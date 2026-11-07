import Langlands.Representation.Families.CompactCompressionMatrices
import Langlands.Representation.Compact.CoefficientSpecialization
import Mathlib.LinearAlgebra.TensorProduct.Basis

/-! # Specializing compact-compression matrices -/

noncomputable section

set_option autoImplicit false

open scoped TensorProduct

namespace Langlands.Renard.AlgebraicFamily.CompactCompressionMatrices

universe uR uG uV uW un

variable (R : Type uR) [CommRing R]
variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable (A : SmoothRep.{0, uG, uV} ℂ G)
variable [Module R A] [SMulCommClass ℂ R A]
variable [HasCompatibleCoefficients R A.representation]
variable (K : OpenSubgroup G) (hK : IsCompact (K : Set G))
variable {n : Type un} [Fintype n]
variable (b : Module.Basis n R (fixedVectors A.representation K.toSubgroup))

/-- Matrices over the coefficient ring, formed from the actual compact average. -/
def coefficientMatrix (g : G) : Matrix n n R :=
  Matrix.of fun i j =>
    b.repr (Compact.CoefficientSpecialization.compression R A.representation
      A.isSmooth K hK g (b j)) i

variable [Algebra R ℂ]
variable (B : SmoothRep.{0, uG, uW} ℂ G)
variable (f : A.representation.IntertwiningMap B.representation)
variable (hf : ∀ (r : R) (v : A), f (r • v) = algebraMap R ℂ r • f v)
variable (hbij : Function.Bijective
  (Compact.CoefficientSpecialization.scalarExtension R A.representation B.representation f hf))

/-- Transport the scalar-extended coefficient basis along the canonical
equivalence with the actual fiber's compact fixed vectors. -/
def specializedBasis :
    Module.Basis n ℂ (fixedVectors B.representation K.toSubgroup) :=
  (b.baseChange ℂ).map
    (Compact.CoefficientSpecialization.fixedScalarExtensionEquiv
      R A.representation B.representation f hf A.isSmooth B.isSmooth K hK hbij)

omit [Fintype n] in
@[simp]
theorem specializedBasis_apply (j : n) :
    specializedBasis R A K hK b B f hf hbij j =
      fixedVectorsMap f K.toSubgroup (b j) := by
  simp [specializedBasis,
    Compact.CoefficientSpecialization.fixedScalarExtensionEquiv]

omit [Fintype n] in
/-- Coordinates of evaluation are exactly scalar evaluation of the original
 coefficient coordinates. -/
theorem specializedBasis_repr (v : fixedVectors A.representation K.toSubgroup) (i : n) :
    (specializedBasis R A K hK b B f hf hbij).repr
        (fixedVectorsMap f K.toSubgroup v) i =
      algebraMap R ℂ (b.repr v i) := by
  let E := Compact.CoefficientSpecialization.fixedScalarExtensionEquiv
    R A.representation B.representation f hf A.isSmooth B.isSmooth K hK hbij
  have hE : E (1 ⊗ₜ[R] v) = fixedVectorsMap f K.toSubgroup v := by
    simp [E, Compact.CoefficientSpecialization.fixedScalarExtensionEquiv]
  rw [← hE]
  change ((b.baseChange ℂ).map E).repr (E (1 ⊗ₜ[R] v)) i = _
  simp [Module.Basis.map_repr, Algebra.smul_def]

/-- Entrywise evaluation of the coefficient matrix equals the actual
compact-compression matrix in the specialized basis. -/
theorem fixedMatrix_specializedBasis (g : G) :
    fixedMatrix B K hK (specializedBasis R A K hK b B f hf hbij) g =
      (coefficientMatrix R A K hK b g).map (algebraMap R ℂ) := by
  ext i j
  change (specializedBasis R A K hK b B f hf hbij).equivFun
      (Jacquet.compressedAction B.representation B.isSmooth K hK g
        (specializedBasis R A K hK b B f hf hbij j)) i =
    algebraMap R ℂ (b.repr
      (Compact.CoefficientSpecialization.compression R A.representation
        A.isSmooth K hK g (b j)) i)
  rw [specializedBasis_apply, Module.Basis.equivFun_apply]
  have h := LinearMap.congr_fun
    (Jacquet.compressedAction_natural A.representation B.representation
      A.isSmooth B.isSmooth K hK g f) (b j)
  simp only [LinearMap.comp_apply] at h
  rw [← h]
  exact specializedBasis_repr R A K hK b B f hf hbij
    (Jacquet.compressedAction A.representation A.isSmooth K hK g (b j)) i

end Langlands.Renard.AlgebraicFamily.CompactCompressionMatrices
