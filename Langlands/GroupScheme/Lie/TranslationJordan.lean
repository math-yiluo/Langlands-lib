import Langlands.GroupScheme.Lie.RepresentationDerivationPower
import Langlands.GroupScheme.Lie.ConjugationSemisimple
import Langlands.GroupScheme.Lie.SemisimplePrimePowerReplacement
import Langlands.CommutativeAlgebra.LocallyFiniteDerivationJordan

/-! # Jordan components of actual infinitesimal translation -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Polynomial Module
open scoped CategoryTheory.MonObj Matrix

namespace Langlands.GroupScheme.MatrixRepresentation

open Lie Langlands.LinearAlgebra

variable {k : Type u} [Field k]
    {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
    {n : ℕ} (ρ : MatrixRepresentation G (Fin n)) (X : lieKernel G k)

/-- The finite span of the coefficients of an actual representation. -/
def translationCoefficientSpan : Submodule k (coordinateAlgebra G) :=
  Submodule.span k (Set.range fun p : Fin n × Fin n => coordinateMatrix ρ p.1 p.2)

theorem coordinateMatrix_mem_translationCoefficientSpan (i j : Fin n) :
    coordinateMatrix ρ i j ∈ translationCoefficientSpan ρ :=
  Submodule.subset_span ⟨(i, j), rfl⟩

/-- Left infinitesimal translation preserves every representation coefficient span. -/
theorem translationCoefficientSpan_invariant :
    ∀ c ∈ translationCoefficientSpan ρ,
      translationDerivation G X c ∈ translationCoefficientSpan ρ := by
  intro c hc
  induction hc using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨⟨i, j⟩, rfl⟩ := hy
    have h := congrArg (fun M => M i j)
      (coordinateMatrix_translationDerivation ρ X)
    simp only [Matrix.map_apply, Matrix.mul_apply] at h
    rw [h]
    apply Submodule.sum_mem
    intro a _
    simpa only [Algebra.smul_def] using
      (translationCoefficientSpan ρ).smul_mem (ρ.tangentMatrix k X i a)
        (coordinateMatrix_mem_translationCoefficientSpan ρ a j)
  | zero => simpa only [map_zero] using (translationCoefficientSpan ρ).zero_mem
  | add y z hy hz ihy ihz =>
    simpa only [map_add] using (translationCoefficientSpan ρ).add_mem ihy ihz
  | smul a y hy ih =>
    simpa only [Derivation.map_smul] using (translationCoefficientSpan ρ).smul_mem a ih

/-- The coefficient span as a finite invariant subspace of translation. -/
def translationCoefficientSpace :
    FiniteInvariantSubspace (translationDerivation G X).toLinearMap where
  carrier := translationCoefficientSpan ρ
  finite := Module.Finite.span_of_finite k (Set.finite_range _)
  invariant := translationCoefficientSpan_invariant ρ X

/-- Polynomial translation acts by the same polynomial in the tangent matrix. -/
theorem coordinateMatrix_translationDerivation_aeval (P : k[X]) :
    (coordinateMatrix ρ).map (aeval (translationDerivation G X).toLinearMap P) =
      (aeval (ρ.tangentMatrix k X) P).map (algebraMap k (coordinateAlgebra G)) *
        coordinateMatrix ρ := by
  rw [aeval_eq_sum_range, aeval_eq_sum_range]
  ext i j
  simp only [Matrix.map_apply, LinearMap.sum_apply, LinearMap.smul_apply,
    Matrix.sum_apply, Matrix.smul_apply, map_sum,
    Finset.sum_mul, Matrix.mul_apply]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro m hm
  have h := congrArg (fun M => M i j)
    (coordinateMatrix_translationDerivation_pow ρ X m)
  simp only [Matrix.map_apply, Matrix.mul_apply] at h
  rw [h, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro a _
  simp only [Algebra.smul_def, map_mul, Algebra.algebraMap_self, RingHom.id_apply]
  ring

end Langlands.GroupScheme.MatrixRepresentation

namespace Langlands.GroupScheme.Lie

open Langlands.LinearAlgebra

variable {k : Type u} [Field k] [PerfectField k]

/-- Over a perfect field ordinary matrix semisimplicity is geometric. -/
theorem isGeometricallySemisimpleMatrix_of_isSemisimple
    {n : Type} [Fintype n] [DecidableEq n] (M : Matrix n n k)
    (hM : Module.End.IsSemisimple (Matrix.toLin' M)) :
    IsGeometricallySemisimpleMatrix M := by
  have hq : Squarefree (minpoly k M) := by
    simpa only [Matrix.minpoly_toLin'] using hM.minpoly_squarefree
  exact isGeometricallySemisimpleMatrix_of_separable_aeval_eq_zero M
    (PerfectField.separable_iff_squarefree.mpr hq) (minpoly.aeval k M)

end Langlands.GroupScheme.Lie

namespace Langlands.GroupScheme.Lie

open Langlands.LinearAlgebra

variable {k : Type u} [Field k]
    (G : GroupScheme (Spec (CommRingCat.of k))) [IsAffineHom G.X.hom]

/-- Every actual infinitesimal translation derivation is locally finite. -/
theorem translationDerivation_isLocallyFinite (X : lieKernel G k) :
    IsLocallyFinite (translationDerivation G X).toLinearMap := by
  intro c
  obtain ⟨n, ρ, hc⟩ := exists_representation_coefficient_span G c
  exact ⟨ρ.translationCoefficientSpace X, hc⟩

variable [PerfectField k]

/-- Evaluate the semisimple derivation component of translation at the identity. -/
def semisimpleKernel (X : lieKernel G k) : lieKernel G k :=
  kernelOfDerivation G
    (Langlands.Algebra.LocallyFiniteDerivationJordan.semisimplePart
      (translationDerivation G X) (translationDerivation_isLocallyFinite G X))

end Langlands.GroupScheme.Lie

namespace Langlands.GroupScheme.MatrixRepresentation

open Lie Langlands.LinearAlgebra

variable {k : Type u} [Field k] [PerfectField k]
    {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
    {n : ℕ}

/-- Every actual representation differential preserves the constructed
semisimple component. -/
theorem tangentMatrix_semisimpleKernel (ρ : MatrixRepresentation G (Fin n))
    (X : lieKernel G k) :
    Matrix.toLin' (ρ.tangentMatrix k (semisimpleKernel G X)) =
      jordanSemisimplePart (Matrix.toLin' (ρ.tangentMatrix k X)) := by
  let D := translationDerivation G X
  let hD := translationDerivation_isLocallyFinite G X
  let Q := translationCoefficientSpace ρ X
  let M := ρ.tangentMatrix k X
  obtain ⟨P, hnQ, hsQ, hnM, hsM⟩ :=
    exists_common_jordan_polynomial Q.restrict (Matrix.toLin' M)
  have hQ : jordanSemisimplePart Q.restrict = aeval Q.restrict P :=
    jordanSemisimplePart_eq_of_decomposition _ _ _ hnQ hsQ
      (commute_sub_aeval _ _) (by abel)
  have hM : jordanSemisimplePart (Matrix.toLin' M) = aeval (Matrix.toLin' M) P :=
    jordanSemisimplePart_eq_of_decomposition _ _ _ hnM hsM
      (commute_sub_aeval _ _) (by abel)
  have hcoeff :
      (coordinateMatrix ρ).map
          (Langlands.Algebra.LocallyFiniteDerivationJordan.semisimplePart D hD) =
        (coordinateMatrix ρ).map (aeval D.toLinearMap P) := by
    ext i j
    let c : Q.carrier :=
      ⟨coordinateMatrix ρ i j, coordinateMatrix_mem_translationCoefficientSpan ρ i j⟩
    have hinc : D.toLinearMap.comp Q.carrier.subtype =
        Q.carrier.subtype.comp Q.restrict := rfl
    have he := LinearMap.congr_fun (aeval_intertwines Q.carrier.subtype hinc P) c
    change locallyFiniteSemisimplePart D.toLinearMap hD (c : coordinateAlgebra G) =
      aeval D.toLinearMap P (c : coordinateAlgebra G)
    rw [locallyFiniteSemisimplePart_eq _ _ Q c]
    change (jordanSemisimplePart Q.restrict c).val = _
    rw [hQ]
    exact he.symm
  have heval : ρ.tangentMatrix k (semisimpleKernel G X) = aeval M P := by
    rw [semisimpleKernel, tangentMatrix_kernelOfDerivation]
    change ((coordinateMatrix ρ).map
      (Langlands.Algebra.LocallyFiniteDerivationJordan.semisimplePart D hD)).map
        (coordinateOrigin G) = _
    rw [hcoeff, coordinateMatrix_translationDerivation_aeval,
      Matrix.map_mul, coordinateMatrix_origin, mul_one]
    ext i j
    exact (coordinateOrigin G).commutes _
  rw [heval, hM]
  exact (aeval_algHom_apply Matrix.toLinAlgEquiv'.toAlgHom M P).symm

end Langlands.GroupScheme.MatrixRepresentation

namespace Langlands.GroupScheme.Lie

open Langlands.LinearAlgebra

variable {k : Type u} [Field k] [PerfectField k]
    (G : GroupScheme (Spec (CommRingCat.of k))) [IsAffineHom G.X.hom]

/-- The evaluated semisimple component is semisimple in every actual
finite representation after extension to the algebraic closure. -/
theorem isSemisimpleElement_semisimpleKernel (X : lieKernel G k) :
    IsSemisimpleElement G (semisimpleKernel G X) := by
  intro n ρ
  apply isGeometricallySemisimpleMatrix_of_isSemisimple
  rw [MatrixRepresentation.tangentMatrix_semisimpleKernel]
  exact (jordanSemisimplePart_properties _).2.2.1

end Langlands.GroupScheme.Lie
