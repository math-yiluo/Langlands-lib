import Langlands.GroupScheme.IntegralModel.MatrixVector
import Langlands.FieldTheory.HenselianSeparableDepthBasis
import Mathlib.LinearAlgebra.Matrix.Basis

/-! # Polynomial models of actual separable additive depth lattices -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

noncomputable section

universe u w

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj Matrix
open Langlands.FieldTheory

namespace Langlands.GroupScheme.IntegralModel

variable {K : Type u} [Field K]
  (v : Valuation K (WithZero (Multiplicative ℤ)))
  (hH : HenselianLocalRing v.valuationSubring)
  (L : Type w) [Field L] [Algebra K L] [Algebra.IsSeparable K L]
  (hv : Function.Surjective v) [FiniteDimensional K L]
  (b₀ : Module.Basis (Fin (Module.finrank K L)) K L)

/-- The generic matrix whose columns are the actual depth-lattice basis,
expressed in a fixed reference basis. -/
def separableDepthBasisMatrix (r : ℝ) :
    (Matrix (Fin (Module.finrank K L)) (Fin (Module.finrank K L)) K)ˣ where
  val := b₀.toMatrix (henselianSeparableDepthFieldBasis v hH L hv r)
  inv := (henselianSeparableDepthFieldBasis v hH L hv r).toMatrix b₀
  val_inv := Module.Basis.toMatrix_mul_toMatrix_flip _ _
  inv_val := Module.Basis.toMatrix_mul_toMatrix_flip _ _

/-- A polynomial integral model of the actual depth lattice, in a fixed
generic vector presentation of the extension field's additive space. -/
def separableDepthVector (r : ℝ) :
    IntegralModel v.valuationSubring K
      (VectorGroup.groupScheme (CommRingCat.of K) (Module.finrank K L)) :=
  matrixVector v.valuationSubring K (Module.finrank K L)
    (separableDepthBasisMatrix v hH L hv b₀ r)

theorem separableDepthVector_isSmooth (r : ℝ) :
    (separableDepthVector v hH L hv b₀ r).IsSmooth :=
  matrixVector_isSmooth _ _ _ _

theorem separableDepthVector_hasGeometricallyConnectedFibres (r : ℝ) :
    (separableDepthVector v hH L hv b₀ r).HasGeometricallyConnectedFibres :=
  matrixVector_hasGeometricallyConnectedFibres _ _ _ _

/-- Interpret a rational point of the fixed vector presentation as an
element of the actual extension field, using the fixed reference basis. -/
def separableDepthVectorPoint
    (g : rationalPoints
      (VectorGroup.groupScheme (CommRingCat.of K) (Module.finrank K L))) : L :=
  b₀.equivFun.symm
    (VectorGroup.sectionCoordinates (CommRingCat.of K) (Module.finrank K L) g).toAdd

omit [Algebra.IsSeparable K L] [FiniteDimensional K L] in
theorem separableDepthVectorPoint_repr
    (g : rationalPoints
      (VectorGroup.groupScheme (CommRingCat.of K) (Module.finrank K L))) :
    (b₀.repr (separableDepthVectorPoint L b₀ g) :
        Fin (Module.finrank K L) → K) =
      (VectorGroup.sectionCoordinates (CommRingCat.of K) (Module.finrank K L) g).toAdd :=
  b₀.equivFun.apply_symm_apply _

/-- The image of integral sections is exactly the actual valuation-depth
ball, including in ramified separable extensions. -/
theorem separableDepthVector_mem_integralPoints (r : ℝ)
    (g : rationalPoints
      (VectorGroup.groupScheme (CommRingCat.of K) (Module.finrank K L))) :
    g ∈ (separableDepthVector v hH L hv b₀ r).integralPoints ↔
      separableDepthVectorPoint L b₀ g ∈ henselianSeparableDepthLattice v hH L r := by
  let b := henselianSeparableDepthFieldBasis v hH L hv r
  let x := separableDepthVectorPoint L b₀ g
  have hx : (b₀.repr x : Fin (Module.finrank K L) → K) =
      (VectorGroup.sectionCoordinates (CommRingCat.of K) (Module.finrank K L) g).toAdd :=
    separableDepthVectorPoint_repr L b₀ g
  change g ∈ (matrixVector _ _ _ (separableDepthBasisMatrix v hH L hv b₀ r)).integralPoints ↔
    x ∈ henselianSeparableDepthLattice v hH L r
  rw [matrixVector_mem_integralPoints, henselianSeparableDepthFieldBasis_mem_iff v hH L hv r]
  change (∃ a : Fin (Module.finrank K L) → v.valuationSubring,
      (VectorGroup.sectionCoordinates (CommRingCat.of K) (Module.finrank K L) g).toAdd =
        b₀.toMatrix b *ᵥ (algebraMap v.valuationSubring K ∘ a)) ↔
    ∀ i, b.repr x i ∈ v.valuationSubring
  constructor
  · rintro ⟨a, ha⟩ i
    have hh := congrArg
      (fun z : Fin (Module.finrank K L) → K => b.toMatrix b₀ *ᵥ z) ha
    rw [← hx, Module.Basis.toMatrix_mulVec_repr, Matrix.mulVec_mulVec,
      Module.Basis.toMatrix_mul_toMatrix_flip, Matrix.one_mulVec] at hh
    rw [congrFun hh i]
    exact (a i).property
  · intro h
    refine ⟨fun i => ⟨b.repr x i, h i⟩, ?_⟩
    rw [← hx]
    exact (Module.Basis.toMatrix_mulVec_repr b b₀ x).symm

/-- The coefficient matrix of the actual inclusion of the deeper depth
lattice into the shallower lattice, in their integral bases. -/
def separableDepthTransitionMatrix (r s : ℝ) (hrs : r ≤ s) :
    Matrix (Fin (Module.finrank K L)) (Fin (Module.finrank K L))
      v.valuationSubring :=
  fun i j => (henselianSeparableDepthIntegralBasis v hH L hv r).repr
    ⟨(henselianSeparableDepthIntegralBasis v hH L hv s j : L),
      henselianSeparableDepthLattice_antitone v hH L hrs
        (henselianSeparableDepthIntegralBasis v hH L hv s j).property⟩ i

theorem separableDepthTransitionMatrix_map (r s : ℝ) (hrs : r ≤ s) :
    (separableDepthTransitionMatrix v hH L hv r s hrs).map
        (algebraMap v.valuationSubring K) =
      (henselianSeparableDepthFieldBasis v hH L hv r).toMatrix
        (henselianSeparableDepthFieldBasis v hH L hv s) := by
  ext i j
  change ((henselianSeparableDepthIntegralBasis v hH L hv r).repr
    ⟨(henselianSeparableDepthIntegralBasis v hH L hv s j : L), _⟩ i : K) = _
  rw [Module.Basis.toMatrix_apply, henselianSeparableDepthFieldBasis_apply]
  exact (henselianSeparableDepthFieldBasis_repr_coe v hH L hv r
    ⟨(henselianSeparableDepthIntegralBasis v hH L hv s j : L), _⟩ i).symm

theorem separableDepthTransitionMatrix_equation (r s : ℝ) (hrs : r ≤ s) :
    (separableDepthBasisMatrix v hH L hv b₀ r :
        Matrix (Fin (Module.finrank K L)) (Fin (Module.finrank K L)) K) *
      (separableDepthTransitionMatrix v hH L hv r s hrs).map
        (algebraMap v.valuationSubring K) =
      (separableDepthBasisMatrix v hH L hv b₀ s :
        Matrix (Fin (Module.finrank K L)) (Fin (Module.finrank K L)) K) := by
  rw [separableDepthTransitionMatrix_map]
  exact Module.Basis.toMatrix_mul_toMatrix _ _ _

/-- The actual depth-lattice inclusion gives a model map extending the
identity in the fixed generic presentation. -/
def separableDepthVectorTransition (r s : ℝ) (hrs : r ≤ s) :
    (separableDepthVector v hH L hv b₀ s).Hom
      (separableDepthVector v hH L hv b₀ r) (𝟙 _) :=
  matrixVectorTransition
    (separableDepthBasisMatrix v hH L hv b₀ s)
    (separableDepthBasisMatrix v hH L hv b₀ r)
    (separableDepthTransitionMatrix v hH L hv r s hrs)
    (separableDepthTransitionMatrix_equation v hH L hv b₀ r s hrs)

/-- Every model map extending the generic identity between the actual
depth-lattice models has smooth connected unipotent special-fibre kernel. -/
theorem separableDepthVector_kernel_properties (r s : ℝ) (hrs : r ≤ s)
    (φ : (separableDepthVector v hH L hv b₀ s).Hom
      (separableDepthVector v hH L hv b₀ r) (𝟙 _)) :
    Smooth (kernel φ.specialFibreMap).X.hom ∧
      ConnectedSpace (kernel φ.specialFibreMap).X.left ∧
        IsUnipotent (kernel φ.specialFibreMap) :=
  matrixVector_kernel_properties _ _
    (separableDepthTransitionMatrix v hH L hv r s hrs)
    (separableDepthTransitionMatrix_equation v hH L hv b₀ r s hrs) φ

end Langlands.GroupScheme.IntegralModel
