import Langlands.GroupScheme.FiniteAlgebraMatrixPoints
import Langlands.GroupScheme.VectorGroupQuotient
import Langlands.Algebra.BinaryElementary
import Mathlib.LinearAlgebra.TensorProduct.Basis

/-! # Actual binary elementary maps over finite algebras -/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry
open scoped CategoryTheory.MonObj TensorProduct

namespace Langlands.GroupScheme.FiniteAlgebraUnits.BinaryRoot

section Matrices

variable {R S : Type u} [Ring R] [Ring S]

/-- Upper elementary units form a homomorphism from the additive coefficient group. -/
def upperHom : Multiplicative R →* Langlands.BinaryElementary.GL₂ R where
  toFun x := Langlands.BinaryElementary.upper x.toAdd
  map_one' := by
    apply Units.ext
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Langlands.BinaryElementary.upper]
  map_mul' x y := Langlands.BinaryElementary.upper_add x.toAdd y.toAdd

/-- Lower elementary units form a homomorphism from the additive coefficient group. -/
def lowerHom : Multiplicative R →* Langlands.BinaryElementary.GL₂ R where
  toFun x := Langlands.BinaryElementary.lower x.toAdd
  map_one' := by
    apply Units.ext
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Langlands.BinaryElementary.lower]
  map_mul' x y := Langlands.BinaryElementary.lower_add x.toAdd y.toAdd

/-- An arbitrary coefficient-ring map preserves the upper elementary unit. -/
theorem map_upper (f : R →+* S) (x : R) :
    Units.map (RingHom.mapMatrix f).toMonoidHom (Langlands.BinaryElementary.upper x) =
      Langlands.BinaryElementary.upper (f x) := by
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Langlands.BinaryElementary.upper, RingHom.mapMatrix_apply]

/-- An arbitrary coefficient-ring map preserves the lower elementary unit. -/
theorem map_lower (f : R →+* S) (x : R) :
    Units.map (RingHom.mapMatrix f).toMonoidHom (Langlands.BinaryElementary.lower x) =
      Langlands.BinaryElementary.lower (f x) := by
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Langlands.BinaryElementary.lower, RingHom.mapMatrix_apply]

end Matrices

variable (k D : Type u) [Field k] [Ring D] [Algebra k D]
  {d n : ℕ} (bD : Module.Basis (Fin d) k D)
  (bA : Module.Basis (Fin n) k (Matrix (Fin 2) (Fin 2) D))

/-- The actual additive group whose coordinates are a fixed basis of the finite algebra. -/
abbrev additiveScheme : GroupScheme (base k) :=
  VectorGroup.groupScheme (CommRingCat.of k) d

/-- Basis coordinates determine an actual tensor-valued additive parameter. -/
def parameterHom (R : CommAlgCat.{u} (CommRingCat.of k)) :
    Multiplicative (Fin d → R) →* Multiplicative (R ⊗[k] D) :=
  AddMonoidHom.toMultiplicative
    { toFun := fun x => ∑ i, x i ⊗ₜ[k] bD i
      map_zero' := by simp
      map_add' := fun x y => by
        simp [TensorProduct.add_tmul, Finset.sum_add_distrib] }

/-- Every tensor coefficient is represented by basis coordinates, including over nonreduced tests. -/
theorem parameterHom_surjective (R : CommAlgCat.{u} (CommRingCat.of k)) :
    Function.Surjective (parameterHom k D bD R) := by
  intro x
  refine ⟨Multiplicative.ofAdd fun i => (bD.baseChange R).repr x.toAdd i, ?_⟩
  apply Multiplicative.toAdd.injective
  change (∑ i, (bD.baseChange R).repr x.toAdd i ⊗ₜ[k] bD i) = x.toAdd
  simpa only [Module.Basis.baseChange_apply, TensorProduct.smul_tmul',
    smul_eq_mul, mul_one] using (bD.baseChange R).sum_repr x.toAdd

/-- The tensor parameter of an actual relative additive point. -/
def tensorCoordinates (T : Over (base k)) :
    (T ⟶ (additiveScheme k (d := d)).X) →*
      Multiplicative (((algΓ (CommRingCat.of k)).obj T).unop ⊗[k] D) :=
  (parameterHom k D bD ((algΓ (CommRingCat.of k)).obj T).unop).comp
    (VectorGroup.coordinates (CommRingCat.of k) d T).toMonoidHom

/-- The actual additive test points cover every tensor parameter. -/
theorem tensorCoordinates_surjective (T : Over (base k)) :
    Function.Surjective (tensorCoordinates k D bD T) :=
  (parameterHom_surjective k D bD ((algΓ (CommRingCat.of k)).obj T).unop).comp
    (VectorGroup.coordinates (CommRingCat.of k) d T).surjective

/-- Every change of actual test pulls the parameter back by the tensor coefficient map. -/
theorem tensorCoordinates_naturality {T T' : Over (base k)} (a : T' ⟶ T)
    (x : T ⟶ (additiveScheme k (d := d)).X) :
    (tensorCoordinates k D bD T' (a ≫ x)).toAdd =
      Algebra.TensorProduct.map ((algΓ (CommRingCat.of k)).map a).unop.hom
        (AlgHom.id k D) (tensorCoordinates k D bD T x).toAdd := by
  change (∑ i, TensorProduct.tmul k
      (M := ((algΓ (CommRingCat.of k)).obj T').unop) (N := D)
      ((VectorGroup.coordinates (CommRingCat.of k) d T' (a ≫ x)).toAdd i) (bD i)) =
    Algebra.TensorProduct.map ((algΓ (CommRingCat.of k)).map a).unop.hom
      (AlgHom.id k D)
      (∑ i, TensorProduct.tmul k
        (M := ((algΓ (CommRingCat.of k)).obj T).unop) (N := D)
        ((VectorGroup.coordinates (CommRingCat.of k) d T x).toAdd i) (bD i))
  rw [VectorGroup.coordinates_comp, map_sum]
  rfl

/-- The upper elementary map on all actual test points. -/
def upperPoints (T : Over (base k)) :
    (T ⟶ (additiveScheme k (d := d)).X) →* (T ⟶ (groupScheme bA).X) :=
  (MatrixPoints.tensorMatrixEquiv k D bA T).symm.toMonoidHom.comp
    (upperHom.comp (tensorCoordinates k D bD T))

/-- The lower elementary map on all actual test points. -/
def lowerPoints (T : Over (base k)) :
    (T ⟶ (additiveScheme k (d := d)).X) →* (T ⟶ (groupScheme bA).X) :=
  (MatrixPoints.tensorMatrixEquiv k D bA T).symm.toMonoidHom.comp
    (lowerHom.comp (tensorCoordinates k D bD T))

/-- The actual upper elementary formula is natural on all relative tests. -/
theorem upperPoints_naturality {T T' : Over (base k)} (a : T' ⟶ T)
    (x : T ⟶ (additiveScheme k (d := d)).X) :
    upperPoints k D bD bA T' (a ≫ x) = a ≫ upperPoints k D bD bA T x := by
  apply (MatrixPoints.tensorMatrixEquiv k D bA T').injective
  rw [MatrixPoints.tensorMatrixEquiv_naturality]
  simp only [upperPoints, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
    MulEquiv.apply_symm_apply, upperHom, MonoidHom.coe_mk, OneHom.coe_mk, map_upper]
  rw [tensorCoordinates_naturality]
  rfl

/-- The actual lower elementary formula is natural on all relative tests. -/
theorem lowerPoints_naturality {T T' : Over (base k)} (a : T' ⟶ T)
    (x : T ⟶ (additiveScheme k (d := d)).X) :
    lowerPoints k D bD bA T' (a ≫ x) = a ≫ lowerPoints k D bD bA T x := by
  apply (MatrixPoints.tensorMatrixEquiv k D bA T').injective
  rw [MatrixPoints.tensorMatrixEquiv_naturality]
  simp only [lowerPoints, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
    MulEquiv.apply_symm_apply, lowerHom, MonoidHom.coe_mk, OneHom.coe_mk, map_lower]
  rw [tensorCoordinates_naturality]
  rfl

/-- The actual upper elementary group-scheme homomorphism. -/
def upperMap : additiveScheme k (d := d) ⟶ groupScheme bA :=
  homOfPoints (upperPoints k D bD bA) (upperPoints_naturality k D bD bA)

/-- The actual lower elementary group-scheme homomorphism. -/
def lowerMap : additiveScheme k (d := d) ⟶ groupScheme bA :=
  homOfPoints (lowerPoints k D bD bA) (lowerPoints_naturality k D bD bA)

/-- On every test, the actual upper morphism is exactly its tensor elementary matrix. -/
theorem tensorMatrixEquiv_upperMap (T : Over (base k))
    (x : T ⟶ (additiveScheme k (d := d)).X) :
    MatrixPoints.tensorMatrixEquiv k D bA T (x ≫ (upperMap k D bD bA).hom.hom) =
      Langlands.BinaryElementary.upper (tensorCoordinates k D bD T x).toAdd := by
  rw [upperMap, comp_homOfPoints]
  exact (MatrixPoints.tensorMatrixEquiv k D bA T).apply_symm_apply _

/-- On every test, the actual lower morphism is exactly its tensor elementary matrix. -/
theorem tensorMatrixEquiv_lowerMap (T : Over (base k))
    (x : T ⟶ (additiveScheme k (d := d)).X) :
    MatrixPoints.tensorMatrixEquiv k D bA T (x ≫ (lowerMap k D bD bA).hom.hom) =
      Langlands.BinaryElementary.lower (tensorCoordinates k D bD T x).toAdd := by
  rw [lowerMap, comp_homOfPoints]
  exact (MatrixPoints.tensorMatrixEquiv k D bA T).apply_symm_apply _

/-- Every upper elementary tensor unit comes from an actual point of the upper root map. -/
theorem exists_upperPoint (T : Over (base k))
    (a : ((algΓ (CommRingCat.of k)).obj T).unop ⊗[k] D) :
    ∃ x : T ⟶ (additiveScheme k (d := d)).X,
      MatrixPoints.tensorMatrixEquiv k D bA T (x ≫ (upperMap k D bD bA).hom.hom) =
        Langlands.BinaryElementary.upper a := by
  obtain ⟨x, hx⟩ := tensorCoordinates_surjective k D bD T (Multiplicative.ofAdd a)
  refine ⟨x, ?_⟩
  rw [tensorMatrixEquiv_upperMap, hx]
  rfl

/-- Every lower elementary tensor unit comes from an actual point of the lower root map. -/
theorem exists_lowerPoint (T : Over (base k))
    (a : ((algΓ (CommRingCat.of k)).obj T).unop ⊗[k] D) :
    ∃ x : T ⟶ (additiveScheme k (d := d)).X,
      MatrixPoints.tensorMatrixEquiv k D bA T (x ≫ (lowerMap k D bD bA).hom.hom) =
        Langlands.BinaryElementary.lower a := by
  obtain ⟨x, hx⟩ := tensorCoordinates_surjective k D bD T (Multiplicative.ofAdd a)
  refine ⟨x, ?_⟩
  rw [tensorMatrixEquiv_lowerMap, hx]
  rfl

end Langlands.GroupScheme.FiniteAlgebraUnits.BinaryRoot
