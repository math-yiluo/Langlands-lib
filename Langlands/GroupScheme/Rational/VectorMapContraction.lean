import Langlands.GroupScheme.Rational.TorusVectorCocycle
import Langlands.GroupScheme.Lie.AffineCoordinates

/-! # Coefficient contraction of vector-valued regular maps -/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry
open scoped CategoryTheory.MonObj TensorProduct

namespace Langlands.GroupScheme.VectorCocycleDescent

variable (k K : Type u) [Field k] [Field K] [Algebra k K]

attribute [local instance] Algebra.TensorProduct.rightAlgebra

variable {A B : Type u} [CommRing A] [Algebra k A]
  [CommRing B] [Algebra k B]

/-- Extend a coefficient map while fixing the extension-field factor. -/
def tensorMap (f : A →ₐ[k] B) : A ⊗[k] K →ₐ[K] B ⊗[k] K where
  __ := (Algebra.TensorProduct.map f (AlgHom.id k K)).toRingHom
  commutes' z := by
    change (Algebra.TensorProduct.map f (AlgHom.id k K)) (1 ⊗ₜ[k] z) = 1 ⊗ₜ[k] z
    simp

@[simp]
theorem tensorMap_tmul (f : A →ₐ[k] B) (x : A) (z : K) :
    tensorMap k K f (x ⊗ₜ[k] z) = f x ⊗ₜ[k] z :=
  rfl

@[simp]
theorem tensorMap_comp_includeLeft (f : A →ₐ[k] B) :
    ((tensorMap k K f).restrictScalars k).comp Algebra.TensorProduct.includeLeft =
      Algebra.TensorProduct.includeLeft.comp f := by
  ext x
  simp [Algebra.TensorProduct.includeLeft_apply]

/-- Contraction commutes with arbitrary maps of the original test algebras. -/
theorem contract_naturality (f : A →ₐ[k] B) (x : A ⊗[k] K) :
    contract k K B (tensorMap k K f x) = f (contract k K A x) := by
  induction x using TensorProduct.inductionOn with
  | tmul x z =>
    simp only [tensorMap_tmul, contract_tmul, map_mul, f.commutes]
  | add x y hx hy => simp only [map_add, hx, hy]

end Langlands.GroupScheme.VectorCocycleDescent

namespace Langlands.GroupScheme.RelativeRoot

variable {k : Type u} [Field k]
  {H V : GroupScheme (Spec (CommRingCat.of k))} {d : ℕ}
  (e : ∀ T : Over (Spec (CommRingCat.of k)),
    (T ⟶ V.X) ≃* Multiplicative (Fin d → Γ(T.left, ⊤)))
  (K : Type u) [Field K] [Algebra k K]

variable (b : (((GroupScheme.baseChange (algebraBaseMap k K)).obj H)).X ⟶ (((GroupScheme.baseChange (algebraBaseMap k K)).obj V)).X)

/-- Coordinates of a regular vector-valued map over the extension field,
viewed on the original group's points over an extension algebra. -/
def extendedMapCoordinates {A : Type u} [CommRing A]
    [Algebra k A] [Algebra K A] [IsScalarTower k K A]
    (t : Lie.AffinePoints H A) : Fin d → A :=
  (vectorAffineCoordinates (vectorBaseChangeCoordinates e K) A
    ((Lie.affineBaseChangeEquiv k K H A).symm t ≫ b)).toAdd

include e in
theorem extendedMapCoordinates_naturality (he : IsNaturalVectorCoordinates e)
    {A B : Type u} [CommRing A] [Algebra k A] [Algebra K A] [IsScalarTower k K A]
    [CommRing B] [Algebra k B] [Algebra K B] [IsScalarTower k K B]
    (f : A →ₐ[K] B) (t : Lie.AffinePoints H A) :
    extendedMapCoordinates e K b (Lie.affineMap H (f.restrictScalars k) t) =
      fun j => f (extendedMapCoordinates e K b t j) := by
  have ht :
      (Lie.affineBaseChangeEquiv k K H B).symm
        (Lie.affineMap H (f.restrictScalars k) t) =
        Lie.affineMap ((GroupScheme.baseChange (algebraBaseMap k K)).obj H) f ((Lie.affineBaseChangeEquiv k K H A).symm t) := by
    apply (Lie.affineBaseChangeEquiv k K H B).injective
    rw [MulEquiv.apply_symm_apply, Lie.affineBaseChangeEquiv_naturality,
      MulEquiv.apply_symm_apply]
  dsimp only [extendedMapCoordinates]
  rw [ht]
  simpa only [Lie.affineMap_apply, Category.assoc] using
    (he.baseChange.vectorAffineCoordinates_naturality f
      ((Lie.affineBaseChangeEquiv k K H A).symm t ≫ b))

attribute [local instance] Algebra.TensorProduct.rightAlgebra

/-- Contract the extension coefficients of the regular map on an affine test. -/
def contractedMapCoordinates {A : Type u} [CommRing A] [Algebra k A]
    (t : Lie.AffinePoints H A) : Fin d → A :=
  fun j => VectorCocycleDescent.contract k K A
    (extendedMapCoordinates e K b
      (Lie.affineMap H (Algebra.TensorProduct.includeLeft : A →ₐ[k] A ⊗[k] K) t) j)

theorem contractedMapCoordinates_naturality (he : IsNaturalVectorCoordinates e)
    {A B : Type u} [CommRing A] [Algebra k A] [CommRing B] [Algebra k B]
    (f : A →ₐ[k] B) (t : Lie.AffinePoints H A) :
    contractedMapCoordinates e K b (Lie.affineMap H f t) =
      fun j => f (contractedMapCoordinates e K b t j) := by
  have ht :
      Lie.affineMap H (Algebra.TensorProduct.includeLeft : B →ₐ[k] B ⊗[k] K)
        (Lie.affineMap H f t) =
      Lie.affineMap H ((VectorCocycleDescent.tensorMap k K f).restrictScalars k)
        (Lie.affineMap H (Algebra.TensorProduct.includeLeft : A →ₐ[k] A ⊗[k] K) t) := by
    rw [← Lie.affineMap_comp, ← Lie.affineMap_comp,
      VectorCocycleDescent.tensorMap_comp_includeLeft]
  funext j
  change VectorCocycleDescent.contract k K B
    (extendedMapCoordinates e K b
      (Lie.affineMap H (Algebra.TensorProduct.includeLeft : B →ₐ[k] B ⊗[k] K)
        (Lie.affineMap H f t)) j) = _
  rw [ht, extendedMapCoordinates_naturality e K b he]
  exact VectorCocycleDescent.contract_naturality k K f _

/-- The actual vector point represented by the contracted coordinates. -/
def contractedMapPoint {A : Type u} [CommRing A] [Algebra k A]
    (t : Lie.AffinePoints H A) : Lie.AffinePoints V A :=
  (vectorAffineCoordinates e A).symm
    (Multiplicative.ofAdd (contractedMapCoordinates e K b t))

theorem contractedMapPoint_naturality (he : IsNaturalVectorCoordinates e)
    {A B : Type u} [CommRing A] [Algebra k A] [CommRing B] [Algebra k B]
    (f : A →ₐ[k] B) (t : Lie.AffinePoints H A) :
    contractedMapPoint e K b (Lie.affineMap H f t) =
      Lie.affineMap V f (contractedMapPoint e K b t) := by
  apply (vectorAffineCoordinates e B).injective
  apply Multiplicative.toAdd.injective
  rw [he.vectorAffineCoordinates_naturality]
  simp only [contractedMapPoint, MulEquiv.apply_symm_apply, toAdd_ofAdd]
  exact contractedMapCoordinates_naturality e K b he f t

variable [IsAffineHom H.X.hom]

/-- The actual regular map obtained by contracting the extension coefficients. -/
def contractedMap : H.X ⟶ V.X :=
  (Lie.coordinateIso H).inv ≫
    contractedMapPoint e K b (Lie.coordinateIso H).hom

theorem comp_contractedMap (he : IsNaturalVectorCoordinates e)
    {A : Type u} [CommRing A] [Algebra k A] (t : Lie.AffinePoints H A) :
    t ≫ contractedMap e K b = contractedMapPoint e K b t := by
  let f := Lie.pointCoordinates H t
  have ht : Lie.affineMap H f (Lie.coordinateIso H).hom = t := by
    change (Lie.pointCoordinates H).symm f = t
    exact (Lie.pointCoordinates H).symm_apply_apply t
  rw [← ht, contractedMapPoint_naturality e K b he]
  simp only [contractedMap, Lie.affineMap_apply, Category.assoc]
  erw [Iso.hom_inv_id_assoc]
  rfl

end Langlands.GroupScheme.RelativeRoot
