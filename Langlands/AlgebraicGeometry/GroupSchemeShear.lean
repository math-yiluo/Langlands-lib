import Langlands.AlgebraicGeometry.Deformation.ElementaryReductionProducts
import Langlands.AbelianScheme.KernelBaseChange

/-! # The shear automorphism of the square of a group scheme, and maps compatible with it -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open MonoidalCategory CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.AlgebraicGeometry.GroupSchemeShear

open Langlands.AlgebraicGeometry.Deformation.AffineOpenQuotientSections.Reduction
  (productMap product_isPullback)

section ProductMap

variable {S T T' : Scheme.{u}} {Y Z : Over S} {Y' Z' : Over T} {Y'' Z'' : Over T'}

@[reassoc]
theorem productMap_fst (y : Y'.left ⟶ Y.left) (z : Z'.left ⟶ Z.left) (t : T ⟶ S)
    (hy : y ≫ Y.hom = Y'.hom ≫ t) (hz : z ≫ Z.hom = Z'.hom ≫ t) :
    productMap y z t hy hz ≫ (fst Y Z).left = (fst Y' Z').left ≫ y :=
  (product_isPullback Y Z).lift_fst _ _ _

@[reassoc]
theorem productMap_snd (y : Y'.left ⟶ Y.left) (z : Z'.left ⟶ Z.left) (t : T ⟶ S)
    (hy : y ≫ Y.hom = Y'.hom ≫ t) (hz : z ≫ Z.hom = Z'.hom ≫ t) :
    productMap y z t hy hz ≫ (snd Y Z).left = (snd Y' Z').left ≫ z :=
  (product_isPullback Y Z).lift_snd _ _ _

@[reassoc (attr := simp)]
theorem productMap_pullback_fst (y : Y'.left ⟶ Y.left) (z : Z'.left ⟶ Z.left) (t : T ⟶ S)
    (hy : y ≫ Y.hom = Y'.hom ≫ t) (hz : z ≫ Z.hom = Z'.hom ≫ t) :
    productMap y z t hy hz ≫ pullback.fst Y.hom Z.hom = pullback.fst Y'.hom Z'.hom ≫ y :=
  (product_isPullback Y Z).lift_fst _ _ _

@[reassoc (attr := simp)]
theorem productMap_pullback_snd (y : Y'.left ⟶ Y.left) (z : Z'.left ⟶ Z.left) (t : T ⟶ S)
    (hy : y ≫ Y.hom = Y'.hom ≫ t) (hz : z ≫ Z.hom = Z'.hom ≫ t) :
    productMap y z t hy hz ≫ pullback.snd Y.hom Z.hom = pullback.snd Y'.hom Z'.hom ≫ z :=
  (product_isPullback Y Z).lift_snd _ _ _

theorem productMap_hom (y : Y'.left ⟶ Y.left) (z : Z'.left ⟶ Z.left) (t : T ⟶ S)
    (hy : y ≫ Y.hom = Y'.hom ≫ t) (hz : z ≫ Z.hom = Z'.hom ≫ t) :
    productMap y z t hy hz ≫ (Y ⊗ Z).hom = (Y' ⊗ Z').hom ≫ t := by
  change _ ≫ pullback.fst Y.hom Z.hom ≫ Y.hom = (pullback.fst Y'.hom Z'.hom ≫ Y'.hom) ≫ t
  rw [productMap_pullback_fst_assoc, hy, Category.assoc]

theorem productMap_ext {W : Scheme.{u}} {a b : W ⟶ (Y ⊗ Z).left}
    (h₁ : a ≫ (fst Y Z).left = b ≫ (fst Y Z).left)
    (h₂ : a ≫ (snd Y Z).left = b ≫ (snd Y Z).left) : a = b :=
  (product_isPullback Y Z).hom_ext h₁ h₂

theorem productMap_comp (y : Y''.left ⟶ Y'.left) (z : Z''.left ⟶ Z'.left) (t : T' ⟶ T)
    (hy : y ≫ Y'.hom = Y''.hom ≫ t) (hz : z ≫ Z'.hom = Z''.hom ≫ t)
    (y' : Y'.left ⟶ Y.left) (z' : Z'.left ⟶ Z.left) (t' : T ⟶ S)
    (hy' : y' ≫ Y.hom = Y'.hom ≫ t') (hz' : z' ≫ Z.hom = Z'.hom ≫ t') :
    productMap y z t hy hz ≫ productMap y' z' t' hy' hz' =
      productMap (y ≫ y') (z ≫ z') (t ≫ t')
        (by rw [Category.assoc, hy', reassoc_of% hy])
        (by rw [Category.assoc, hz', reassoc_of% hz]) := by
  apply productMap_ext <;> simp

theorem productMap_id :
    productMap (𝟙 Y.left) (𝟙 Z.left) (𝟙 S) (by simp) (by simp) = 𝟙 (Y ⊗ Z).left := by
  apply productMap_ext <;> simp

end ProductMap

section Instances

variable {S : Scheme.{u}} (X Y : Over S)

instance isSeparated_tensor_hom [IsSeparated X.hom] [IsSeparated Y.hom] :
    IsSeparated (X ⊗ Y).hom := by
  change IsSeparated (pullback.fst X.hom Y.hom ≫ X.hom)
  infer_instance

instance smooth_tensor_hom [Smooth X.hom] [Smooth Y.hom] : Smooth (X ⊗ Y).hom := by
  change Smooth (pullback.fst X.hom Y.hom ≫ X.hom)
  infer_instance

end Instances

section Shear

variable {C : Type*} [Category C] [CartesianMonoidalCategory C] (G : C) [GrpObj G]

/-- The shear automorphism `(x, y) ↦ (x * y, y)` of the square of a group object. -/
def shear : G ⊗ G ≅ G ⊗ G where
  hom := lift (fst G G * snd G G) (snd G G)
  inv := lift (fst G G / snd G G) (snd G G)
  hom_inv_id := by
    apply CartesianMonoidalCategory.hom_ext
    · rw [Category.assoc, lift_fst, GrpObj.comp_div, lift_fst, lift_snd, mul_div_cancel_right,
        Category.id_comp]
    · rw [Category.assoc, lift_snd, lift_snd, Category.id_comp]
  inv_hom_id := by
    apply CartesianMonoidalCategory.hom_ext
    · rw [Category.assoc, lift_fst, MonObj.comp_mul, lift_fst, lift_snd, div_mul_cancel,
        Category.id_comp]
    · rw [Category.assoc, lift_snd, lift_snd, Category.id_comp]

@[reassoc (attr := simp)]
theorem shear_hom_fst : (shear G).hom ≫ fst G G = fst G G * snd G G := lift_fst _ _

@[reassoc (attr := simp)]
theorem shear_hom_snd : (shear G).hom ≫ snd G G = snd G G := lift_snd _ _

@[reassoc (attr := simp)]
theorem shear_inv_fst : (shear G).inv ≫ fst G G = fst G G / snd G G := lift_fst _ _

@[reassoc (attr := simp)]
theorem shear_inv_snd : (shear G).inv ≫ snd G G = snd G G := lift_snd _ _

theorem fst_mul_snd : fst G G * snd G G = μ[G] := by
  rw [Hom.mul_def, lift_fst_snd, Category.id_comp]

end Shear

section Multiplicative

variable {S T T' : Scheme.{u}}

/-- A morphism of the underlying schemes of two monoid objects over a map of bases,
compatible with the multiplications. -/
def IsMulMap {G : Over T} {H : Over S} [MonObj G] [MonObj H] (b : T ⟶ S)
    (f : G.left ⟶ H.left) (hf : f ≫ H.hom = G.hom ≫ b) : Prop :=
  μ[G].left ≫ f = productMap f f b hf hf ≫ μ[H].left

theorem IsMulMap.comp {G : Over T'} {H : Over T} {K : Over S} [MonObj G] [MonObj H] [MonObj K]
    {b : T' ⟶ T} {f : G.left ⟶ H.left} {hf : f ≫ H.hom = G.hom ≫ b} (h₁ : IsMulMap b f hf)
    {b' : T ⟶ S} {g : H.left ⟶ K.left} {hg : g ≫ K.hom = H.hom ≫ b'} (h₂ : IsMulMap b' g hg) :
    IsMulMap (b ≫ b') (f ≫ g) (by rw [Category.assoc, hg, reassoc_of% hf]) := by
  unfold IsMulMap at h₁ h₂ ⊢
  rw [reassoc_of% h₁, h₂, ← Category.assoc, productMap_comp]

/-- The first projection of a base change is multiplicative for the base-changed group law. -/
theorem isMulMap_pullback_fst (b : T ⟶ S) (H : Grp (Over S)) :
    IsMulMap (G := ((Over.pullback b).mapGrp.obj H).X) (H := H.X) b
      (pullback.fst H.X.hom b) pullback.condition := by
  let G := ((Over.pullback b).mapGrp.obj H).X
  have h := (Langlands.GroupScheme.baseChangePointsEquiv b H (G ⊗ G)).map_mul (fst G G)
    (snd G G)
  have h' := congrArg (fun k : (Over.map b).obj (G ⊗ G) ⟶ H.X ↦ k.left) h
  simp only [Langlands.GroupScheme.baseChangePointsEquiv_left] at h'
  unfold IsMulMap
  rw [fst_mul_snd] at h'
  rw [h', Hom.mul_def, Over.comp_left]
  congr 1
  apply productMap_ext
  · rw [productMap_fst, ← Over.comp_left, lift_fst]
    rfl
  · rw [productMap_snd, ← Over.comp_left, lift_snd]
    rfl

theorem isMulMap_id (G : Over T) [MonObj G] : IsMulMap (𝟙 T) (𝟙 G.left) (by simp) := by
  unfold IsMulMap
  rw [productMap_id, Category.comp_id, Category.id_comp]

variable {G : Over T} {H : Over S} [GrpObj G] [GrpObj H] {b : T ⟶ S} {f : G.left ⟶ H.left}
  {hf : f ≫ H.hom = G.hom ≫ b}

/-- A multiplicative map commutes with the shear automorphisms. -/
theorem IsMulMap.shear_hom (h : IsMulMap b f hf) :
    productMap f f b hf hf ≫ (shear H).hom.left = (shear G).hom.left ≫ productMap f f b hf hf := by
  apply productMap_ext
  · simp only [Category.assoc, productMap_fst]
    rw [← Over.comp_left, shear_hom_fst, fst_mul_snd, ← Over.comp_left_assoc, shear_hom_fst,
      fst_mul_snd]
    exact h.symm
  · simp only [Category.assoc, productMap_snd]
    rw [← Over.comp_left, shear_hom_snd, productMap_snd, ← Over.comp_left_assoc, shear_hom_snd]

theorem IsMulMap.shear_inv (h : IsMulMap b f hf) :
    productMap f f b hf hf ≫ (shear H).inv.left = (shear G).inv.left ≫ productMap f f b hf hf := by
  rw [← cancel_mono (shear H).hom.left, Category.assoc, ← Over.comp_left, Iso.inv_hom_id,
    Over.id_left, Category.comp_id, Category.assoc, h.shear_hom, ← Over.comp_left_assoc,
    Iso.inv_hom_id, Over.id_left, Category.id_comp]

end Multiplicative

end Langlands.AlgebraicGeometry.GroupSchemeShear
