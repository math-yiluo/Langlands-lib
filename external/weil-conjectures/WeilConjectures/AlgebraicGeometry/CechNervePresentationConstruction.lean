/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Over
public import WeilConjectures.AlgebraicGeometry.AffineComparisonEtaleCechSystem
public import WeilConjectures.CategoryTheory.Pro.Generating
/-!
# Repeated intersections of compatible affine étale presentations

The product in an over-category is a wide pullback. Its universal property gives
all transition maps and cone legs, and constructs the limit of each nerve term
from the limits of the base and the individual covering members.
-/

@[expose] public section
universe v u v₁ u₁
open CategoryTheory CategoryTheory.Limits
namespace CategoryTheory.Presheaf
variable {C : Type u} [Category.{v} C] {V : C} [HasFiniteProducts (Over V)]
  {n : ℕ} (U : Fin n → Over V)
noncomputable def nerveWideCone {k : ℕ} (y : Fin (k + 1) → Fin n) :
    Cone (WidePullbackShape.wideCospan V (fun l ↦ (U (y l)).left)
      (fun l ↦ (U (y l)).hom)) :=
  (Over.ConstructProducts.conesEquiv V (Discrete.functor (fun l ↦ U (y l)))).inverse.obj
    (Fan.mk _ (Pi.π (fun l ↦ U (y l))))
noncomputable def nerveWideConeIsLimit {k : ℕ} (y : Fin (k + 1) → Fin n) :
    IsLimit (nerveWideCone U y) :=
  IsLimit.ofRightAdjoint
    (Over.ConstructProducts.conesEquiv V (Discrete.functor (fun l ↦ U (y l)))).toAdjunction
    (productIsProduct (fun l ↦ U (y l)))

section Maps
variable {D : Type u₁} [Category.{v₁} D] (F : C ⥤ D) {X : D}
  [PreservesFiniteLimits F] [HasFiniteProducts (Over X)]
  (A : Fin n → Over X) (f : X ⟶ F.obj V)
  (g : ∀ a, (A a).left ⟶ F.obj (U a).left)
  (w : ∀ a, g a ≫ F.map (U a).hom = (A a).hom ≫ f)

set_option backward.isDefEq.respectTransparency.types false in
noncomputable def nerveMapCone {k : ℕ} (y : Fin (k + 1) → Fin n) :
    Cone ((WidePullbackShape.wideCospan V (fun l ↦ (U (y l)).left)
      (fun l ↦ (U (y l)).hom)) ⋙ F) where
  pt := (cechNerveObj A y).left
  π.app z := match z with
    | none => (cechNerveObj A y).hom ≫ f
    | some l => (Pi.π (fun l ↦ A (y l)) l).left ≫ g (y l)
  π.naturality i j a := by
    simp only [Functor.const_obj_map]
    cases a with
    | id z =>
      rw [WidePullbackShape.hom_id, CategoryTheory.Functor.map_id, Category.comp_id]
      exact Category.id_comp _
    | term l =>
      dsimp [WidePullbackShape.wideCospan]
      simp only [Category.id_comp, Category.assoc, w, Over.w_assoc]

noncomputable def nerveMap {k : ℕ} (y : Fin (k + 1) → Fin n) :
    (cechNerveObj A y).left ⟶ F.obj (cechNerveObj U y).left :=
  (isLimitOfPreserves F (nerveWideConeIsLimit U y)).lift (nerveMapCone U F A f g w y)

@[reassoc (attr := simp)]
theorem nerveMap_proj {k : ℕ} (y : Fin (k + 1) → Fin n) (l : Fin (k + 1)) :
    nerveMap U F A f g w y ≫ F.map (Pi.π (fun l ↦ U (y l)) l).left =
      (Pi.π (fun l ↦ A (y l)) l).left ≫ g (y l) :=
  (isLimitOfPreserves F (nerveWideConeIsLimit U y)).fac _ (some l)

@[reassoc (attr := simp)]
theorem nerveMap_base {k : ℕ} (y : Fin (k + 1) → Fin n) :
    nerveMap U F A f g w y ≫ F.map (cechNerveObj U y).hom =
      (cechNerveObj A y).hom ≫ f :=
  (isLimitOfPreserves F (nerveWideConeIsLimit U y)).fac _ none

set_option backward.isDefEq.respectTransparency.types false in
theorem nerveMap_face {k m : ℕ} (y : Fin (m + 1) → Fin n)
    (θ : Fin (k + 1) → Fin (m + 1)) :
    (cechNerveMap A y θ).left ≫ nerveMap U F A f g w (y ∘ θ) =
      nerveMap U F A f g w y ≫ F.map (cechNerveMap U y θ).left := by
  apply (isLimitOfPreserves F (nerveWideConeIsLimit U (y ∘ θ))).hom_ext
  intro z
  cases z with
  | none =>
    change _ ≫ F.map (cechNerveObj U (y ∘ θ)).hom =
      (_ ≫ F.map (cechNerveMap U y θ).left) ≫ F.map (cechNerveObj U (y ∘ θ)).hom
    rw [Category.assoc, nerveMap_base, Category.assoc, ← F.map_comp, Over.w, nerveMap_base]
    rw [← Category.assoc, Over.w]
  | some l =>
    change _ ≫ F.map (Pi.π (fun l ↦ U (y (θ l))) l).left =
      (_ ≫ F.map (cechNerveMap U y θ).left) ≫
        F.map (Pi.π (fun l ↦ U (y (θ l))) l).left
    erw [Category.assoc, nerveMap_proj U F A f g w (y ∘ θ) l,
      Category.assoc, ← F.map_comp, ← Over.comp_left, cechNerveMap_π, nerveMap_proj]
    erw [← Category.assoc, ← Over.comp_left, cechNerveMap_π]
    rfl

theorem nerve_hom_ext {Z : D} {k : ℕ} (y : Fin (k + 1) → Fin n)
    {a b : Z ⟶ F.obj (cechNerveObj U y).left}
    (hbase : a ≫ F.map (cechNerveObj U y).hom =
      b ≫ F.map (cechNerveObj U y).hom)
    (hproj : ∀ l, a ≫ F.map (Pi.π (fun l ↦ U (y l)) l).left =
      b ≫ F.map (Pi.π (fun l ↦ U (y l)) l).left) : a = b := by
  apply (isLimitOfPreserves F (nerveWideConeIsLimit U y)).hom_ext
  intro z
  cases z with
  | none => exact hbase
  | some l => exact hproj l

end Maps
end CategoryTheory.Presheaf

namespace AlgebraicGeometry.ProEtale
universe s
open CategoryTheory.Presheaf
attribute [local instance] Over.ConstructProducts.over_finiteProducts_of_finiteWidePullbacks
variable {Y : Scheme.{s}} {V : Y.ProEt} {n : ℕ} (U : Fin n → Over V)
abbrev finiteCover : PreZeroHypercover.{0} V where
  I₀ := Fin n
  X a := (U a).left
  f a := (U a).hom
variable {I : Type s} [SmallCategory I]
  (P : (finiteCover U).RelativeLimitPresentation (Scheme.toProEt Y) I)

noncomputable abbrev presentedFamily (i : I) : Fin n → Over (P.pres.diag.obj i) :=
  fun a ↦ Over.mk ((P.f a).natTrans.app i)

theorem family_π_w (i : I) (a : Fin n) :
    (P.pres₀ a).π.app i ≫ (Scheme.toProEt Y).map ((P.f a).natTrans.app i) =
      (U a).hom ≫ P.pres.π.app i := by
  rw [← RelativeLimitPresentation.Hom.map_π, P.hf]

noncomputable def presentedTrans {i j : I} (a : i ⟶ j) (k : ℕ)
    (y : Fin (k + 1) → Fin n) :
    (cechNerveObj (presentedFamily U P i) y).left ⟶
      (cechNerveObj (presentedFamily U P j) y).left :=
  nerveMap (presentedFamily U P j) (𝟭 _) (presentedFamily U P i) (P.pres.diag.map a)
    (fun b ↦ (P.pres₀ b).diag.map a) (fun b ↦ (P.f b).natTrans.naturality a) y

noncomputable def presentedπ (k : ℕ) (y : Fin (k + 1) → Fin n) (i : I) :
    (cechNerveObj U y).left ⟶
      (Scheme.toProEt Y).obj (cechNerveObj (presentedFamily U P i) y).left :=
  nerveMap (presentedFamily U P i) (Scheme.toProEt Y) U (P.pres.π.app i)
    (fun a ↦ (P.pres₀ a).π.app i) (family_π_w U P i) y

@[reassoc (attr := simp)]
theorem presentedTrans_proj {i j : I} (a : i ⟶ j) (k : ℕ)
    (y : Fin (k + 1) → Fin n) (l : Fin (k + 1)) :
    presentedTrans U P a k y ≫ (Pi.π (fun l ↦ presentedFamily U P j (y l)) l).left =
      (Pi.π (fun l ↦ presentedFamily U P i (y l)) l).left ≫ (P.pres₀ (y l)).diag.map a :=
  nerveMap_proj _ _ _ _ _ _ _ _

@[reassoc (attr := simp)]
theorem presentedTrans_base {i j : I} (a : i ⟶ j) (k : ℕ)
    (y : Fin (k + 1) → Fin n) :
    presentedTrans U P a k y ≫ (cechNerveObj (presentedFamily U P j) y).hom =
      (cechNerveObj (presentedFamily U P i) y).hom ≫ P.pres.diag.map a :=
  nerveMap_base _ _ _ _ _ _ _

@[reassoc (attr := simp)]
theorem presentedπ_proj (k : ℕ) (y : Fin (k + 1) → Fin n) (i : I) (l : Fin (k + 1)) :
    presentedπ U P k y i ≫ (Scheme.toProEt Y).map
      (Pi.π (fun l ↦ presentedFamily U P i (y l)) l).left =
      (Pi.π (fun l ↦ U (y l)) l).left ≫ (P.pres₀ (y l)).π.app i :=
  nerveMap_proj _ _ _ _ _ _ _ _

@[reassoc (attr := simp)]
theorem presentedπ_base (k : ℕ) (y : Fin (k + 1) → Fin n) (i : I) :
    presentedπ U P k y i ≫ (Scheme.toProEt Y).map
      (cechNerveObj (presentedFamily U P i) y).hom =
      (cechNerveObj U y).hom ≫ P.pres.π.app i :=
  nerveMap_base _ _ _ _ _ _ _

set_option backward.isDefEq.respectTransparency.types false in
theorem presentedTrans_id (i : I) (k : ℕ) (y : Fin (k + 1) → Fin n) :
    presentedTrans U P (𝟙 i) k y = 𝟙 _ := by
  apply nerve_hom_ext (presentedFamily U P i) (𝟭 _) y
  · change _ ≫ (cechNerveObj (presentedFamily U P i) y).hom =
      (𝟙 _) ≫ (cechNerveObj (presentedFamily U P i) y).hom
    rw [presentedTrans_base, P.pres.diag.map_id, Category.comp_id, Category.id_comp]
  · intro l
    change _ ≫ (Pi.π (fun l ↦ presentedFamily U P i (y l)) l).left =
      (𝟙 _) ≫ (Pi.π (fun l ↦ presentedFamily U P i (y l)) l).left
    erw [presentedTrans_proj, CategoryTheory.Functor.map_id, Category.comp_id]

set_option backward.isDefEq.respectTransparency.types false in
theorem presentedTrans_comp {i j l : I} (a : i ⟶ j) (b : j ⟶ l) (k : ℕ)
    (y : Fin (k + 1) → Fin n) :
    presentedTrans U P (a ≫ b) k y =
      presentedTrans U P a k y ≫ presentedTrans U P b k y := by
  apply nerve_hom_ext (presentedFamily U P l) (𝟭 _) y
  · change _ ≫ (cechNerveObj (presentedFamily U P l) y).hom = _
    simp only [CategoryTheory.Functor.id_map, Category.assoc, presentedTrans_base,
      P.pres.diag.map_comp,
      presentedTrans_base_assoc]
  · intro z
    change _ ≫ (Pi.π (fun z ↦ presentedFamily U P l (y z)) z).left = _
    simp only [CategoryTheory.Functor.id_map, Category.assoc, presentedTrans_proj,
      CategoryTheory.Functor.map_comp, presentedTrans_proj_assoc]

set_option backward.isDefEq.respectTransparency.types false in
theorem presentedπ_naturality {i j : I} (a : i ⟶ j) (k : ℕ)
    (y : Fin (k + 1) → Fin n) :
    presentedπ U P k y i ≫ (Scheme.toProEt Y).map (presentedTrans U P a k y) =
      presentedπ U P k y j := by
  apply nerve_hom_ext (presentedFamily U P j) (Scheme.toProEt Y) y
  · rw [Category.assoc, ← CategoryTheory.Functor.map_comp, presentedTrans_base,
      CategoryTheory.Functor.map_comp,
      presentedπ_base_assoc, presentedπ_base]
    exact congrArg (fun t ↦ (cechNerveObj U y).hom ≫ t) (P.pres.cone.w a)
  · intro z
    rw [Category.assoc, ← CategoryTheory.Functor.map_comp, presentedTrans_proj,
      CategoryTheory.Functor.map_comp,
      presentedπ_proj_assoc, presentedπ_proj]
    exact congrArg (fun t ↦ (Pi.π (fun l ↦ U (y l)) z).left ≫ t)
      ((P.pres₀ (y z)).cone.w a)

noncomputable def presentedNerve (k : ℕ) (y : Fin (k + 1) → Fin n) : I ⥤ Y.Etale where
  obj i := (cechNerveObj (presentedFamily U P i) y).left
  map a := presentedTrans U P a k y
  map_id i := presentedTrans_id U P i k y
  map_comp a b := presentedTrans_comp U P a b k y

noncomputable def presentedNerveCone (k : ℕ) (y : Fin (k + 1) → Fin n) :
    Cone (presentedNerve U P k y ⋙ Scheme.toProEt Y) where
  pt := (cechNerveObj U y).left
  π.app i := presentedπ U P k y i
  π.naturality i j a := by
    change 𝟙 _ ≫ _ = _ ≫ _
    rw [Category.id_comp]
    exact (presentedπ_naturality U P a k y).symm

noncomputable def nerveBaseProjection (k : ℕ) (y : Fin (k + 1) → Fin n) :
    presentedNerve U P k y ⋙ Scheme.Etale.forget Y ⋙ Over.forget Y ⟶
      P.pres.diag ⋙ Scheme.Etale.forget Y ⋙ Over.forget Y where
  app i := (cechNerveObj (presentedFamily U P i) y).hom.left
  naturality i j a := by
    exact congrArg (Scheme.Etale.forget Y ⋙ Over.forget Y).map
      (presentedTrans_base U P a k y)

noncomputable def nerveFactorProjection (k : ℕ) (y : Fin (k + 1) → Fin n)
    (l : Fin (k + 1)) :
    presentedNerve U P k y ⋙ Scheme.Etale.forget Y ⋙ Over.forget Y ⟶
      (P.pres₀ (y l)).diag ⋙ Scheme.Etale.forget Y ⋙ Over.forget Y where
  app i := (Pi.π (fun l ↦ presentedFamily U P i (y l)) l).left.left
  naturality i j a := by
    exact congrArg (Scheme.Etale.forget Y ⋙ Over.forget Y).map
      (presentedTrans_proj U P a k y l)

set_option backward.isDefEq.respectTransparency.types false in
/-- Compatible presentations of a base and its covering members present every
nonempty repeated intersection.
Source: Stacks Project, Tag 099U, the finite Čech limit reduction, and the
universal property of a wide pullback.
(auxiliary; not a blueprint node).

Proof: Postcompose any test cone with the base and factor projections. Their
limit properties give a map to the original base and a map to each original
factor. Compatibility follows after composing with every base projection, where
it is precisely the cone equation. The wide-pullback universal property combines
these maps into a map to the original nerve term. Its composites with all stage
projections agree with the test cone because their base and factor projections
agree. The same projection argument proves uniqueness. Every transition and
face equation follows by projecting to the base and to each repeated factor. -/
noncomputable def presentedNerveIsLimit
    (hB : IsLimit ((Scheme.ProEt.forget Y ⋙ Over.forget Y).mapCone P.pres.cone))
    (hA : ∀ a, IsLimit
      ((Scheme.ProEt.forget Y ⋙ Over.forget Y).mapCone (P.pres₀ a).cone))
    (k : ℕ) (y : Fin (k + 1) → Fin n) : IsLimit
      ((Scheme.ProEt.forget Y ⋙ Over.forget Y).mapCone (presentedNerveCone U P k y)) := by
  let R := Scheme.ProEt.forget Y ⋙ Over.forget Y
  let E := Scheme.Etale.forget Y ⋙ Over.forget Y
  let L := isLimitOfPreserves R (nerveWideConeIsLimit U y)
  let L' (i : I) := isLimitOfPreserves E
    (nerveWideConeIsLimit (presentedFamily U P i) y)
  let baseCone (s : Cone ((presentedNerve U P k y ⋙ Scheme.toProEt Y) ⋙ R)) :
      Cone ((P.pres.diag ⋙ Scheme.toProEt Y) ⋙ R) :=
    (Cone.postcompose (nerveBaseProjection U P k y)).obj s
  let factorCone (s : Cone ((presentedNerve U P k y ⋙ Scheme.toProEt Y) ⋙ R))
      (l : Fin (k + 1)) : Cone (((P.pres₀ (y l)).diag ⋙ Scheme.toProEt Y) ⋙ R) :=
    (Cone.postcompose (nerveFactorProjection U P k y l)).obj s
  let c₀ (s : Cone ((presentedNerve U P k y ⋙ Scheme.toProEt Y) ⋙ R)) :
      Cone ((WidePullbackShape.wideCospan V (fun l ↦ (U (y l)).left)
        (fun l ↦ (U (y l)).hom)) ⋙ R) :=
    WidePullbackShape.mkCone (hB.lift (baseCone s))
      (fun l ↦ (hA (y l)).lift (factorCone s l)) (by
        intro l
        apply hB.hom_ext
        intro i
        change (((hA (y l)).lift (factorCone s l)) ≫ (U (y l)).hom.left) ≫
            (P.pres.π.app i).left = _
        have hw := congrArg R.map (family_π_w U P i (y l)).symm
        change (U (y l)).hom.left ≫ (P.pres.π.app i).left =
          ((P.pres₀ (y l)).π.app i).left ≫ ((P.f (y l)).natTrans.app i).left at hw
        erw [Category.assoc, hw, ← Category.assoc, (hA (y l)).fac, hB.fac]
        change (s.π.app i ≫ (Pi.π (fun l ↦ presentedFamily U P i (y l)) l).left.left) ≫
          ((P.f (y l)).natTrans.app i).left =
            s.π.app i ≫ (cechNerveObj (presentedFamily U P i) y).hom.left
        rw [Category.assoc, ← MorphismProperty.Comma.comp_left]
        exact congrArg (fun t ↦ s.π.app i ≫ E.map t)
          (Over.w (Pi.π (fun l ↦ presentedFamily U P i (y l)) l)))
  refine ⟨(fun s ↦ L.lift (c₀ s)), ?_, ?_⟩
  · intro s i
    apply (L' i).hom_ext
    intro z
    cases z with
    | none =>
      change (L.lift (c₀ s) ≫ (presentedπ U P k y i).left) ≫
        (cechNerveObj (presentedFamily U P i) y).hom.left = _
      have hw := congrArg R.map (presentedπ_base U P k y i)
      change (presentedπ U P k y i).left ≫
          (cechNerveObj (presentedFamily U P i) y).hom.left =
        (cechNerveObj U y).hom.left ≫ (P.pres.π.app i).left at hw
      rw [Category.assoc, hw, ← Category.assoc]
      change (L.lift (c₀ s) ≫ (R.mapCone (nerveWideCone U y)).π.app none) ≫ _ = _
      rw [L.fac]
      exact hB.fac (baseCone s) i
    | some l =>
      change (L.lift (c₀ s) ≫ (presentedπ U P k y i).left) ≫
        (Pi.π (fun l ↦ presentedFamily U P i (y l)) l).left.left = _
      have hw := congrArg R.map (presentedπ_proj U P k y i l)
      change (presentedπ U P k y i).left ≫
          (Pi.π (fun l ↦ presentedFamily U P i (y l)) l).left.left =
        (Pi.π (fun l ↦ U (y l)) l).left.left ≫ ((P.pres₀ (y l)).π.app i).left at hw
      rw [Category.assoc, hw, ← Category.assoc]
      change (L.lift (c₀ s) ≫ (R.mapCone (nerveWideCone U y)).π.app (some l)) ≫ _ = _
      rw [L.fac]
      exact (hA (y l)).fac (factorCone s l) i
  · intro s m hm
    change ∀ i, m ≫ (presentedπ U P k y i).left = s.π.app i at hm
    apply L.uniq (c₀ s) m
    intro z
    cases z with
    | none =>
      apply hB.hom_ext
      intro i
      change (m ≫ (cechNerveObj U y).hom.left) ≫ (P.pres.π.app i).left = _
      have hw := congrArg R.map (presentedπ_base U P k y i)
      change (presentedπ U P k y i).left ≫
          (cechNerveObj (presentedFamily U P i) y).hom.left =
        (cechNerveObj U y).hom.left ≫ (P.pres.π.app i).left at hw
      rw [Category.assoc, ← hw, ← Category.assoc, hm i]
      exact (hB.fac (baseCone s) i).symm
    | some l =>
      apply (hA (y l)).hom_ext
      intro i
      change (m ≫ (Pi.π (fun l ↦ U (y l)) l).left.left) ≫
        ((P.pres₀ (y l)).π.app i).left = _
      have hw := congrArg R.map (presentedπ_proj U P k y i l)
      change (presentedπ U P k y i).left ≫
          (Pi.π (fun l ↦ presentedFamily U P i (y l)) l).left.left =
        (Pi.π (fun l ↦ U (y l)) l).left.left ≫ ((P.pres₀ (y l)).π.app i).left at hw
      rw [Category.assoc, ← hw, ← Category.assoc, hm i]
      exact ((hA (y l)).fac (factorCone s l) i).symm

noncomputable def systemOfPresentation
    (hcov : ∀ i, Sieve.ofArrows (fun a ↦ (P.pres₀ a).diag.obj i)
      (fun a ↦ (P.f a).natTrans.app i) ∈ Y.smallEtaleTopology (P.pres.diag.obj i))
    (hAff : ∀ i, IsAffine (P.pres.diag.obj i).left)
    (hAff₀ : ∀ i a, IsAffine ((P.pres₀ a).diag.obj i).left) :
    AffineEtaleCechSystem Y V U I where
  W i := P.pres.diag.obj i
  T i a := (P.pres₀ a).diag.obj i
  f i a := (P.f a).natTrans.app i
  covering := hcov
  trans := fun a k y ↦ presentedTrans U P a k y
  trans_id := presentedTrans_id U P
  trans_comp := fun a b k y ↦ presentedTrans_comp U P a b k y
  trans_face := by
    intro i j a k m y θ
    exact (nerveMap_face (presentedFamily U P j) (𝟭 _) (presentedFamily U P i)
      (P.pres.diag.map a) (fun b ↦ (P.pres₀ b).diag.map a)
      (fun b ↦ (P.f b).natTrans.naturality a) y θ).symm
  π := presentedπ U P
  π_naturality := fun a k y ↦ presentedπ_naturality U P a k y
  π_face := fun i k m y θ ↦
    nerveMap_face (presentedFamily U P i) (Scheme.toProEt Y) U (P.pres.π.app i)
      (fun a ↦ (P.pres₀ a).π.app i) (family_π_w U P i) y θ
  affine := by
    intro i k y
    let R := Scheme.Etale.forget Y ⋙ Over.forget Y
    have hz (z : WidePullbackShape (Fin (k + 1))) :
        IsAffine (((WidePullbackShape.wideCospan (P.pres.diag.obj i)
          (fun l ↦ (presentedFamily U P i (y l)).left)
          (fun l ↦ (presentedFamily U P i (y l)).hom)) ⋙ R).obj z) := by
      cases z with
      | none => exact hAff i
      | some l => exact hAff₀ i (y l)
    exact Scheme.isAffine_of_isLimit (R.mapCone (nerveWideCone (presentedFamily U P i) y))
      (isLimitOfPreserves R (nerveWideConeIsLimit (presentedFamily U P i) y))

end AlgebraicGeometry.ProEtale
