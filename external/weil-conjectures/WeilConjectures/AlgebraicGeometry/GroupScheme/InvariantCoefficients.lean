/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.GroupScheme.Lie.InfPoints
public import Mathlib.Algebra.Group.End
import WeilConjectures.AlgebraicGeometry.DualNumbersBaseChange

/-!
# Coefficients of infinitesimal right translations

Source: the invariant-extension argument in the Lie-ring paragraph of
`WeilConjectures/AlgebraicGeometry/GroupScheme/Lie/Bracket.lean`, blueprint
`def-wf-lie-algebra-derivation`.
-/

@[expose] public section

universe u

open CategoryTheory TrivSqZeroExt
open scoped MonObj

namespace AlgebraicGeometry.GrpObj

variable {S : Scheme.{u}} (G : Over S) [GrpObj G]

/-- Right multiplication of the universal point by an infinitesimal point, as a map
`G[ε] → G`. Both factors are explicitly pulled back to `G[ε]`. -/
noncomputable def infinitesimalRightTranslation (v : infPoints G) :
    G.left.dualNumbers ⟶ G.left :=
  let X := Over.mk (G.left.dualNumbersProj ≫ G.hom)
  let p : X ⟶ G := Over.homMk G.left.dualNumbersProj rfl
  let q : X ⟶ G := Over.homMk (G.hom.dualNumbers ≫ v.1.left) (by
    rw [Category.assoc, Over.w v.1]
    exact Scheme.Hom.dualNumbers_comp_proj G.hom)
  (p * q).left

/-- Infinitesimal right translation restricts to the identity on the zero section. -/
theorem infinitesimalRightTranslation_reduction (v : infPoints G) :
    G.left.dualNumbersι ≫ infinitesimalRightTranslation G v = 𝟙 G.left := by
  let X := Over.mk (G.left.dualNumbersProj ≫ G.hom)
  let i : G ⟶ X := Over.homMk G.left.dualNumbersι (by
    change G.left.dualNumbersι ≫ G.left.dualNumbersProj ≫ G.hom = G.hom
    simp)
  let p : X ⟶ G := Over.homMk G.left.dualNumbersProj rfl
  let q : X ⟶ G := Over.homMk (G.hom.dualNumbers ≫ v.1.left) (by
    rw [Category.assoc, Over.w v.1]
    exact Scheme.Hom.dualNumbers_comp_proj G.hom)
  have hp : i ≫ p = 𝟙 G := by
    apply Over.OverMorphism.ext
    exact Scheme.dualNumbersι_comp_proj _
  have hq : i ≫ q = 1 := by
    apply Over.OverMorphism.ext
    change G.left.dualNumbersι ≫ G.hom.dualNumbers ≫ v.1.left = _
    rw [← Category.assoc, Scheme.Hom.ι_comp_dualNumbers, Category.assoc,
      ι_comp_left_eq G v.2]
    simp [Hom.one_def, unitSection, Over.toUnit_left]
  exact congrArg Over.Hom.left ((MonObj.comp_mul i p q).trans (by rw [hp, hq, mul_one]))

/-- The inverse image of an open under infinitesimal translation is that same open. -/
theorem infinitesimalRightTranslation_preimage (v : infPoints G) (U : G.left.Opens) :
    U ≤ (infinitesimalRightTranslation G v) ⁻¹ᵁ U := by
  have h := congrArg (fun f : G.left ⟶ G.left ↦ f.base)
    (infinitesimalRightTranslation_reduction G v)
  change (infinitesimalRightTranslation G v).base = 𝟙 _ at h
  change U ≤ (TopologicalSpace.Opens.map (infinitesimalRightTranslation G v).base).obj U
  rw [h]
  exact le_rfl

/-- The coefficient of ε in the comorphism of right translation. It is an explicitly
constructed additive endomorphism of the sections on each open; no witness is chosen. -/
noncomputable def invariantCoefficient (v : infPoints G) :
    ∀ U : G.left.Opens, AddMonoid.End Γ(G.left, U) := fun U ↦
  { toFun := fun a ↦ ((infinitesimalRightTranslation G v).appLE U U
      (infinitesimalRightTranslation_preimage G v U) a).snd
    map_zero' := by rw [map_zero]; rfl
    map_add' a b := by rw [map_add]; rfl }

private theorem infinitesimalRightTranslation_unit (v : infPoints G) :
    (unitSection G).dualNumbers ≫ infinitesimalRightTranslation G v = v.1.left := by
  let X := Over.mk (G.left.dualNumbersProj ≫ G.hom)
  let p : X ⟶ G := Over.homMk G.left.dualNumbersProj rfl
  let q : X ⟶ G := Over.homMk (G.hom.dualNumbers ≫ v.1.left) (by
    rw [Category.assoc, Over.w v.1]
    exact Scheme.Hom.dualNumbers_comp_proj G.hom)
  let j : Scheme.dualNumbersOver S ⟶ X := Over.homMk (unitSection G).dualNumbers (by
    change (unitSection G).dualNumbers ≫ G.left.dualNumbersProj ≫ G.hom =
      S.dualNumbersProj
    rw [Scheme.Hom.dualNumbers_comp_proj_assoc, unitSection_comp_hom,
      Category.comp_id])
  have hp : j ≫ p = 1 := by
    apply Over.OverMorphism.ext
    change (unitSection G).dualNumbers ≫ G.left.dualNumbersProj = _
    rw [Scheme.Hom.dualNumbers_comp_proj]
    simp [Hom.one_def, unitSection, Over.toUnit_left]
  have hq : j ≫ q = v.1 := by
    apply Over.OverMorphism.ext
    change (unitSection G).dualNumbers ≫ G.hom.dualNumbers ≫ v.1.left = v.1.left
    rw [← Category.assoc, ← Scheme.Hom.dualNumbers_comp, unitSection_comp_hom,
      Scheme.Hom.dualNumbers_id, Category.id_comp]
  exact congrArg Over.Hom.left ((MonObj.comp_mul j p q).trans (by rw [hp, hq, one_mul]))

set_option backward.isDefEq.respectTransparency false in
private theorem dualNumbers_hom_ext_coeff {X : Scheme.{u}} (m n : X.dualNumbers ⟶ X)
    (hm : X.dualNumbersι ≫ m = 𝟙 X) (hn : X.dualNumbersι ≫ n = 𝟙 X)
    (em : ∀ U : X.Opens, U ≤ m ⁻¹ᵁ U) (en : ∀ U : X.Opens, U ≤ n ⁻¹ᵁ U)
    (h : ∀ (U : X.Opens) (a : Γ(X, U)),
      (m.appLE U U (em U) a).snd = (n.appLE U U (en U) a).snd) : m = n := by
  have hb₁ := congrArg (fun f : X ⟶ X ↦ f.base) hm
  have hb₂ := congrArg (fun f : X ⟶ X ↦ f.base) hn
  rcases m with ⟨⟨⟨vb, vc⟩, vp⟩⟩
  rcases n with ⟨⟨⟨wb, wc⟩, wp⟩⟩
  change vb = 𝟙 _ at hb₁
  change wb = 𝟙 _ at hb₂
  subst vb wb
  refine Scheme.Hom.ext rfl fun U ↦ ?_
  simp only [eqToHom_refl]
  erw [X.dualNumbers.presheaf.map_id, Category.comp_id]
  ext a : 2
  apply TrivSqZeroExt.ext
  · have h₁ := ConcreteCategory.congr_hom (Scheme.Hom.congr_app hm U) a
    have h₂ := ConcreteCategory.congr_hom (Scheme.Hom.congr_app hn U) a
    simp only [Scheme.Hom.comp_app, eqToHom_refl, op_id,
      Scheme.Hom.id_app] at h₁ h₂
    erw [X.presheaf.map_id, Category.comp_id] at h₁ h₂
    change (vc.app (Opposite.op U) a).fst = a at h₁
    change (wc.app (Opposite.op U) a).fst = a at h₂
    exact h₁.trans h₂.symm
  · have h' := h U a
    simp only [Scheme.Hom.appLE, homOfLE_refl, op_id] at h'
    erw [X.dualNumbers.presheaf.map_id, Category.comp_id] at h'
    exact h'

private theorem invariantCoefficient_injective : Function.Injective (invariantCoefficient G) := by
  intro v w h
  have hm : infinitesimalRightTranslation G v = infinitesimalRightTranslation G w := by
    apply dualNumbers_hom_ext_coeff _ _
      (infinitesimalRightTranslation_reduction G v)
      (infinitesimalRightTranslation_reduction G w)
      (infinitesimalRightTranslation_preimage G v)
      (infinitesimalRightTranslation_preimage G w)
    intro U a
    exact congrArg (fun F ↦ F U a) h
  apply Subtype.ext
  apply Over.OverMorphism.ext
  rw [← infinitesimalRightTranslation_unit G v, ← infinitesimalRightTranslation_unit G w, hm]

private theorem infinitesimalRightTranslation_one :
    infinitesimalRightTranslation G 1 = G.left.dualNumbersProj := by
  let X := Over.mk (G.left.dualNumbersProj ≫ G.hom)
  let p : X ⟶ G := Over.homMk G.left.dualNumbersProj rfl
  let k : X ⟶ Scheme.dualNumbersOver S := Over.homMk G.hom.dualNumbers
    (Scheme.Hom.dualNumbers_comp_proj G.hom)
  have h : p * (k ≫ (1 : Scheme.dualNumbersOver S ⟶ G)) = p := by
    rw [MonObj.comp_one, mul_one]
  exact congrArg Over.Hom.left h

private theorem invariantCoefficient_one : invariantCoefficient G 1 = 0 := by
  ext U a
  have h (m : G.left.dualNumbers ⟶ G.left) (e : U ≤ m ⁻¹ᵁ U)
      (hm : m = G.left.dualNumbersProj) : (m.appLE U U e a).snd = 0 := by
    subst m
    simp only [Scheme.Hom.appLE, homOfLE_refl, op_id]
    erw [G.left.dualNumbers.presheaf.map_id, Category.comp_id]
    rfl
  exact h _ _ (infinitesimalRightTranslation_one G)

private theorem infinitesimalRightTranslation_over (v : infPoints G) :
    infinitesimalRightTranslation G v ≫ G.hom =
      G.hom.dualNumbers ≫ S.dualNumbersProj := by
  let X := Over.mk (G.left.dualNumbersProj ≫ G.hom)
  let p : X ⟶ G := Over.homMk G.left.dualNumbersProj rfl
  let q : X ⟶ G := Over.homMk (G.hom.dualNumbers ≫ v.1.left) (by
    rw [Category.assoc, Over.w v.1]
    exact Scheme.Hom.dualNumbers_comp_proj G.hom)
  exact (Over.w (p * q)).trans (Scheme.Hom.dualNumbers_comp_proj G.hom).symm

private noncomputable def liftedRightTranslation (v : infPoints G) :
    G.left.dualNumbers ⟶ G.left.dualNumbers :=
  (Scheme.isPullback_dualNumbersProj G.hom).lift
    (infinitesimalRightTranslation G v) G.hom.dualNumbers
    (infinitesimalRightTranslation_over G v)

private theorem liftedRightTranslation_proj (v : infPoints G) :
    liftedRightTranslation G v ≫ G.left.dualNumbersProj =
      infinitesimalRightTranslation G v :=
  (Scheme.isPullback_dualNumbersProj G.hom).lift_fst _ _ _

private theorem liftedRightTranslation_over (v : infPoints G) :
    liftedRightTranslation G v ≫ G.hom.dualNumbers = G.hom.dualNumbers :=
  (Scheme.isPullback_dualNumbersProj G.hom).lift_snd _ _ _

private theorem liftedRightTranslation_comp (v w : infPoints G) :
    liftedRightTranslation G v ≫ infinitesimalRightTranslation G w =
      infinitesimalRightTranslation G (v * w) := by
  let X := Over.mk (G.left.dualNumbersProj ≫ G.hom)
  let p : X ⟶ G := Over.homMk G.left.dualNumbersProj rfl
  let k : X ⟶ Scheme.dualNumbersOver S := Over.homMk G.hom.dualNumbers
    (Scheme.Hom.dualNumbers_comp_proj G.hom)
  let F : X ⟶ X := Over.homMk (liftedRightTranslation G v) (by
    change liftedRightTranslation G v ≫ G.left.dualNumbersProj ≫ G.hom = _
    rw [← Category.assoc, liftedRightTranslation_proj]
    exact (infinitesimalRightTranslation_over G v).trans
      (Scheme.Hom.dualNumbers_comp_proj G.hom))
  have hp : F ≫ p = p * (k ≫ v.1) := by
    apply Over.OverMorphism.ext
    exact liftedRightTranslation_proj G v
  have hk : F ≫ k = k := by
    apply Over.OverMorphism.ext
    exact liftedRightTranslation_over G v
  have h : F ≫ (p * (k ≫ w.1)) = p * (k ≫ (v.1 * w.1)) := by
    rw [MonObj.comp_mul, hp, ← Category.assoc F k, hk, MonObj.comp_mul, mul_assoc]
  exact congrArg Over.Hom.left h

set_option backward.isDefEq.respectTransparency false in
private theorem dualNumbers_appLE_fst {X : Scheme.{u}} (m : X.dualNumbers ⟶ X)
    (hm : X.dualNumbersι ≫ m = 𝟙 X) (U : X.Opens)
    (e : U ≤ m ⁻¹ᵁ U) (a : Γ(X, U)) : (m.appLE U U e a).fst = a := by
  have hb := congrArg (fun f : X ⟶ X ↦ f.base) hm
  rcases m with ⟨⟨⟨mb, mc⟩, mp⟩⟩
  change mb = 𝟙 _ at hb
  subst mb
  have h := ConcreteCategory.congr_hom (Scheme.Hom.congr_app hm U) a
  simp only [Scheme.Hom.comp_app, eqToHom_refl, op_id, Scheme.Hom.id_app] at h
  erw [X.presheaf.map_id, Category.comp_id] at h
  simp only [Scheme.Hom.appLE, homOfLE_refl, op_id]
  erw [X.dualNumbers.presheaf.map_id, Category.comp_id]
  exact h

private theorem liftedRightTranslation_base (v : infPoints G) :
    (liftedRightTranslation G v).base = 𝟙 _ := by
  have hm := congrArg (fun f : G.left ⟶ G.left ↦ f.base)
    (infinitesimalRightTranslation_reduction G v)
  have hF := congrArg (fun f : G.left.dualNumbers ⟶ G.left ↦ f.base)
    (liftedRightTranslation_proj G v)
  change (infinitesimalRightTranslation G v).base = 𝟙 _ at hm
  change (liftedRightTranslation G v).base ≫ 𝟙 _ = _ at hF
  exact (Category.comp_id _).symm.trans (hF.trans hm)

private theorem liftedRightTranslation_preimage (v : infPoints G) (U : G.left.Opens) :
    U ≤ liftedRightTranslation G v ⁻¹ᵁ U := by
  change U ≤ (TopologicalSpace.Opens.map (liftedRightTranslation G v).base).obj U
  rw [liftedRightTranslation_base G v]
  exact le_rfl

private theorem dualNumbers_map_eps {R T : Type u} [CommRing R] [CommRing T]
    (f : R →+* T) : DualNumber.mapRingHom f (inr 1) = inr 1 := by
  ext <;> simp

private theorem liftedRightTranslation_eps (v : infPoints G) (U : G.left.Opens) :
    (liftedRightTranslation G v).appLE U U (liftedRightTranslation_preimage G v U)
      (inr 1) = inr 1 := by
  let F := liftedRightTranslation G v
  have htop : F.appTop (inr 1) = inr 1 := by
    have h := ConcreteCategory.congr_hom
      (Scheme.Hom.congr_app (liftedRightTranslation_over G v) ⊤)
      (inr 1 : DualNumber Γ(S, ⊤))
    simp only [Scheme.Hom.comp_app, eqToHom_refl, op_id] at h
    erw [G.left.dualNumbers.presheaf.map_id, Category.comp_id] at h
    change F.appTop (DualNumber.mapRingHom G.hom.appTop.hom (inr 1)) =
      DualNumber.mapRingHom G.hom.appTop.hom (inr 1) at h
    simpa only [dualNumbers_map_eps] using h
  have h := ConcreteCategory.congr_hom
    (F.map_appLE (liftedRightTranslation_preimage G v U)
      (homOfLE le_top : U ⟶ ⊤).op) (inr 1 : DualNumber Γ(G.left, ⊤))
  change F.appLE U U _ (DualNumber.mapRingHom
      (G.left.presheaf.map (homOfLE le_top : U ⟶ ⊤).op).hom (inr 1)) =
    DualNumber.mapRingHom (G.left.presheaf.map _).hom (F.appTop (inr 1)) at h
  simpa only [dualNumbers_map_eps, htop] using h

set_option backward.isDefEq.respectTransparency false in
private theorem liftedRightTranslation_inl (v : infPoints G) (U : G.left.Opens)
    (a : Γ(G.left, U)) :
    (liftedRightTranslation G v).appLE U U (liftedRightTranslation_preimage G v U)
        (inl a) =
      (infinitesimalRightTranslation G v).appLE U U
        (infinitesimalRightTranslation_preimage G v U) a := by
  have h := ConcreteCategory.congr_hom (Scheme.Hom.appLE_comp_appLE
    (liftedRightTranslation G v) G.left.dualNumbersProj U U U le_rfl
    (liftedRightTranslation_preimage G v U)) a
  simp only [liftedRightTranslation_proj] at h
  have hi : G.left.dualNumbersProj.appLE U U le_rfl a = inl a := by
    simp only [Scheme.Hom.appLE, homOfLE_refl, op_id]
    erw [G.left.dualNumbers.presheaf.map_id, Category.comp_id]
    rfl
  change (liftedRightTranslation G v).appLE U U _
    (G.left.dualNumbersProj.appLE U U le_rfl a) = _ at h
  rw [hi] at h
  exact h

private theorem liftedRightTranslation_snd (v : infPoints G) (U : G.left.Opens)
    (x : DualNumber Γ(G.left, U)) :
    ((liftedRightTranslation G v).appLE U U (liftedRightTranslation_preimage G v U)
      x).snd = invariantCoefficient G v U x.fst + x.snd := by
  let F : DualNumber Γ(G.left, U) →+* DualNumber Γ(G.left, U) :=
    ((liftedRightTranslation G v).appLE U U
      (liftedRightTranslation_preimage G v U)).hom
  have hx : x = inl x.fst + inl x.snd * inr 1 := by ext <;> simp
  have hf (a : Γ(G.left, U)) : (F (inl a)).fst = a := by
    change ((liftedRightTranslation G v).appLE U U _ (inl a)).fst = a
    rw [liftedRightTranslation_inl]
    exact dualNumbers_appLE_fst _ (infinitesimalRightTranslation_reduction G v) U _ a
  have he : F (inr 1) = inr 1 := liftedRightTranslation_eps G v U
  have hs (a : Γ(G.left, U)) : (F (inl a)).snd = invariantCoefficient G v U a := by
    change ((liftedRightTranslation G v).appLE U U _ (inl a)).snd = _
    rw [liftedRightTranslation_inl]
    rfl
  change (F x).snd = _
  calc
    (F x).snd = (F (inl x.fst + inl x.snd * inr 1)).snd := congrArg (fun y ↦ (F y).snd) hx
    _ = invariantCoefficient G v U x.fst + x.snd := by
      rw [map_add, map_mul, he]
      simp [hf, hs]

set_option backward.isDefEq.respectTransparency false in
/-- Multiplication of infinitesimal points adds the invariant coefficient operators.

Source: the first coefficient step of the Lie-ring paragraph in
`WeilConjectures/AlgebraicGeometry/GroupScheme/Lie/Bracket.lean`.
(blueprint: lem-ag-invariant-coefficient-add)

Proof: Right translation by v*w is the composition of right translation by v and by w,
using the same square-zero parameter ε. On an open U, the two comorphisms are
`a ↦ a + ε D_v(a)` and `a ↦ a + ε D_w(a)`. The lifted maps fix ε, since they are over
S[ε], and apply their coefficients to functions on G. Their composition therefore
sends a to `a + ε(D_v(a)+D_w(a))`: the remaining term contains ε² and vanishes.
The coefficients are precisely the explicit `invariantCoefficient` maps, so they
agree on every open. This works sheafwise on an arbitrary base scheme, including
the empty scheme, and uses no division or characteristic assumption. -/
theorem invariantCoefficient_mul (v w : infPoints G) :
    invariantCoefficient G (v * w) = invariantCoefficient G v + invariantCoefficient G w := by
  ext U a
  have h := ConcreteCategory.congr_hom (Scheme.Hom.appLE_comp_appLE
    (liftedRightTranslation G v) (infinitesimalRightTranslation G w) U U U
    (infinitesimalRightTranslation_preimage G w U)
    (liftedRightTranslation_preimage G v U)) a
  simp only [liftedRightTranslation_comp] at h
  change ((infinitesimalRightTranslation G (v * w)).appLE U U _ a).snd =
    invariantCoefficient G v U a + invariantCoefficient G w U a
  rw [← h]
  change ((liftedRightTranslation G v).appLE U U _
    ((infinitesimalRightTranslation G w).appLE U U _ a)).snd = _
  rw [liftedRightTranslation_snd]
  rw [dualNumbers_appLE_fst _ (infinitesimalRightTranslation_reduction G w)]
  rfl

/-- The explicit invariant coefficient operators form a faithful additive realization
of infinitesimal points. -/
theorem invariantCoefficient_faithful_additive :
    Function.Injective (invariantCoefficient G) ∧
      (∀ v w : infPoints G,
        invariantCoefficient G (v * w) = invariantCoefficient G v + invariantCoefficient G w) ∧
      invariantCoefficient G 1 = 0 :=
  ⟨invariantCoefficient_injective G, invariantCoefficient_mul G, invariantCoefficient_one G⟩

end AlgebraicGeometry.GrpObj
