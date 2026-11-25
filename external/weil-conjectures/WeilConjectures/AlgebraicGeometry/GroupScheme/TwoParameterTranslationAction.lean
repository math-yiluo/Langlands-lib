/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.GroupScheme.InvariantCoefficients
import WeilConjectures.AlgebraicGeometry.DualNumbersBaseChange

/-!
# Section operators of two-parameter right translations

Source: the invariant-extension and mixed-coefficient steps in the Lie-ring paragraph of
`WeilConjectures/AlgebraicGeometry/GroupScheme/Lie/Bracket.lean` (blueprint
`def-wf-lie-algebra-derivation`).
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory TrivSqZeroExt
open scoped MonObj

namespace AlgebraicGeometry.GrpObj

variable {S : Scheme.{u}} (G : Over S) [GrpObj G]

/-- Right translation of the universal point by a point over `S[ε][δ]`.
(blueprint: lem-ag-two-parameter-translation-action)
-/
noncomputable def twoParameterRightTranslation (z : Scheme.dualNumbers₂Over S ⟶ G) :
    G.left.dualNumbers.dualNumbers ⟶ G.left :=
  let X := Over.mk
    (G.left.dualNumbers.dualNumbersProj ≫ G.left.dualNumbersProj ≫ G.hom)
  let p : X ⟶ G := Over.homMk
    (G.left.dualNumbers.dualNumbersProj ≫ G.left.dualNumbersProj) (Category.assoc _ _ _)
  let q : X ⟶ G := Over.homMk (G.hom.dualNumbers.dualNumbers ≫ z.left) (by
    rw [Category.assoc, Over.w z]
    change G.hom.dualNumbers.dualNumbers ≫
      S.dualNumbers.dualNumbersProj ≫ S.dualNumbersProj =
        G.left.dualNumbers.dualNumbersProj ≫ G.left.dualNumbersProj ≫ G.hom
    rw [Scheme.Hom.dualNumbers_comp_proj_assoc, Scheme.Hom.dualNumbers_comp_proj])
  (p * q).left

/-- The coefficientwise operator `1 + εD` on a double square-zero extension.
(blueprint: lem-ag-two-parameter-translation-action)
-/
def epsilonSectionAction {R : Type u} [CommRing R] (D : AddMonoid.End R)
    (x : DualNumber (DualNumber R)) : DualNumber (DualNumber R) :=
  ⟨⟨x.fst.fst, x.fst.snd + D x.fst.fst⟩,
    ⟨x.snd.fst, x.snd.snd + D x.snd.fst⟩⟩

/-- The coefficientwise operator `1 + δD` on a double square-zero extension.
(blueprint: lem-ag-two-parameter-translation-action)
-/
def deltaSectionAction {R : Type u} [CommRing R] (D : AddMonoid.End R)
    (x : DualNumber (DualNumber R)) : DualNumber (DualNumber R) :=
  ⟨x.fst, ⟨x.snd.fst + D x.fst.fst, x.snd.snd + D x.fst.snd⟩⟩

/-- The double thickening of G, viewed over S. -/
private noncomputable def translationDoubleSource : Over S :=
  Over.mk (G.left.dualNumbers.dualNumbersProj ≫ G.left.dualNumbersProj ≫ G.hom)

/-- The universal point of G on its double thickening. -/
private noncomputable def translationDoublePoint : translationDoubleSource G ⟶ G :=
  Over.homMk (G.left.dualNumbers.dualNumbersProj ≫ G.left.dualNumbersProj)
    (Category.assoc _ _ _)

/-- The parameter map of the double thickening of G. -/
private noncomputable def translationDoubleParameters :
    translationDoubleSource G ⟶ Scheme.dualNumbers₂Over S :=
  Over.homMk G.hom.dualNumbers.dualNumbers (by
    change G.hom.dualNumbers.dualNumbers ≫
      S.dualNumbers.dualNumbersProj ≫ S.dualNumbersProj = _
    rw [Scheme.Hom.dualNumbers_comp_proj_assoc, Scheme.Hom.dualNumbers_comp_proj]
    rfl)

/-- Right translation, retaining both parameters, constructed by two cartesian lifts. -/
private noncomputable def liftedTwoParameterTranslation (z : Scheme.dualNumbers₂Over S ⟶ G) :
    G.left.dualNumbers.dualNumbers ⟶ G.left.dualNumbers.dualNumbers :=
  let k := translationDoubleParameters G
  let r := translationDoublePoint G * (k ≫ z)
  let r₁ := (Scheme.isPullback_dualNumbersProj G.hom).lift r.left
    (k.left ≫ S.dualNumbers.dualNumbersProj) (by
      exact (Over.w r).trans (Over.w k).symm)
  (Scheme.isPullback_dualNumbersProj G.hom.dualNumbers).lift r₁ k.left
    ((Scheme.isPullback_dualNumbersProj G.hom).lift_snd _ _ _)

private theorem liftedTwoParameterTranslation_inner (z : Scheme.dualNumbers₂Over S ⟶ G) :
    liftedTwoParameterTranslation G z ≫ G.left.dualNumbers.dualNumbersProj =
      (Scheme.isPullback_dualNumbersProj G.hom).lift
        (translationDoublePoint G * (translationDoubleParameters G ≫ z)).left
        ((translationDoubleParameters G).left ≫ S.dualNumbers.dualNumbersProj)
        (by
          exact (Over.w (translationDoublePoint G *
            (translationDoubleParameters G ≫ z))).trans
            (Over.w (translationDoubleParameters G)).symm) :=
  (Scheme.isPullback_dualNumbersProj G.hom.dualNumbers).lift_fst _ _ _

/-- The lift has the prescribed underlying right translation. -/
private theorem liftedTwoParameterTranslation_proj (z : Scheme.dualNumbers₂Over S ⟶ G) :
    liftedTwoParameterTranslation G z ≫
      G.left.dualNumbers.dualNumbersProj ≫ G.left.dualNumbersProj =
        (translationDoublePoint G * (translationDoubleParameters G ≫ z)).left := by
  rw [← Category.assoc, liftedTwoParameterTranslation_inner]
  exact (Scheme.isPullback_dualNumbersProj G.hom).lift_fst _ _ _

/-- The lift fixes the two base parameters. -/
private theorem liftedTwoParameterTranslation_over (z : Scheme.dualNumbers₂Over S ⟶ G) :
    liftedTwoParameterTranslation G z ≫ G.hom.dualNumbers.dualNumbers =
      G.hom.dualNumbers.dualNumbers :=
  (Scheme.isPullback_dualNumbersProj G.hom.dualNumbers).lift_snd _ _ _

omit [GrpObj G] in
private theorem double_hom_ext (f g : G.left.dualNumbers.dualNumbers ⟶
    G.left.dualNumbers.dualNumbers)
    (hp : f ≫ G.left.dualNumbers.dualNumbersProj ≫ G.left.dualNumbersProj =
      g ≫ G.left.dualNumbers.dualNumbersProj ≫ G.left.dualNumbersProj)
    (hk : f ≫ G.hom.dualNumbers.dualNumbers = g ≫ G.hom.dualNumbers.dualNumbers) :
    f = g := by
  apply (Scheme.isPullback_dualNumbersProj G.hom.dualNumbers).hom_ext
  · apply (Scheme.isPullback_dualNumbersProj G.hom).hom_ext
    · simpa only [Category.assoc] using hp
    · simpa only [Category.assoc, Scheme.Hom.dualNumbers_comp_proj] using
        congrArg (fun h ↦ h ≫ S.dualNumbers.dualNumbersProj) hk
  · exact hk

/-- Successive parameter-preserving right translations multiply their points. -/
private theorem liftedTwoParameterTranslation_comp (z t : Scheme.dualNumbers₂Over S ⟶ G) :
    liftedTwoParameterTranslation G z ≫ liftedTwoParameterTranslation G t =
      liftedTwoParameterTranslation G (z * t) := by
  let X := translationDoubleSource G
  let p := translationDoublePoint G
  let k := translationDoubleParameters G
  let F : X ⟶ X := Over.homMk (liftedTwoParameterTranslation G z) (by
    change liftedTwoParameterTranslation G z ≫
      G.left.dualNumbers.dualNumbersProj ≫ G.left.dualNumbersProj ≫ G.hom = _
    rw [← Category.assoc _ _ G.hom, ← Category.assoc,
      liftedTwoParameterTranslation_proj]
    exact Over.w (p * (k ≫ z)))
  have hp : F ≫ p = p * (k ≫ z) := by
    apply Over.OverMorphism.ext
    exact liftedTwoParameterTranslation_proj G z
  have hk : F ≫ k = k := by
    apply Over.OverMorphism.ext
    exact liftedTwoParameterTranslation_over G z
  apply double_hom_ext G
  · rw [Category.assoc, liftedTwoParameterTranslation_proj,
      liftedTwoParameterTranslation_proj]
    have h : F ≫ (p * (k ≫ t)) = p * (k ≫ (z * t)) := by
      rw [MonObj.comp_mul, hp, ← Category.assoc F k, hk, MonObj.comp_mul, mul_assoc]
    exact congrArg Over.Hom.left h
  · rw [Category.assoc, liftedTwoParameterTranslation_over,
      liftedTwoParameterTranslation_over, liftedTwoParameterTranslation_over]

private theorem translation_double_factor (v : infPoints G)
    (h : Scheme.dualNumbers₂Over S ⟶ Scheme.dualNumbersOver S)
    (f : G.left.dualNumbers.dualNumbers ⟶ G.left.dualNumbers)
    (hp : f ≫ G.left.dualNumbersProj =
      G.left.dualNumbers.dualNumbersProj ≫ G.left.dualNumbersProj)
    (hk : f ≫ G.hom.dualNumbers = G.hom.dualNumbers.dualNumbers ≫ h.left) :
    (translationDoublePoint G * (translationDoubleParameters G ≫ h ≫ v.1)).left =
      f ≫ infinitesimalRightTranslation G v := by
  let Y := Over.mk (G.left.dualNumbersProj ≫ G.hom)
  let F : translationDoubleSource G ⟶ Y := Over.homMk f (by
    change f ≫ G.left.dualNumbersProj ≫ G.hom = _
    rw [← Category.assoc, hp]
    rfl)
  let p : Y ⟶ G := Over.homMk G.left.dualNumbersProj rfl
  let q : Y ⟶ G := Over.homMk (G.hom.dualNumbers ≫ v.1.left) (by
    rw [Category.assoc, Over.w v.1]
    exact Scheme.Hom.dualNumbers_comp_proj G.hom)
  have hp' : F ≫ p = translationDoublePoint G := Over.OverMorphism.ext hp
  have hq : F ≫ q = translationDoubleParameters G ≫ h ≫ v.1 := by
    apply Over.OverMorphism.ext
    change f ≫ G.hom.dualNumbers ≫ v.1.left = _
    rw [← Category.assoc, hk, Category.assoc]
    rfl
  have hh := congrArg Over.Hom.left (MonObj.comp_mul F p q)
  change f ≫ infinitesimalRightTranslation G v = _ at hh
  rw [hp', hq] at hh
  exact hh.symm

/-- Forgetting δ gives the usual ε-translation. -/
private theorem liftedTwoParameterTranslation_epsilon_proj (v : infPoints G) :
    liftedTwoParameterTranslation G (Scheme.dualNumbersProjεOver S ≫ v.1) ≫
      G.left.dualNumbers.dualNumbersProj ≫ G.left.dualNumbersProj =
        G.left.dualNumbers.dualNumbersProj ≫ infinitesimalRightTranslation G v := by
  rw [liftedTwoParameterTranslation_proj]
  exact translation_double_factor G v (Scheme.dualNumbersProjεOver S)
    G.left.dualNumbers.dualNumbersProj rfl
    (Scheme.Hom.dualNumbers_comp_proj G.hom.dualNumbers).symm

/-- Forgetting ε gives the usual δ-translation. -/
private theorem liftedTwoParameterTranslation_delta_proj (v : infPoints G) :
    liftedTwoParameterTranslation G (Scheme.dualNumbersProjδOver S ≫ v.1) ≫
      G.left.dualNumbers.dualNumbersProj ≫ G.left.dualNumbersProj =
        G.left.dualNumbersProj.dualNumbers ≫ infinitesimalRightTranslation G v := by
  rw [liftedTwoParameterTranslation_proj]
  apply translation_double_factor G v (Scheme.dualNumbersProjδOver S)
    G.left.dualNumbersProj.dualNumbers
  · exact Scheme.Hom.dualNumbers_comp_proj _
  · change G.left.dualNumbersProj.dualNumbers ≫ G.hom.dualNumbers =
      G.hom.dualNumbers.dualNumbers ≫ S.dualNumbersProj.dualNumbers
    rw [← Scheme.Hom.dualNumbers_comp, ← Scheme.Hom.dualNumbers_comp,
      Scheme.Hom.dualNumbers_comp_proj]

private theorem infinitesimal_translation_base (v : infPoints G) :
    (infinitesimalRightTranslation G v).base = 𝟙 _ := by
  have h := congrArg (fun f : G.left ⟶ G.left ↦ f.base)
    (infinitesimalRightTranslation_reduction G v)
  exact h

/-- The ε-translation lift acts identically on the underlying space. -/
private theorem liftedTwoParameterTranslation_epsilon_base (v : infPoints G) :
    (liftedTwoParameterTranslation G (Scheme.dualNumbersProjεOver S ≫ v.1)).base =
      𝟙 _ := by
  have h := congrArg (fun f : G.left.dualNumbers.dualNumbers ⟶ G.left ↦ f.base)
    (liftedTwoParameterTranslation_epsilon_proj G v)
  change (liftedTwoParameterTranslation G _).base ≫ 𝟙 _ ≫ 𝟙 _ =
    𝟙 _ ≫ (infinitesimalRightTranslation G v).base at h
  ext x
  have hx := congrArg (fun f ↦ f x) h
  rw [infinitesimal_translation_base] at hx
  exact hx

/-- The δ-translation lift acts identically on the underlying space. -/
private theorem liftedTwoParameterTranslation_delta_base (v : infPoints G) :
    (liftedTwoParameterTranslation G (Scheme.dualNumbersProjδOver S ≫ v.1)).base =
      𝟙 _ := by
  have h := congrArg (fun f : G.left.dualNumbers.dualNumbers ⟶ G.left ↦ f.base)
    (liftedTwoParameterTranslation_delta_proj G v)
  change (liftedTwoParameterTranslation G _).base ≫ 𝟙 _ ≫ 𝟙 _ =
    𝟙 _ ≫ (infinitesimalRightTranslation G v).base at h
  ext x
  have hx := congrArg (fun f ↦ f x) h
  rw [infinitesimal_translation_base] at hx
  exact hx

-- Section-map calculations use the lift's proved equations, not its cartesian construction.
attribute [local irreducible] liftedTwoParameterTranslation

omit [GrpObj G] in
private theorem proj_appLE (X : Scheme.{u}) (U : X.Opens) (a : Γ(X, U)) :
    X.dualNumbersProj.appLE U U le_rfl a = inl a := by
  simp only [Scheme.Hom.appLE, homOfLE_refl, op_id]
  erw [X.dualNumbers.presheaf.map_id, Category.comp_id]
  rfl

private theorem translation_appLE (v : infPoints G) (U : G.left.Opens)
    (a : Γ(G.left, U)) :
    (infinitesimalRightTranslation G v).appLE U U
      (infinitesimalRightTranslation_preimage G v U) a =
      ⟨a, invariantCoefficient G v U a⟩ := by
  apply TrivSqZeroExt.ext
  · have hfst_generic : ∀ {X : Scheme.{u}} (m : X.dualNumbers ⟶ X),
        X.dualNumbersι ≫ m = 𝟙 X → ∀ (U : X.Opens)
        (e : U ≤ m ⁻¹ᵁ U) (a : Γ(X, U)), (m.appLE U U e a).fst = a := by
      intro X m hm U e a
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
    exact hfst_generic (infinitesimalRightTranslation G v)
      (infinitesimalRightTranslation_reduction G v) U _ a
  · rfl

omit [GrpObj G] in
private theorem dual_appLE {X Y : Scheme.{u}} (f : X ⟶ Y)
    (U : Y.Opens) (V : X.Opens) (e : V ≤ f ⁻¹ᵁ U) (x : DualNumber Γ(Y, U)) :
    f.dualNumbers.appLE U V e x = DualNumber.mapRingHom (f.appLE U V e).hom x := by
  change DualNumber.mapRingHom (X.presheaf.map (homOfLE e).op).hom
    (DualNumber.mapRingHom (f.app U).hom x) = _
  exact (RingHom.congr_fun (DualNumber.mapRingHom_comp (f.app U).hom
    (X.presheaf.map (homOfLE e).op).hom) x).symm

private theorem lift_preimage (z : Scheme.dualNumbers₂Over S ⟶ G)
    (hb : (liftedTwoParameterTranslation G z).base = 𝟙 _) (U : G.left.Opens) :
    U ≤ (liftedTwoParameterTranslation G z) ⁻¹ᵁ U := by
  change U ≤ (TopologicalSpace.Opens.map (liftedTwoParameterTranslation G z).base).obj U
  rw [hb]
  exact le_rfl

private theorem lifted_epsilon_constants (v : infPoints G) (U : G.left.Opens)
    (a : Γ(G.left, U)) :
    (liftedTwoParameterTranslation G (Scheme.dualNumbersProjεOver S ≫ v.1)).appLE U U
      (lift_preimage G _ (liftedTwoParameterTranslation_epsilon_base G v) U)
      (inl (inl a)) = inl ⟨a, invariantCoefficient G v U a⟩ := by
  let F := liftedTwoParameterTranslation G (Scheme.dualNumbersProjεOver S ≫ v.1)
  have eF := lift_preimage G _ (liftedTwoParameterTranslation_epsilon_base G v) U
  have h := ConcreteCategory.congr_hom (Scheme.Hom.appLE_comp_appLE F
    (G.left.dualNumbers.dualNumbersProj ≫ G.left.dualNumbersProj) U U U le_rfl eF) a
  have hi := ConcreteCategory.congr_hom (Scheme.Hom.appLE_comp_appLE
    G.left.dualNumbers.dualNumbersProj G.left.dualNumbersProj U U U le_rfl le_rfl) a
  change G.left.dualNumbers.dualNumbersProj.appLE U U _
    (G.left.dualNumbersProj.appLE U U _ a) = _ at hi
  rw [proj_appLE, proj_appLE] at hi
  change F.appLE U U _
    ((G.left.dualNumbers.dualNumbersProj ≫ G.left.dualNumbersProj).appLE U U _ a) = _ at h
  rw [← hi] at h
  have hp := liftedTwoParameterTranslation_epsilon_proj G v
  change F ≫ _ = _ at hp
  simp only [hp] at h
  have ht := ConcreteCategory.congr_hom (Scheme.Hom.appLE_comp_appLE
    G.left.dualNumbers.dualNumbersProj (infinitesimalRightTranslation G v) U U U
    (infinitesimalRightTranslation_preimage G v U) le_rfl) a
  change G.left.dualNumbers.dualNumbersProj.appLE U U _
    ((infinitesimalRightTranslation G v).appLE U U _ a) = _ at ht
  rw [proj_appLE, translation_appLE] at ht
  exact h.trans ht.symm

private theorem lifted_delta_constants (v : infPoints G) (U : G.left.Opens)
    (a : Γ(G.left, U)) :
    (liftedTwoParameterTranslation G (Scheme.dualNumbersProjδOver S ≫ v.1)).appLE U U
      (lift_preimage G _ (liftedTwoParameterTranslation_delta_base G v) U)
      (inl (inl a)) = ⟨inl a, inl (invariantCoefficient G v U a)⟩ := by
  let F := liftedTwoParameterTranslation G (Scheme.dualNumbersProjδOver S ≫ v.1)
  have eF := lift_preimage G _ (liftedTwoParameterTranslation_delta_base G v) U
  have h := ConcreteCategory.congr_hom (Scheme.Hom.appLE_comp_appLE F
    (G.left.dualNumbers.dualNumbersProj ≫ G.left.dualNumbersProj) U U U le_rfl eF) a
  have hi := ConcreteCategory.congr_hom (Scheme.Hom.appLE_comp_appLE
    G.left.dualNumbers.dualNumbersProj G.left.dualNumbersProj U U U le_rfl le_rfl) a
  change G.left.dualNumbers.dualNumbersProj.appLE U U _
    (G.left.dualNumbersProj.appLE U U _ a) = _ at hi
  rw [proj_appLE, proj_appLE] at hi
  change F.appLE U U _
    ((G.left.dualNumbers.dualNumbersProj ≫ G.left.dualNumbersProj).appLE U U _ a) = _ at h
  rw [← hi] at h
  have hp := liftedTwoParameterTranslation_delta_proj G v
  change F ≫ _ = _ at hp
  simp only [hp] at h
  have ht := ConcreteCategory.congr_hom (Scheme.Hom.appLE_comp_appLE
    G.left.dualNumbersProj.dualNumbers (infinitesimalRightTranslation G v) U U U
    (infinitesimalRightTranslation_preimage G v U) le_rfl) a
  change G.left.dualNumbersProj.dualNumbers.appLE U U _
    ((infinitesimalRightTranslation G v).appLE U U _ a) = _ at ht
  rw [dual_appLE, translation_appLE] at ht
  have hmap (x : DualNumber Γ(G.left, U)) :
      DualNumber.mapRingHom (G.left.dualNumbersProj.appLE U U le_rfl).hom x =
        ⟨inl x.fst, inl x.snd⟩ := by
    ext <;> simp [proj_appLE]
  rw [hmap] at ht
  exact h.trans ht.symm

omit [GrpObj G] in
private theorem double_map_parameters {R T : Type u} [CommRing R] [CommRing T]
    (f : R →+* T) :
    DualNumber.mapRingHom (DualNumber.mapRingHom f) (inl (inr 1)) = inl (inr 1) ∧
    DualNumber.mapRingHom (DualNumber.mapRingHom f) (inr 1) = inr 1 := by
  constructor <;> ext <;> simp

omit [GrpObj G] in
private theorem double_parameters
    (F : G.left.dualNumbers.dualNumbers ⟶ G.left.dualNumbers.dualNumbers)
    (hk : F ≫ G.hom.dualNumbers.dualNumbers = G.hom.dualNumbers.dualNumbers)
    (_hb : F.base = 𝟙 _) (U : G.left.Opens) (e : U ≤ F ⁻¹ᵁ U) :
    F.appLE U U e
      (inl (inr 1)) = inl (inr 1) ∧
    F.appLE U U e
      (inr 1) = inr 1 := by
  have htop : F.appTop (inl (inr 1)) = inl (inr 1) ∧
      F.appTop (inr 1) = inr 1 := by
    have h := Scheme.Hom.congr_app hk ⊤
    simp only [Scheme.Hom.comp_app, eqToHom_refl, op_id] at h
    erw [G.left.dualNumbers.dualNumbers.presheaf.map_id, Category.comp_id] at h
    have hε := ConcreteCategory.congr_hom h
      (inl (inr 1) : DualNumber (DualNumber Γ(S, ⊤)))
    have hδ := ConcreteCategory.congr_hom h
      (inr 1 : DualNumber (DualNumber Γ(S, ⊤)))
    change F.appTop (DualNumber.mapRingHom (DualNumber.mapRingHom G.hom.appTop.hom)
      (inl (inr 1))) = DualNumber.mapRingHom
        (DualNumber.mapRingHom G.hom.appTop.hom) (inl (inr 1)) at hε
    change F.appTop (DualNumber.mapRingHom (DualNumber.mapRingHom G.hom.appTop.hom)
      (inr 1)) = DualNumber.mapRingHom
        (DualNumber.mapRingHom G.hom.appTop.hom) (inr 1) at hδ
    simpa only [(double_map_parameters G.hom.appTop.hom).1,
      (double_map_parameters G.hom.appTop.hom).2] using And.intro hε hδ
  have h := F.map_appLE e
    (homOfLE le_top : U ⟶ ⊤).op
  have hε := ConcreteCategory.congr_hom h
    (inl (inr 1) : DualNumber (DualNumber Γ(G.left, ⊤)))
  have hδ := ConcreteCategory.congr_hom h
    (inr 1 : DualNumber (DualNumber Γ(G.left, ⊤)))
  change F.appLE U U _ (DualNumber.mapRingHom (DualNumber.mapRingHom
      (G.left.presheaf.map (homOfLE le_top : U ⟶ ⊤).op).hom) (inl (inr 1))) =
    DualNumber.mapRingHom
      (DualNumber.mapRingHom (G.left.presheaf.map (homOfLE le_top : U ⟶ ⊤).op).hom)
      (F.appTop (inl (inr 1))) at hε
  change F.appLE U U _ (DualNumber.mapRingHom (DualNumber.mapRingHom
      (G.left.presheaf.map (homOfLE le_top : U ⟶ ⊤).op).hom) (inr 1)) =
    DualNumber.mapRingHom
      (DualNumber.mapRingHom (G.left.presheaf.map (homOfLE le_top : U ⟶ ⊤).op).hom)
      (F.appTop (inr 1)) at hδ
  simpa only [(double_map_parameters _).1, (double_map_parameters _).2,
    htop.1, htop.2] using And.intro hε hδ

omit [GrpObj G] in
private theorem four_coefficients {R : Type u} [CommRing R]
    (F : DualNumber (DualNumber R) →+* DualNumber (DualNumber R))
    (he : F (inl (inr 1)) = inl (inr 1)) (hd : F (inr 1) = inr 1)
    (x : DualNumber (DualNumber R)) :
    F x = F (inl (inl x.fst.fst)) +
      F (inl (inl x.fst.snd)) * inl (inr 1) +
      F (inl (inl x.snd.fst)) * inr 1 +
      F (inl (inl x.snd.snd)) * inl (inr 1) * inr 1 := by
  have hx : x = inl (inl x.fst.fst) +
      inl (inl x.fst.snd) * inl (inr 1) +
      inl (inl x.snd.fst) * inr 1 +
      inl (inl x.snd.snd) * inl (inr 1) * inr 1 := by
    ext <;> simp
  conv_lhs => rw [hx]
  simp only [map_add, map_mul, he, hd]

omit [GrpObj G] in
private theorem epsilon_formula {R : Type u} [CommRing R]
    (F : DualNumber (DualNumber R) →+* DualNumber (DualNumber R)) (D : AddMonoid.End R)
    (he : F (inl (inr 1)) = inl (inr 1)) (hd : F (inr 1) = inr 1)
    (hc : ∀ a, F (inl (inl a)) = inl ⟨a, D a⟩) (x : DualNumber (DualNumber R)) :
    F x = epsilonSectionAction D x := by
  rw [four_coefficients F he hd, hc, hc, hc, hc]
  ext <;> simp [epsilonSectionAction, add_comm]

omit [GrpObj G] in
private theorem delta_formula {R : Type u} [CommRing R]
    (F : DualNumber (DualNumber R) →+* DualNumber (DualNumber R)) (D : AddMonoid.End R)
    (he : F (inl (inr 1)) = inl (inr 1)) (hd : F (inr 1) = inr 1)
    (hc : ∀ a, F (inl (inl a)) = ⟨inl a, inl (D a)⟩)
    (x : DualNumber (DualNumber R)) : F x = deltaSectionAction D x := by
  rw [four_coefficients F he hd, hc, hc, hc, hc]
  ext <;> simp [deltaSectionAction, add_comm]

private theorem lifted_epsilon_app (v : infPoints G) (U : G.left.Opens)
    (x : DualNumber (DualNumber Γ(G.left, U))) :
    (liftedTwoParameterTranslation G (Scheme.dualNumbersProjεOver S ≫ v.1)).appLE U U
      (lift_preimage G _ (liftedTwoParameterTranslation_epsilon_base G v) U) x =
      epsilonSectionAction (invariantCoefficient G v U) x := by
  have hp := double_parameters G _ (liftedTwoParameterTranslation_over G _)
    (liftedTwoParameterTranslation_epsilon_base G v) U
    (lift_preimage G _ (liftedTwoParameterTranslation_epsilon_base G v) U)
  exact epsilon_formula _ _ hp.1 hp.2 (lifted_epsilon_constants G v U) x

private theorem lifted_delta_app (v : infPoints G) (U : G.left.Opens)
    (x : DualNumber (DualNumber Γ(G.left, U))) :
    (liftedTwoParameterTranslation G (Scheme.dualNumbersProjδOver S ≫ v.1)).appLE U U
      (lift_preimage G _ (liftedTwoParameterTranslation_delta_base G v) U) x =
      deltaSectionAction (invariantCoefficient G v U) x := by
  have hp := double_parameters G _ (liftedTwoParameterTranslation_over G _)
    (liftedTwoParameterTranslation_delta_base G v) U
    (lift_preimage G _ (liftedTwoParameterTranslation_delta_base G v) U)
  exact delta_formula _ _ hp.1 hp.2 (lifted_delta_constants G v U) x

private theorem coefficient_inv (v : infPoints G) :
    invariantCoefficient G v⁻¹ = -invariantCoefficient G v := by
  have h := invariantCoefficient_mul G v v⁻¹
  rw [mul_inv_cancel, (invariantCoefficient_faithful_additive G).2.2] at h
  exact eq_neg_of_add_eq_zero_right h.symm

omit [GrpObj G] in
private theorem appLE_congr {X Y : Scheme.{u}} (f g : X ⟶ Y) (h : f = g)
    (U : Y.Opens) (V : X.Opens) (ef : V ≤ f ⁻¹ᵁ U) (eg : V ≤ g ⁻¹ᵁ U)
    (a : Γ(Y, U)) : f.appLE U V ef a = g.appLE U V eg a := by
  subst g
  rfl

private theorem lifted_translation_eq (z : Scheme.dualNumbers₂Over S ⟶ G) :
    liftedTwoParameterTranslation G z ≫
      G.left.dualNumbers.dualNumbersProj ≫ G.left.dualNumbersProj =
        twoParameterRightTranslation G z := by
  exact liftedTwoParameterTranslation_proj G z

omit [GrpObj G] in
private theorem appLE_comp_same {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (U : Z.Opens) (V : Y.Opens) (W : X.Opens)
    (eg : V ≤ g ⁻¹ᵁ U) (ef : W ≤ f ⁻¹ᵁ V) (e : W ≤ (f ≫ g) ⁻¹ᵁ U)
    (a : Γ(Z, U)) :
    (f ≫ g).appLE U W e a = f.appLE V W ef (g.appLE U V eg a) := by
  exact (ConcreteCategory.congr_hom
    (Scheme.Hom.appLE_comp_appLE f g U V W eg ef) a).symm

private theorem lifted_commutator_base (v w : infPoints G) :
    (liftedTwoParameterTranslation G
      ((Scheme.dualNumbersProjεOver S ≫ v.1) * (Scheme.dualNumbersProjδOver S ≫ w.1) *
        (Scheme.dualNumbersProjεOver S ≫ v.1)⁻¹ *
          (Scheme.dualNumbersProjδOver S ≫ w.1)⁻¹)).base = 𝟙 _ := by
  rw [← GrpObj.comp_inv, ← GrpObj.comp_inv]
  change (liftedTwoParameterTranslation G
    ((Scheme.dualNumbersProjεOver S ≫ v.1) * (Scheme.dualNumbersProjδOver S ≫ w.1) *
      (Scheme.dualNumbersProjεOver S ≫ (v⁻¹).1) *
        (Scheme.dualNumbersProjδOver S ≫ (w⁻¹).1))).base = _
  rw [← liftedTwoParameterTranslation_comp, ← liftedTwoParameterTranslation_comp,
    ← liftedTwoParameterTranslation_comp]
  simp only [Scheme.Hom.comp_base, liftedTwoParameterTranslation_epsilon_base,
    liftedTwoParameterTranslation_delta_base, Category.id_comp]

private theorem lift_mul_base (z t : Scheme.dualNumbers₂Over S ⟶ G)
    (hz : (liftedTwoParameterTranslation G z).base = 𝟙 _)
    (ht : (liftedTwoParameterTranslation G t).base = 𝟙 _) :
    (liftedTwoParameterTranslation G (z * t)).base = 𝟙 _ := by
  rw [← liftedTwoParameterTranslation_comp, Scheme.Hom.comp_base, hz, ht, Category.id_comp]

omit [GrpObj G] in
private theorem section_product {X : Scheme.{u}} (f g k : X ⟶ X) (h : f ≫ g = k)
    (U : X.Opens) (ef : U ≤ f ⁻¹ᵁ U) (eg : U ≤ g ⁻¹ᵁ U) (ek : U ≤ k ⁻¹ᵁ U)
    (x : Γ(X, U)) : k.appLE U U ek x = f.appLE U U ef (g.appLE U U eg x) := by
  subst k
  exact (ConcreteCategory.congr_hom (Scheme.Hom.appLE_comp_appLE f g U U U eg ef) x).symm

private theorem lift_mul_app (z t : Scheme.dualNumbers₂Over S ⟶ G)
    (U : G.left.Opens) (ez : U ≤ liftedTwoParameterTranslation G z ⁻¹ᵁ U)
    (et : U ≤ liftedTwoParameterTranslation G t ⁻¹ᵁ U)
    (ezt : U ≤ liftedTwoParameterTranslation G (z * t) ⁻¹ᵁ U)
    (x : DualNumber (DualNumber Γ(G.left, U))) :
    (liftedTwoParameterTranslation G (z * t)).appLE U U ezt x =
      (liftedTwoParameterTranslation G z).appLE U U ez
        ((liftedTwoParameterTranslation G t).appLE U U et x) := by
  exact section_product (liftedTwoParameterTranslation G z)
    (liftedTwoParameterTranslation G t) (liftedTwoParameterTranslation G (z * t))
    (liftedTwoParameterTranslation_comp G z t) U ez et ezt x

private theorem lift_word_app (v₁ v₂ v₃ v₄ : infPoints G) (U : G.left.Opens)
    (e : U ≤ liftedTwoParameterTranslation G
      ((Scheme.dualNumbersProjεOver S ≫ v₁.1) * (Scheme.dualNumbersProjδOver S ≫ v₂.1) *
        (Scheme.dualNumbersProjεOver S ≫ v₃.1) *
          (Scheme.dualNumbersProjδOver S ≫ v₄.1)) ⁻¹ᵁ U)
    (x : DualNumber (DualNumber Γ(G.left, U))) :
    (liftedTwoParameterTranslation G
      ((Scheme.dualNumbersProjεOver S ≫ v₁.1) * (Scheme.dualNumbersProjδOver S ≫ v₂.1) *
        (Scheme.dualNumbersProjεOver S ≫ v₃.1) *
          (Scheme.dualNumbersProjδOver S ≫ v₄.1))).appLE U U e x =
      epsilonSectionAction (invariantCoefficient G v₁ U)
        (deltaSectionAction (invariantCoefficient G v₂ U)
          (epsilonSectionAction (invariantCoefficient G v₃ U)
            (deltaSectionAction (invariantCoefficient G v₄ U) x))) := by
  let z₁ := Scheme.dualNumbersProjεOver S ≫ v₁.1
  let z₂ := Scheme.dualNumbersProjδOver S ≫ v₂.1
  let z₃ := Scheme.dualNumbersProjεOver S ≫ v₃.1
  let z₄ := Scheme.dualNumbersProjδOver S ≫ v₄.1
  have h₁ := liftedTwoParameterTranslation_epsilon_base G v₁
  have h₂ := liftedTwoParameterTranslation_delta_base G v₂
  have h₃ := liftedTwoParameterTranslation_epsilon_base G v₃
  have h₄ := liftedTwoParameterTranslation_delta_base G v₄
  have e₁ := lift_preimage G z₁ h₁ U
  have e₂ := lift_preimage G z₂ h₂ U
  have e₃ := lift_preimage G z₃ h₃ U
  have e₄ := lift_preimage G z₄ h₄ U
  have h₁₂ := lift_mul_base G z₁ z₂ h₁ h₂
  have e₁₂ := lift_preimage G (z₁ * z₂) h₁₂ U
  have e₁₂₃ := lift_preimage G ((z₁ * z₂) * z₃) (lift_mul_base G _ z₃ h₁₂ h₃) U
  change (liftedTwoParameterTranslation G (((z₁ * z₂) * z₃) * z₄)).appLE U U e x = _
  simp only [lift_mul_app G _ z₄ U e₁₂₃ e₄ e,
    lift_mul_app G _ z₃ U e₁₂ e₃ e₁₂₃,
    lift_mul_app G z₁ z₂ U e₁ e₂ e₁₂]
  dsimp only [z₁, z₂, z₃, z₄]
  simp only [lifted_epsilon_app, lifted_delta_app]

/-- The section map of the right-translation commutator is the composition of its four
coefficientwise square-zero operators, before extracting any mixed coefficient.

Source: the invariant-extension and mixed-coefficient steps of the Lie-ring paragraph in
`WeilConjectures/AlgebraicGeometry/GroupScheme/Lie/Bracket.lean`.
(blueprint: lem-ag-two-parameter-translation-action)

Proof: Base change right translation by v from S[ε] to S[ε][δ], keeping δ fixed.
On each open its comorphism is 1+εD_v. Indeed reduction along ε=0 is the identity,
the ε coefficient on constants is the defining invariantCoefficient, and compatibility
with the projection to S[ε][δ] fixes both parameters. The same argument for w fixes ε
and gives 1+δD_w. These descriptions act coefficientwise on all four components of
Γ(U,𝒪_G)[ε][δ]. The inverse translations have the inverse operators 1-εD_v and
1-δD_w: multiplication cancels the linear terms and the quadratic terms vanish.
Right translation by the product v_ε w_δ v_ε⁻¹ w_δ⁻¹ is the successive composition
of these four translations. Contravariance gives the displayed order on functions,
namely the operator for v_ε outermost. Apply these operators to the constant section
a. Since all translations reduce to the identity, their underlying maps are identity
maps of G; appLE therefore evaluates them on the same open U, independently of its
proof argument e. This proves the equality without extracting the mixed coefficient.
The argument is sheafwise, works on an empty scheme, and uses only square-zero
identities, with no division or smoothness hypothesis. -/
theorem twoParameterRightTranslation_commutator_app
    (v w : infPoints G) (U : G.left.Opens)
    (e : U ≤ (twoParameterRightTranslation G
      ((Scheme.dualNumbersProjεOver S ≫ v.1) * (Scheme.dualNumbersProjδOver S ≫ w.1) *
        (Scheme.dualNumbersProjεOver S ≫ v.1)⁻¹ *
          (Scheme.dualNumbersProjδOver S ≫ w.1)⁻¹)) ⁻¹ᵁ U)
    (a : Γ(G.left, U)) :
    (twoParameterRightTranslation G
      ((Scheme.dualNumbersProjεOver S ≫ v.1) * (Scheme.dualNumbersProjδOver S ≫ w.1) *
        (Scheme.dualNumbersProjεOver S ≫ v.1)⁻¹ *
          (Scheme.dualNumbersProjδOver S ≫ w.1)⁻¹)).appLE U U e a =
      epsilonSectionAction (invariantCoefficient G v U)
        (deltaSectionAction (invariantCoefficient G w U)
          (epsilonSectionAction (-invariantCoefficient G v U)
            (deltaSectionAction (-invariantCoefficient G w U) (inl (inl a))))) := by
  let z := (Scheme.dualNumbersProjεOver S ≫ v.1) *
    (Scheme.dualNumbersProjδOver S ≫ w.1) *
      (Scheme.dualNumbersProjεOver S ≫ v.1)⁻¹ *
        (Scheme.dualNumbersProjδOver S ≫ w.1)⁻¹
  let z' := (Scheme.dualNumbersProjεOver S ≫ v.1) *
    (Scheme.dualNumbersProjδOver S ≫ w.1) *
      (Scheme.dualNumbersProjεOver S ≫ (v⁻¹).1) *
        (Scheme.dualNumbersProjδOver S ≫ (w⁻¹).1)
  have hz : z = z' := by
    dsimp only [z, z']
    rw [← GrpObj.comp_inv, ← GrpObj.comp_inv]
    rfl
  have hb : (liftedTwoParameterTranslation G z').base = 𝟙 _ := by
    rw [← hz]
    exact lifted_commutator_base G v w
  have ec := lift_preimage G z' hb U
  let P := G.left.dualNumbers.dualNumbersProj ≫ G.left.dualNumbersProj
  have hg : liftedTwoParameterTranslation G z' ≫ P =
      twoParameterRightTranslation G z :=
    (lifted_translation_eq G z').trans (congrArg (twoParameterRightTranslation G) hz.symm)
  have ef : U ≤ (liftedTwoParameterTranslation G z' ≫ P) ⁻¹ᵁ U := by
    rw [hg]
    exact e
  have h₁ := appLE_congr (twoParameterRightTranslation G z)
    (liftedTwoParameterTranslation G z' ≫ P) hg.symm U U e ef a
  have h₂ := appLE_comp_same (liftedTwoParameterTranslation G z') P U U U le_rfl ec ef a
  have hi := ConcreteCategory.congr_hom (Scheme.Hom.appLE_comp_appLE
    G.left.dualNumbers.dualNumbersProj G.left.dualNumbersProj U U U le_rfl le_rfl) a
  change G.left.dualNumbers.dualNumbersProj.appLE U U _
    (G.left.dualNumbersProj.appLE U U _ a) = P.appLE U U _ a at hi
  rw [proj_appLE, proj_appLE] at hi
  rw [← hi] at h₂
  have hc := lift_word_app G v w v⁻¹ w⁻¹ U ec (inl (inl a))
  simp only [coefficient_inv] at hc
  exact h₁.trans (h₂.trans hc)

end AlgebraicGeometry.GrpObj
