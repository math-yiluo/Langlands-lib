/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ArtinSchreierTrace.SplitCondensedRegularProduct
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.UnitCoherence
public import WeilConjectures.AlgebraicGeometry.ArtinSchreierTrace.ArtinSchreierTraceComparison
public import WeilConjectures.AlgebraicGeometry.ArtinSchreierUnit.ArtinSchreierSplitProjector
public import WeilConjectures.CategoryTheory.ModuleObjects.Linear
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.MonoidalModule

/-! # Coefficient maps and root restriction on finite covers -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ArtinSchreierTrace

attribute [local implicit_reducible] condensedUnit
attribute [local implicit_reducible] CommMon.toMon
  GrothendieckTopology.monoidalCategory_sheaf_of_essentiallySmall
  GrothendieckTopology.braidedCategory_sheaf_of_essentiallySmall
  GrothendieckTopology.symmetricCategory_sheaf_of_essentiallySmall
  ProEtale.sheafMonoidalCategory ProEtale.sheafBraidedCategory
  ProEtale.sheafSymmetricCategory Mod.monoidalCategory Mod.monoidalCategoryStruct Monoidal.induced

attribute [local irreducible] ProEtale.CondensedRing.upperStar
  ProEtale.CondensedRing.upperStarComp
  ProEtale.CondensedRing.lowerStarComp
  ProEtale.CondensedRing.upperStarLowerStarAdjunction
  ProEtale.CondensedRing.monoidal_upperStar
  Mod.monoidal_extendScalars Functor.monoidal_mapMod

private theorem evaluation_conjugate
    {A B C : Type*} [Category A] [Category B] [Category C]
    {L : A ⥤ B} {R : B ⥤ A} (adj : L ⊣ R)
    {L' : B ⥤ C} {R' : C ⥤ B} (adj' : L' ⊣ R')
    {Lx : A ⥤ C} {Rx : C ⥤ A} (adjx : Lx ⊣ Rx)
    (α : Lx ⟶ L ⋙ L') (M : B) (N : C) (v : L'.obj M ⟶ N) :
    adjx.homEquiv (R.obj M) N
        (α.app (R.obj M) ≫ L'.map (adj.counit.app M) ≫ v) =
      R.map (adj'.homEquiv M N v) ≫ (conjugateEquiv (adj.comp adj') adjx α).app N := by
  have h := homEquiv_comp_conjugateEquiv_app (adj.comp adj') adjx α
    (L'.map (adj.counit.app M) ≫ v)
  have hε : adj.homEquiv (R.obj M) M (adj.counit.app M) = 𝟙 _ := by
    rw [← adj.homEquiv_symm_id M]
    exact (adj.homEquiv _ _).apply_symm_apply _
  rw [Adjunction.comp_homEquiv] at h
  change adj.homEquiv (R.obj M) (R'.obj N)
      (adj'.homEquiv (L.obj (R.obj M)) N (L'.map (adj.counit.app M) ≫ v)) ≫
        (conjugateEquiv (adj.comp adj') adjx α).app N = _ at h
  rw [Adjunction.homEquiv_naturality_left,
    Adjunction.homEquiv_naturality_right] at h
  simp only [Functor.id_obj] at h
  rw [hε, Category.id_comp] at h
  exact h.symm

private theorem evaluate_adjoint
    {A B : Type*} [Category A] [Category B]
    {L : A ⥤ B} {R : B ⥤ A} (adj : L ⊣ R)
    (M : A) (N : B) (v : L.obj M ⟶ N) :
    L.map (adj.homEquiv M N v) ≫ adj.counit.app N = v := by
  calc
    _ = (adj.homEquiv M N).symm (adj.homEquiv M N v) :=
      (adj.homEquiv_counit (g := adj.homEquiv M N v)).symm
    _ = v := (adj.homEquiv M N).symm_apply_apply v

private theorem evaluate_homEquiv
    {A B : Type*} [Category A] [Category B]
    {L : A ⥤ B} {R : B ⥤ A} (adj : L ⊣ R)
    (M : A) (N : B) (v : M ⟶ R.obj N) :
    adj.homEquiv M N (L.map v ≫ adj.counit.app N) = v := by
  rw [← adj.homEquiv_counit]
  exact (adj.homEquiv M N).apply_symm_apply v

private theorem evaluation_mate
    {A B C : Type*} [Category A] [Category B] [Category C]
    {L : A ⥤ B} {R : B ⥤ A} (adj : L ⊣ R)
    {L' : B ⥤ C} {R' : C ⥤ B} (adj' : L' ⊣ R')
    {Lx : A ⥤ C} {Rx : C ⥤ A} (adjx : Lx ⊣ Rx)
    (α : Lx ⟶ L ⋙ L') (M : B) (N : C) (v : L'.obj M ⟶ N) :
    Lx.map (R.map (adj'.homEquiv M N v) ≫
        (conjugateEquiv (adj.comp adj') adjx α).app N) ≫ adjx.counit.app N =
      α.app (R.obj M) ≫ L'.map (adj.counit.app M) ≫ v := by
  apply (adjx.homEquiv (R.obj M) N).injective
  rw [evaluate_homEquiv]
  exact (evaluation_conjugate adj adj' adjx α M N v).symm

private theorem evaluation_mate_iso
    {A B C : Type*} [Category A] [Category B] [Category C]
    {L : A ⥤ B} {R : B ⥤ A} (adj : L ⊣ R)
    {L' : B ⥤ C} {R' : C ⥤ B} (adj' : L' ⊣ R')
    {Lx : A ⥤ C} {Rx : C ⥤ A} (adjx : Lx ⊣ Rx)
    (α : Lx ≅ L ⋙ L') (β : R' ⋙ R ≅ Rx)
    (hβ : conjugateIsoEquiv (adj.comp adj') adjx α = β)
    (M : B) (N : C) (v : L'.obj M ⟶ N) (u : M ⟶ R'.obj N)
    (hu : adj'.homEquiv M N v = u) :
    Lx.map (R.map u ≫ β.hom.app N) ≫ adjx.counit.app N =
      α.hom.app (R.obj M) ≫ L'.map (adj.counit.app M) ≫ v := by
  have h := evaluation_mate adj adj' adjx α.hom M N v
  rw [← conjugateIsoEquiv_apply_hom, hβ, hu] at h
  exact h

/-- The coefficient pullback map is the adjoint of the monoidal unit comparison.
Source: the coefficient adjunction, as used in blueprint lemma-artin-schreier-character-sheaf
(blueprint: lem-fd-as-coefficient-cover-maps).

Proof: the underlying morphism of the adjoint is condensedPushforwardHom by
homEquiv_εIso_inv_hom. Maps from the regular module are determined by the image
of its unit, and regularLift sends that unit to the specified coefficient unit. -/
theorem coefficientUnit_eq_adjoint
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X Y : Scheme.{u}} (f : Y ⟶ X) :
    Mod.regularLift
        ((ProEtale.CondensedRing.lowerStar Λ f).obj (condensedUnit Λ Y))
        (MonObj.one ≫ ProEtale.condensedPushforwardHom Λ f) =
      (ProEtale.CondensedRing.upperStarLowerStarAdjunction Λ f).homEquiv
        (condensedUnit Λ X) (condensedUnit Λ Y)
        (regularUnitIso Λ f).inv := by
  apply Mod.regular_hom_ext
  rw [Mod.one_comp_regularLift]
  unfold regularUnitIso
  erw [ProEtale.CondensedRing.homEquiv_εIso_inv_hom]

private def coefficientUnit
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X Y : Scheme.{u}} (f : Y ⟶ X) :
    condensedUnit Λ X ⟶
      (ProEtale.CondensedRing.lowerStar Λ f).obj (condensedUnit Λ Y) :=
  (ProEtale.CondensedRing.upperStarLowerStarAdjunction Λ f).homEquiv
    (condensedUnit Λ X) (condensedUnit Λ Y)
    (regularUnitIso Λ f).inv

private theorem regularLift_eq_coefficientUnit
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X Y : Scheme.{u}} (f : Y ⟶ X) :
    Mod.regularLift
        ((ProEtale.CondensedRing.lowerStar Λ f).obj (condensedUnit Λ Y))
        (MonObj.one ≫ ProEtale.condensedPushforwardHom Λ f) = coefficientUnit Λ f :=
  coefficientUnit_eq_adjoint Λ f

private theorem coefficientUnit_hom
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X Y : Scheme.{u}} (f : Y ⟶ X) :
    (coefficientUnit Λ f).hom = ProEtale.condensedPushforwardHom Λ f := by
  unfold coefficientUnit regularUnitIso
  exact ProEtale.CondensedRing.homEquiv_εIso_inv_hom Λ f

private theorem coefficientUnit_comp
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    coefficientUnit Λ (f ≫ g) = coefficientUnit Λ g ≫
      (ProEtale.CondensedRing.lowerStar Λ g).map (coefficientUnit Λ f) ≫
        (ProEtale.CondensedRing.lowerStarComp Λ f g).hom.app (condensedUnit Λ X) := by
  apply Mod.hom_ext
  simp only [Mod.comp_hom', ProEtale.CondensedRing.lowerStar_map_hom,
    ProEtale.CondensedRing.lowerStarComp_hom_app_hom, coefficientUnit_hom]
  exact ProEtale.condensedPushforwardHom_comp Λ f g

private theorem coefficientUnit_congr
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X Y : Scheme.{u}} {f g : Y ⟶ X} (h : f = g) :
    coefficientUnit Λ f ≫ (ProEtale.CondensedRing.lowerStarCongr Λ h).hom.app
      (condensedUnit Λ Y) = coefficientUnit Λ g := by
  subst h
  simp only [ProEtale.CondensedRing.lowerStarCongr, eqToIso_refl, Iso.refl_hom,
    NatTrans.id_app, Category.comp_id]

private def coefficientPull
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (ProEtale.CondensedRing.lowerStar Λ g).obj (condensedUnit Λ Y) ⟶
      (ProEtale.CondensedRing.lowerStar Λ (f ≫ g)).obj (condensedUnit Λ X) :=
  (ProEtale.CondensedRing.lowerStar Λ g).map (coefficientUnit Λ f) ≫
    (ProEtale.CondensedRing.lowerStarComp Λ f g).hom.app (condensedUnit Λ X)

private theorem coefficientPull_comp
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {W X Y Z : Scheme.{u}}
    (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z) :
    coefficientPull Λ g h ≫ coefficientPull Λ f (g ≫ h) =
      coefficientPull Λ (f ≫ g) h ≫
        (ProEtale.CondensedRing.lowerStarCongr Λ (Category.assoc f g h)).hom.app
          (condensedUnit Λ W) := by
  have hc := congrArg (fun e ↦ e.hom.app (condensedUnit Λ W))
    (ProEtale.CondensedRing.lowerStarComp_assoc Λ f g h)
  simp only [Iso.trans_hom, NatTrans.comp_app, Functor.associator_hom_app,
    Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app,
    Functor.isoWhiskerRight_hom, Functor.whiskerRight_app,
    Category.id_comp] at hc
  unfold coefficientPull
  rw [coefficientUnit_comp, Functor.map_comp, Functor.map_comp]
  simp only [Category.assoc]
  rw [← hc]
  have hn := (ProEtale.CondensedRing.lowerStarComp Λ g h).hom.naturality
    (coefficientUnit Λ f)
  simp only [Functor.comp_map] at hn
  rw [← reassoc_of% hn]

@[reassoc]
private theorem lowerStarCongr_trans
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X Y : Scheme.{u}} {f g h : X ⟶ Y}
    (e : f = g) (e' : g = h)
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (ProEtale.condensedRingObj Λ X)) :
    (ProEtale.CondensedRing.lowerStarCongr Λ e).hom.app M ≫
        (ProEtale.CondensedRing.lowerStarCongr Λ e').hom.app M =
      (ProEtale.CondensedRing.lowerStarCongr Λ (e.trans e')).hom.app M := by
  subst g
  subst h
  simp [ProEtale.CondensedRing.lowerStarCongr]

private theorem coefficientPull_congr
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X Y Z : Scheme.{u}}
    (f : X ⟶ Y) {g h : Y ⟶ Z} (e : g = h) :
    (ProEtale.CondensedRing.lowerStarCongr Λ e).hom.app (condensedUnit Λ Y) ≫
        coefficientPull Λ f h =
      coefficientPull Λ f g ≫
        (ProEtale.CondensedRing.lowerStarCongr Λ
          (congrArg (fun k ↦ f ≫ k) e)).hom.app (condensedUnit Λ X) := by
  subst h
  simp [ProEtale.CondensedRing.lowerStarCongr]

private theorem condensedPull_eq_coefficientPull
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X : Scheme.{u}} {Y Z : Over X} (f : Y ⟶ Z) :
    condensedPull Λ f = coefficientPull Λ f.left Z.hom ≫
      (ProEtale.CondensedRing.lowerStarCongr Λ (Over.w f)).hom.app
        (condensedUnit Λ Y.left) := by
  simp only [condensedPull, coefficientPull, coefficientUnit,
    coefficientUnit_eq_adjoint, Category.assoc]

/-- Coefficient functions form a contravariant functor on the category of covers.
Source: latest blueprint, lem-wft-as-unit-trivialization.proof.md, restriction of
coefficient functions (blueprint: lem-wft-as-coefficient-pull-calculus). -/
theorem condensedPull_comp
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X : Scheme.{u}} {W Y Z : Over X}
    (j : W ⟶ Y) (h : Y ⟶ Z) :
    condensedPull Λ (j ≫ h) = condensedPull Λ h ≫ condensedPull Λ j := by
  simp only [condensedPull_eq_coefficientPull, Category.assoc]
  rw [reassoc_of% coefficientPull_congr Λ j.left (Over.w h),
    reassoc_of% coefficientPull_comp Λ j.left h.left Z.hom, lowerStarCongr_trans_assoc,
    lowerStarCongr_trans]
  rfl

private theorem coefficientUnit_pull
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X : Scheme.{u}} {Y Z : Over X} (f : Y ⟶ Z) :
    coefficientUnit Λ Z.hom ≫ condensedPull Λ f = coefficientUnit Λ Y.hom := by
  rw [condensedPull, coefficientUnit_eq_adjoint]
  change coefficientUnit Λ Z.hom ≫
    (ProEtale.CondensedRing.lowerStar Λ Z.hom).map (coefficientUnit Λ f.left) ≫
    (ProEtale.CondensedRing.lowerStarComp Λ f.left Z.hom).hom.app _ ≫
    (ProEtale.CondensedRing.lowerStarCongr Λ (Over.w f)).hom.app _ = _
  calc
    _ = coefficientUnit Λ (f.left ≫ Z.hom) ≫
        (ProEtale.CondensedRing.lowerStarCongr Λ (Over.w f)).hom.app
          (condensedUnit Λ Y.left) := by
      rw [coefficientUnit_comp]
      simp only [Category.assoc]
    _ = _ := coefficientUnit_congr Λ (Over.w f)

/-- The pullback of a constant coefficient function has that constant value at
any chosen root.
Source: blueprint lemma-artin-schreier-character-sheaf, trivial-character clause
(blueprint: lem-fd-as-coefficient-cover-maps).

Proof: composing the coefficient unit with pullback of functions is the
coefficient unit of the composite. Adjunction identifies its evaluation with
the inverse monoidal unit comparison. -/
theorem condensedEvaluation_coefficientUnit
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X T : Scheme.{u}}
    (Y : Over X) (x : T ⟶ X) (s : Over.mk x ⟶ Y) :
    condensedEvaluation Λ x s (M := condensedUnit Λ X)
      (Mod.regularLift
        ((ProEtale.CondensedRing.lowerStar Λ Y.hom).obj (condensedUnit Λ Y.left))
        (MonObj.one ≫ ProEtale.condensedPushforwardHom Λ Y.hom)) =
    (regularUnitIso Λ x).inv := by
  unfold condensedEvaluation
  let F := ProEtale.CondensedRing.upperStar Λ x
  let ε := (ProEtale.CondensedRing.upperStarLowerStarAdjunction Λ x).counit.app
    (condensedUnit Λ T)
  have hu := regularLift_eq_coefficientUnit Λ Y.hom
  have hp := coefficientUnit_pull Λ s
  calc
    _ = F.map (coefficientUnit Λ Y.hom ≫ condensedPull Λ s) ≫ ε :=
      congrArg (fun v ↦ F.map (v ≫ condensedPull Λ s) ≫ ε) hu
    _ = F.map (coefficientUnit Λ x) ≫ ε :=
      congrArg (fun v ↦ F.map v ≫ ε) hp
    _ = _ := evaluate_adjoint
      (ProEtale.CondensedRing.upperStarLowerStarAdjunction Λ x)
      (condensedUnit Λ X) (condensedUnit Λ T) (regularUnitIso Λ x).inv

private theorem coefficientEvaluation_eq_sheetProjection
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X Y T : Scheme.{u}}
    (π : Y ⟶ X) (t : T ⟶ Y) (x : T ⟶ X) (w : t ≫ π = x) :
    (ProEtale.CondensedRing.upperStar Λ x).map
        ((ProEtale.CondensedRing.lowerStar Λ π).map (coefficientUnit Λ t) ≫
          (ProEtale.CondensedRing.lowerStarComp Λ t π).hom.app (condensedUnit Λ T) ≫
          (ProEtale.CondensedRing.lowerStarCongr Λ w).hom.app (condensedUnit Λ T)) ≫
        (ProEtale.CondensedRing.upperStarLowerStarAdjunction Λ x).counit.app
          (condensedUnit Λ T) =
      ProEtale.CondensedRing.stalkLowerStarProj Λ w (condensedUnit Λ Y) ≫
        (regularUnitIso Λ t).inv := by
  rw [ProEtale.CondensedRing.stalkLowerStarProj_eq]
  let adj := ProEtale.CondensedRing.upperStarLowerStarAdjunction Λ π
  let adjs := ProEtale.CondensedRing.upperStarLowerStarAdjunction Λ
    (X := T) (Y := Y) t
  let adjx := ProEtale.CondensedRing.upperStarLowerStarAdjunction Λ x
  let α := ProEtale.CondensedRing.upperStarCongr Λ w.symm ≪≫
    ProEtale.CondensedRing.upperStarComp Λ t π
  have hα : conjugateIsoEquiv (adj.comp adjs) adjx α =
      ProEtale.CondensedRing.lowerStarComp Λ t π ≪≫
        ProEtale.CondensedRing.lowerStarCongr Λ w := by
    rw [conjugateIsoEquiv_trans _
      (ProEtale.CondensedRing.upperStarLowerStarAdjunction Λ (t ≫ π))]
    rw [ProEtale.CondensedRing.conjugateIsoEquiv_upperStarComp,
      ProEtale.CondensedRing.conjugateIsoEquiv_upperStarCongr,
      ProEtale.CondensedRing.lowerStarCongr_symm]
  have h := evaluation_mate_iso adj adjs adjx α
    (ProEtale.CondensedRing.lowerStarComp Λ t π ≪≫
      ProEtale.CondensedRing.lowerStarCongr Λ w) hα
    (condensedUnit Λ Y) (condensedUnit Λ T)
    (regularUnitIso Λ (X := T) (Y := Y) t).inv (coefficientUnit Λ t) rfl
  dsimp only [adj, adjs, adjx] at h
  simpa only [α, Iso.trans_hom, NatTrans.comp_app, Category.assoc] using h

/-- Root evaluation equals the composition-comparison projection followed by the
monoidal identification of the pulled-back regular module.
Source: blueprint lemma-artin-schreier-character-sheaf, root-evaluation convention
(blueprint: lem-fd-as-coefficient-cover-maps).

Proof: apply the pullback/pushforward adjunction for x to both maps. Conjugacy of
the composition comparison with lowerStarComp identifies the second adjoint with
lowerStar.map of the adjoint coefficient unit on s, followed by lowerStarComp and
the equality transport. coefficientUnit_eq_adjoint identifies this with the
explicit condensedPull definition. The other side is that same map by the
adjunction triangle identity. -/
theorem condensedEvaluation_id_eq_sheetProjection
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X T : Scheme.{u}}
    (Y : Over X) (x : T ⟶ X) (s : Over.mk x ⟶ Y) :
    condensedEvaluation Λ x s (𝟙 _) =
      sheetProjection Λ Y.hom x s.left (Over.w s) := by
  unfold condensedEvaluation sheetProjection
  simp only [Category.id_comp]
  rw [condensedPull_eq_coefficientPull]
  unfold coefficientPull
  simp only [Category.assoc]
  exact coefficientEvaluation_eq_sheetProjection Λ (T := T) Y.hom s.left x (Over.w s)

end AlgebraicGeometry.ArtinSchreierTrace
