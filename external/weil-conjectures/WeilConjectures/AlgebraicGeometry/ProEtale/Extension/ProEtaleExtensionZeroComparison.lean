/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LowerShriekComparison
public import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Comp
public import Mathlib.CategoryTheory.Adjunction.CompositionIso
import WeilConjectures.SixFunctors.Etale.Derived.HeartGluing
import WeilConjectures.CategoryTheory.AdjunctionSquareComposition
import WeilConjectures.Mathlib.CategoryTheory.Adjunction.Unique

/-!
# Comparison of extension by zero on the etale and pro-etale sites

The comparison is the existing adjunction mate
`openImmersionLowerShriekComparisonUpperStarIso`, not a chosen isomorphism.

## References

* Stacks Project, Tags 09AE and 03EH
* Stacks Project, Tag 09AF
-/

@[expose] public section

universe u' u

open CategoryTheory CategoryTheory.Functor

namespace CategoryTheory

-- Transport adjunctions along the specified restriction isomorphisms.
private lemma conj_transport {C D : Type*} [Category* C] [Category* D]
    {L₁ L₂ : C ⥤ D} {R₁ R₂ R₁' R₂' : D ⥤ C}
    (a : L₁ ⊣ R₁) (b : L₂ ⊣ R₂) (e : R₁ ≅ R₁') (f : R₂ ≅ R₂')
    (α : L₂ ⟶ L₁) :
    conjugateEquiv (a.ofNatIsoRight e) (b.ofNatIsoRight f) α =
      e.inv ≫ conjugateEquiv a b α ≫ f.hom := by
  ext X
  simp only [conjugateEquiv_apply_app, Adjunction.ofNatIsoRight_unit,
    Adjunction.ofNatIsoRight_counit, NatTrans.comp_app, whiskerLeft_app,
    whiskerRight_app, Functor.map_comp, Category.assoc]
  rw [← f.hom.naturality_assoc, ← f.hom.naturality_assoc, ← f.hom.naturality]
  rw [← R₂.map_comp_assoc, ← α.naturality, R₂.map_comp_assoc]
  rw [← b.unit_naturality_assoc]

private lemma comp_transport {C D E : Type*} [Category* C] [Category* D] [Category* E]
    {L : C ⥤ D} {R R' : D ⥤ C} {M : D ⥤ E} {S S' : E ⥤ D}
    (a : L ⊣ R) (b : M ⊣ S) (e : R ≅ R') (f : S ≅ S') :
    (a.ofNatIsoRight e).comp (b.ofNatIsoRight f) =
      (a.comp b).ofNatIsoRight
        (isoWhiskerLeft S e ≪≫ isoWhiskerRight f R') := by
  apply Adjunction.ext
  ext X
  simp only [Adjunction.comp_unit_app, Adjunction.ofNatIsoRight_unit,
    NatTrans.comp_app, whiskerLeft_app, whiskerRight_app, Iso.trans_hom,
    isoWhiskerLeft_hom, isoWhiskerRight_hom, Functor.comp_obj,
    Functor.map_comp, Category.assoc]
  rw [← e.hom.naturality_assoc]

private lemma transport_refl {C D : Type*} [Category* C] [Category* D]
    {L : C ⥤ D} {R : D ⥤ C} (a : L ⊣ R) :
    a.ofNatIsoRight (Iso.refl R) = a := by
  apply Adjunction.ext
  ext X
  simp [Adjunction.ofNatIsoRight_unit]

private lemma conj_uniq_transport {C D : Type*} [Category* C] [Category* D]
    {L M : C ⥤ D} {R S : D ⥤ C} (a : L ⊣ R) (b : M ⊣ S) (e : S ≅ R) :
    conjugateIsoEquiv b a (a.leftAdjointUniq (b.ofNatIsoRight e)) = e := by
  apply Iso.ext
  apply NatTrans.ext
  funext X
  have h := conj_transport b a e (Iso.refl R)
    (a.leftAdjointUniq (b.ofNatIsoRight e)).hom
  simp only [transport_refl, conjugateEquiv_leftAdjointUniq_hom, Iso.refl_hom,
    Category.comp_id] at h
  rw [← cancel_epi (e.inv.app X)]
  simpa using (congr_app h X).symm

private lemma conjIso_transport {C D : Type*} [Category* C] [Category* D]
    {L₁ L₂ : C ⥤ D} {R₁ R₂ R₁' R₂' : D ⥤ C}
    (a : L₁ ⊣ R₁) (b : L₂ ⊣ R₂) (e : R₁ ≅ R₁') (f : R₂ ≅ R₂')
    (α : L₂ ≅ L₁) :
    conjugateIsoEquiv (a.ofNatIsoRight e) (b.ofNatIsoRight f) α =
      e.symm ≪≫ conjugateIsoEquiv a b α ≪≫ f := by
  exact Iso.ext (conj_transport a b e f α.hom)

private lemma comp_conjugate
    {C D E : Type*} [Category* C] [Category* D] [Category* E]
    {F₀₁ : C ⥤ D} {F₁₂ : D ⥤ E} {F₀₂ : C ⥤ E}
    {R₁₀ U₁₀ : D ⥤ C} {R₂₁ U₂₁ : E ⥤ D} {R₂₀ U₂₀ : E ⥤ C}
    (a : F₀₁ ⊣ R₁₀) (b : F₁₂ ⊣ R₂₁) (c : F₀₂ ⊣ R₂₀)
    (e : R₁₀ ≅ U₁₀) (f : R₂₁ ≅ U₂₁) (g : R₂₀ ≅ U₂₀)
    (φ : U₂₀ ≅ U₂₁ ⋙ U₁₀) (ρ : R₂₀ ≅ R₂₁ ⋙ R₁₀)
    (he : ρ ≪≫ isoWhiskerLeft R₂₁ e ≪≫ isoWhiskerRight f U₁₀ = g ≪≫ φ) :
    conjugateIsoEquiv (a.comp b) c
      ((c.ofNatIsoRight g).leftAdjointUniq
        (((a.ofNatIsoRight e).comp (b.ofNatIsoRight f)).ofNatIsoRight φ.symm)) =
      ρ.symm := by
  let ei := isoWhiskerLeft R₂₁ e ≪≫ isoWhiskerRight f U₁₀
  let θ := (c.ofNatIsoRight g).leftAdjointUniq
    (((a.ofNatIsoRight e).comp (b.ofNatIsoRight f)).ofNatIsoRight φ.symm)
  have h := conj_uniq_transport (c.ofNatIsoRight g)
    ((a.ofNatIsoRight e).comp (b.ofNatIsoRight f)) φ.symm
  change conjugateIsoEquiv ((a.ofNatIsoRight e).comp (b.ofNatIsoRight f))
    (c.ofNatIsoRight g) θ = φ.symm at h
  rw [comp_transport, conjIso_transport] at h
  change ei.symm ≪≫ conjugateIsoEquiv (a.comp b) c θ ≪≫ g = φ.symm at h
  have hh : ei ≪≫ φ.symm ≪≫ g.symm = ρ.symm := by
    have h' := congrArg Iso.symm he
    simpa [ei, Iso.trans_symm, Iso.trans_assoc] using
      congrArg (fun z ↦ ei ≪≫ z) h'.symm
  calc
    conjugateIsoEquiv (a.comp b) c θ =
        ei ≪≫ (ei.symm ≪≫ conjugateIsoEquiv (a.comp b) c θ ≪≫ g) ≪≫ g.symm := by
      simp
    _ = ei ≪≫ φ.symm ≪≫ g.symm := by rw [h]
    _ = ρ.symm := hh

private lemma id_conjugate
    {C : Type*} [Category* C]
    {L : C ⥤ C} {R S : C ⥤ C}
    (a : L ⊣ R) (e : R ≅ S) (f : S ≅ 𝟭 C) :
    conjugateIsoEquiv Adjunction.id a
      (Adjunction.leftAdjointIdIso (a.ofNatIsoRight e) f) = (e ≪≫ f).symm := by
  have h := conjIso_transport Adjunction.id a (Iso.refl _) e
    (Adjunction.leftAdjointIdIso (a.ofNatIsoRight e) f)
  have h' : conjugateIsoEquiv Adjunction.id (a.ofNatIsoRight e)
      (Adjunction.leftAdjointIdIso (a.ofNatIsoRight e) f) = f.symm :=
    Equiv.apply_symm_apply _ _
  rw [transport_refl, h'] at h
  have hh := congrArg (fun z ↦ z ≪≫ e.symm) h
  simpa [Iso.trans_symm, Iso.trans_assoc] using hh.symm

private lemma identity_square
    {C D : Type*} [Category* C] [Category* D]
    {L : C ⥤ D} {R : D ⥤ C} {E : C ⥤ C} {S : C ⥤ C}
    {P : D ⥤ D} {T : D ⥤ D}
    (a : L ⊣ R) (b : E ⊣ S) (c : P ⊣ T)
    (θ : E ⋙ L ≅ L ⋙ P) (e : E ≅ 𝟭 C) (p : P ≅ 𝟭 D)
    (β : R ⋙ S ≅ T ⋙ R) (s : S ≅ 𝟭 C) (t : T ≅ 𝟭 D)
    (hθ : conjugateIsoEquiv (b.comp a) (a.comp c) θ.symm = β)
    (he : conjugateIsoEquiv Adjunction.id b e = s.symm)
    (hp : conjugateIsoEquiv Adjunction.id c p = t.symm)
    (hr : R.leftUnitor.symm ≪≫ isoWhiskerRight t.symm R ≪≫ β.symm =
      R.rightUnitor.symm ≪≫ isoWhiskerLeft R s.symm) :
    θ ≪≫ isoWhiskerLeft L p ≪≫ L.rightUnitor =
      isoWhiskerRight e L ≪≫ L.leftUnitor := by
  apply (conjugateIsoEquiv a (b.comp a)).injective
  conv_lhs =>
    rw [← Iso.trans_assoc,
      conjugateIsoEquiv_trans a (a.comp Adjunction.id) (b.comp a)
        L.rightUnitor (θ ≪≫ isoWhiskerLeft L p),
      conjugateIsoEquiv_rightUnitor,
      conjugateIsoEquiv_trans (a.comp Adjunction.id) (a.comp c) (b.comp a)
        (isoWhiskerLeft L p) θ,
      conjugateIsoEquiv_isoWhiskerLeft, hp]
  conv_rhs =>
    rw [conjugateIsoEquiv_trans a (Adjunction.id.comp a) (b.comp a)
      L.leftUnitor (isoWhiskerRight e L),
      conjugateIsoEquiv_leftUnitor, conjugateIsoEquiv_isoWhiskerRight, he]
  have hθ' : conjugateIsoEquiv (a.comp c) (b.comp a) θ = β.symm := by
    simpa only [conjugateIsoEquiv_iso_symm, Iso.symm_symm_eq] using
      congrArg Iso.symm hθ
  rw [hθ']
  apply Iso.ext
  have h := congrArg Iso.hom hr
  simpa using h

private lemma paste_cancel {C : Type*} [Category* C] {A B D E F : C}
    (a : A ≅ B) (b : B ⟶ D) (c : D ⟶ E) (d : F ≅ E) (e : A ⟶ F)
    (h : b ≫ c = (a.inv ≫ e) ≫ d.hom) : a.hom ≫ b ≫ c ≫ d.inv = e := by
  rw [← Category.assoc b c d.inv, h]
  simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]
  rw [← Category.assoc, Iso.hom_inv_id, Category.id_comp]

end CategoryTheory

namespace AlgebraicGeometry.ProEtale

/-- Canonical composition of pro-etale extension by zero, oriented from composite
extension to iterated extension. It is the unique left-adjoint comparison for the
canonical composition of inverse images, exactly as on the etale site. -/
noncomputable def proEtaleOpenExtensionComp (Λ : Type (u + 1)) [CommRing Λ]
    {V U X : Scheme.{u}} (k : V ⟶ U) (j : U ⟶ X)
    [IsOpenImmersion k] [IsOpenImmersion j] :
    openImmersionLowerShriek (ModuleCat.{u + 1} Λ) (k ≫ j) ≅
      openImmersionLowerShriek (ModuleCat.{u + 1} Λ) k ⋙
        openImmersionLowerShriek (ModuleCat.{u + 1} Λ) j :=
  (openImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} Λ) (k ≫ j)).leftAdjointUniq
    (((openImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} Λ) k).comp
      (openImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} Λ) j)).ofNatIsoRight
        (upperStarComp (ModuleCat.{u + 1} Λ) k j).symm)

open Scheme CategoryTheory.Limits Opposite
variable (A : Type u') [Category.{u + 1} A] [Abelian A]
  [IsGrothendieckAbelian.{u + 1} A]
variable {V U X : Scheme.{u}} (k : V ⟶ U) (j : U ⟶ X)
  [IsOpenImmersion k] [IsOpenImmersion j]

-- Literal restriction composition, before transporting to the chosen pullbacks.
private noncomputable def resComp :
    openImmersionRestriction A (k ≫ j) ≅
      openImmersionRestriction A j ⋙ openImmersionRestriction A k :=
  (Functor.sheafPushforwardContinuousComp'
    (eFG := (MorphismProperty.Over.mapComp ⊤
      (inferInstance : WeaklyEtale k) (inferInstance : WeaklyEtale j)
      (k ≫ j) rfl).symm)
    A (ProEt.topology V) (ProEt.topology U) (ProEt.topology X)).symm
set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
set_option linter.flexible false in
omit [Abelian A] [IsGrothendieckAbelian.{u + 1} A] in
private lemma resComp_conj :
    conjugateEquiv (openImmersionRestrictionLowerStarAdjunction A (k ≫ j))
      ((openImmersionRestrictionLowerStarAdjunction A j).comp
        (openImmersionRestrictionLowerStarAdjunction A k))
      (resComp A k j).inv = (lowerStarComp A k j).inv := by
  ext G : 2
  apply Sheaf.hom_ext
  refine NatTrans.ext (funext fun W ↦ ?_)
  simp [conjugateEquiv_apply_app, openImmersionRestrictionLowerStarAdjunction,
    localizationRestrictionLowerStarAdjunction, resComp, lowerStarComp,
    MorphismProperty.Over.mapPullbackAdj, Functor.sheafPushforwardContinuousComp',
    Functor.sheafPushforwardContinuousComp, Functor.sheafPushforwardContinuousIso,
    openImmersionRestriction, localizationRestriction, lowerStar, ← Functor.map_comp]
  congr 1
  apply Quiver.Hom.unop_inj
  ext
  simp only [MorphismProperty.Over.mapComp, MorphismProperty.Over.pullbackComp]
  apply pullback.hom_ext <;> simp
private lemma up_res_comp :
    (upperStarComp A k j).hom ≫
        whiskerRight (upperStarIsoOpenImmersionRestriction A j).hom (upperStar A k) ≫
        whiskerLeft (openImmersionRestriction A j)
          (upperStarIsoOpenImmersionRestriction A k).hom =
      (upperStarIsoOpenImmersionRestriction A (k ≫ j)).hom ≫ (resComp A k j).hom := by
  let C := (openImmersionRestrictionLowerStarAdjunction A j).comp
    (openImmersionRestrictionLowerStarAdjunction A k)
  let LU := (openImmersionRestrictionLowerStarAdjunction A j).comp
    (upperStarLowerStarAdjunction A k)
  let UU := (upperStarLowerStarAdjunction A j).comp (upperStarLowerStarAdjunction A k)
  let U₁₂ := upperStarLowerStarAdjunction A (k ≫ j)
  let L₁₂ := openImmersionRestrictionLowerStarAdjunction A (k ≫ j)
  have hs (S T : Scheme.{u}) (f : S ⟶ T) [IsOpenImmersion f] :
      conjugateEquiv (openImmersionRestrictionLowerStarAdjunction A f)
        (upperStarLowerStarAdjunction A f)
        (upperStarIsoOpenImmersionRestriction A f).hom = 𝟙 _ := by
    exact conjugateEquiv_leftAdjointUniq_hom _ _
  apply (conjugateEquiv C U₁₂).injective
  rw [← conjugateEquiv_comp C UU U₁₂, ← conjugateEquiv_comp C LU UU,
    ← conjugateEquiv_comp C L₁₂ U₁₂]
  dsimp only [C, LU, UU]
  rw [conjugateEquiv_whiskerLeft, conjugateEquiv_whiskerRight, hs, hs, hs]
  simp only [whiskerRight_id', whiskerLeft_id', Category.id_comp, Category.comp_id]
  have e₁ : conjugateIsoEquiv L₁₂ _ (resComp A k j).symm =
      (lowerStarComp A k j).symm := Iso.ext (resComp_conj A k j)
  have e₂ := (conjugateIsoEquiv U₁₂ UU).apply_symm_apply (lowerStarComp A k j).symm
  have h₁ := congrArg Iso.inv e₁
  have h₂ := congrArg Iso.inv e₂
  simp only [conjugateIsoEquiv_apply_inv, Iso.symm_inv] at h₁ h₂
  rw [h₁]
  convert h₂ using 2
  rfl
-- The public extension composition maps are mates of literal restriction composition.
private lemma proComp_conj (Λ : Type (u + 1)) [CommRing Λ] :
    conjugateIsoEquiv
      ((openImmersionLowerShriekAdjunction (ModuleCat.{u + 1} Λ) k).comp
        (openImmersionLowerShriekAdjunction (ModuleCat.{u + 1} Λ) j))
      (openImmersionLowerShriekAdjunction (ModuleCat.{u + 1} Λ) (k ≫ j))
      (proEtaleOpenExtensionComp Λ k j) = (resComp (ModuleCat.{u + 1} Λ) k j).symm := by
  let B := ModuleCat.{u + 1} Λ
  apply comp_conjugate
    (openImmersionLowerShriekAdjunction B k) (openImmersionLowerShriekAdjunction B j)
    (openImmersionLowerShriekAdjunction B (k ≫ j))
    (upperStarIsoOpenImmersionRestriction B k).symm
    (upperStarIsoOpenImmersionRestriction B j).symm
    (upperStarIsoOpenImmersionRestriction B (k ≫ j)).symm
    (upperStarComp B k j) (resComp B k j)
  have h : upperStarComp B k j ≪≫
      isoWhiskerRight (upperStarIsoOpenImmersionRestriction B j) (upperStar B k) ≪≫
      isoWhiskerLeft (openImmersionRestriction B j)
        (upperStarIsoOpenImmersionRestriction B k) =
      upperStarIsoOpenImmersionRestriction B (k ≫ j) ≪≫ resComp B k j :=
    Iso.ext (up_res_comp B k j)
  simpa [← isoWhiskerLeft_symm, ← isoWhiskerRight_symm, Iso.trans_assoc] using congrArg
    (fun z ↦ (upperStarIsoOpenImmersionRestriction B (k ≫ j)).symm ≪≫ z ≪≫
      isoWhiskerLeft (openImmersionRestriction B j)
        (upperStarIsoOpenImmersionRestriction B k).symm ≪≫
      isoWhiskerRight (upperStarIsoOpenImmersionRestriction B j).symm (upperStar B k)) h.symm
private noncomputable def etResComp :
    Etale.openImmersionRestriction A (k ≫ j) ≅
      Etale.openImmersionRestriction A j ⋙ Etale.openImmersionRestriction A k :=
  Etale.localizationRestrictionComp A k j inferInstance inferInstance (k ≫ j) rfl
    inferInstance

private lemma etComp_conj (Λ : Type (u + 1)) [CommRing Λ] :
    conjugateIsoEquiv
      ((Etale.openImmersionLowerShriekAdjunction (ModuleCat.{u + 1} Λ) k).comp
        (Etale.openImmersionLowerShriekAdjunction (ModuleCat.{u + 1} Λ) j))
      (Etale.openImmersionLowerShriekAdjunction (ModuleCat.{u + 1} Λ) (k ≫ j))
      (Etale.openImmersionLowerShriekComp (ModuleCat.{u + 1} Λ) k j) =
      (etResComp (ModuleCat.{u + 1} Λ) k j).symm := by
  let B := ModuleCat.{u + 1} Λ
  apply comp_conjugate
    (Etale.openImmersionLowerShriekAdjunction B k)
    (Etale.openImmersionLowerShriekAdjunction B j)
    (Etale.openImmersionLowerShriekAdjunction B (k ≫ j))
    (Etale.upperStarIsoOpenImmersionRestriction B k).symm
    (Etale.upperStarIsoOpenImmersionRestriction B j).symm
    (Etale.upperStarIsoOpenImmersionRestriction B (k ≫ j)).symm
    (Etale.upperStarComp B k j) (etResComp B k j)
  have h : Etale.upperStarComp B k j ≪≫
      isoWhiskerRight (Etale.upperStarIsoOpenImmersionRestriction B j) (Etale.upperStar B k) ≪≫
      isoWhiskerLeft (Etale.openImmersionRestriction B j)
        (Etale.upperStarIsoOpenImmersionRestriction B k) =
      Etale.upperStarIsoOpenImmersionRestriction B (k ≫ j) ≪≫ etResComp B k j :=
    Iso.ext (Etale.upperStarComp_hom_comp_upperStarIsoLocalizationRestriction B k j
      inferInstance inferInstance (k ≫ j) rfl inferInstance)
  simpa [← isoWhiskerLeft_symm, ← isoWhiskerRight_symm, Iso.trans_assoc] using congrArg
    (fun z ↦ (Etale.upperStarIsoOpenImmersionRestriction B (k ≫ j)).symm ≪≫ z ≪≫
      isoWhiskerLeft (Etale.openImmersionRestriction B j)
        (Etale.upperStarIsoOpenImmersionRestriction B k).symm ≪≫
      isoWhiskerRight (Etale.upperStarIsoOpenImmersionRestriction B j).symm (Etale.upperStar B k))
    h.symm
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option linter.flexible false in
-- Both right-adjoint routes are the same restriction on sections.
private lemma comparison_paste (Λ : Type (u + 1)) [CommRing Λ] :
    isoWhiskerRight
        (openImmersionLowerShriekComparisonUpperStarIso (ModuleCat.{u + 1} Λ) k).symm
        (openImmersionLowerShriek (ModuleCat.{u + 1} Λ) j) ≪≫
      (Etale.openImmersionLowerShriek (ModuleCat.{u + 1} Λ) k).associator
        (comparisonUpperStar (ModuleCat.{u + 1} Λ) U)
        (openImmersionLowerShriek (ModuleCat.{u + 1} Λ) j) ≪≫
      isoWhiskerLeft (Etale.openImmersionLowerShriek (ModuleCat.{u + 1} Λ) k)
        (openImmersionLowerShriekComparisonUpperStarIso (ModuleCat.{u + 1} Λ) j).symm ≪≫
      ((Etale.openImmersionLowerShriek (ModuleCat.{u + 1} Λ) k).associator
        (Etale.openImmersionLowerShriek (ModuleCat.{u + 1} Λ) j)
        (comparisonUpperStar (ModuleCat.{u + 1} Λ) X)).symm =
      (comparisonUpperStar (ModuleCat.{u + 1} Λ) V).associator
        (openImmersionLowerShriek (ModuleCat.{u + 1} Λ) k)
        (openImmersionLowerShriek (ModuleCat.{u + 1} Λ) j) ≪≫
      isoWhiskerLeft (comparisonUpperStar (ModuleCat.{u + 1} Λ) V)
        (proEtaleOpenExtensionComp Λ k j).symm ≪≫
      (openImmersionLowerShriekComparisonUpperStarIso (ModuleCat.{u + 1} Λ) (k ≫ j)).symm ≪≫
      isoWhiskerRight (Etale.openImmersionLowerShriekComp (ModuleCat.{u + 1} Λ) k j)
        (comparisonUpperStar (ModuleCat.{u + 1} Λ) X) := by
  let B := ModuleCat.{u + 1} Λ
  apply adjunctionSquareComposition
    (comparisonAdjunction B V) (comparisonAdjunction B U) (comparisonAdjunction B X)
    (Etale.openImmersionLowerShriekAdjunction B k)
    (Etale.openImmersionLowerShriekAdjunction B j)
    (Etale.openImmersionLowerShriekAdjunction B (k ≫ j))
    (openImmersionLowerShriekAdjunction B k) (openImmersionLowerShriekAdjunction B j)
    (openImmersionLowerShriekAdjunction B (k ≫ j))
    (comparisonLowerStarOpenImmersionRestrictionIso B k).symm
    (comparisonLowerStarOpenImmersionRestrictionIso B j).symm
    (comparisonLowerStarOpenImmersionRestrictionIso B (k ≫ j)).symm
    (etResComp B k j) (resComp B k j).symm
  · dsimp only [openImmersionLowerShriekComparisonUpperStarIso]
    exact Equiv.apply_symm_apply _ _
  · dsimp only [openImmersionLowerShriekComparisonUpperStarIso]
    exact Equiv.apply_symm_apply _ _
  · dsimp only [openImmersionLowerShriekComparisonUpperStarIso]
    exact Equiv.apply_symm_apply _ _
  · exact etComp_conj k j Λ
  · rw [conjugateIsoEquiv_iso_symm, proComp_conj k j Λ]
  · apply Iso.ext
    apply NatTrans.ext
    funext M
    apply Sheaf.hom_ext
    refine NatTrans.ext (funext fun W ↦ ?_)
    simp [comparisonLowerStarOpenImmersionRestrictionIso, resComp, etResComp,
      Etale.localizationRestrictionComp, Functor.sheafPushforwardContinuousComp',
      Functor.sheafPushforwardContinuousComp, Functor.sheafPushforwardContinuousIso,
      comparisonLowerStar, Etale.openImmersionRestriction, Etale.localizationRestriction,
      openImmersionRestriction, localizationRestriction]
    change 𝟙 _ = M.obj.map
      ((MorphismProperty.Over.mapComp (P := @WeaklyEtale) ⊤
        (inferInstance : WeaklyEtale k) (inferInstance : WeaklyEtale j)).inv.app
          (toProEt V |>.obj (unop W))).op ≫ 𝟙 _ ≫ 𝟙 _ ≫ M.obj.map
      ((toProEt X).map
        ((MorphismProperty.Over.mapComp (P := @Etale) ⊤
          (inferInstance : Etale k) (inferInstance : Etale j)).hom.app (unop W))).op
    simp only [Category.id_comp]
    rw [← M.obj.map_comp]
    refine (M.obj.map_id _).symm.trans (congrArg M.obj.map ?_)
    apply Quiver.Hom.unop_inj
    apply MorphismProperty.Over.Hom.ext
    simp [MorphismProperty.Over.mapComp, Scheme.toProEt]
    change 𝟙 _ = 𝟙 _ ≫ 𝟙 _
    simp
-- Identity restriction and its compatibility with the canonical pullback unit.
private noncomputable def resId (X : Scheme.{u}) :
    openImmersionRestriction A (𝟙 X) ≅ 𝟭 _ :=
  Functor.sheafPushforwardContinuousId'
    (MorphismProperty.Over.mapId (P := @WeaklyEtale) (Q := ⊤) X) A (ProEt.topology X)

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
set_option linter.flexible false in
omit [Abelian A] [IsGrothendieckAbelian.{u + 1} A] in
private lemma resId_conj (X : Scheme.{u}) :
    conjugateIsoEquiv Adjunction.id (openImmersionRestrictionLowerStarAdjunction A (𝟙 X))
      (resId A X) = (lowerStarId A X).symm := by
  apply Iso.ext
  apply NatTrans.ext
  funext G
  apply Sheaf.hom_ext
  refine NatTrans.ext (funext fun W ↦ ?_)
  simp [conjugateEquiv_apply_app, openImmersionRestrictionLowerStarAdjunction,
    localizationRestrictionLowerStarAdjunction, resId, lowerStarId,
    MorphismProperty.Over.mapPullbackAdj, Functor.sheafPushforwardContinuousId',
    Functor.sheafPushforwardContinuousId, Functor.sheafPushforwardContinuousIso,
    openImmersionRestriction, localizationRestriction, lowerStar, ← Functor.map_comp]
  congr 1

private lemma up_res_id (X : Scheme.{u}) :
    upperStarIsoOpenImmersionRestriction A (𝟙 X) ≪≫ resId A X = upperStarId A X := by
  apply (conjugateIsoEquiv Adjunction.id (upperStarLowerStarAdjunction A (𝟙 X))).injective
  rw [conjugateIsoEquiv_trans _ (openImmersionRestrictionLowerStarAdjunction A (𝟙 X)) _,
    resId_conj, conjugateIsoEquiv_upperStarId]
  have h : conjugateIsoEquiv (openImmersionRestrictionLowerStarAdjunction A (𝟙 X))
      (upperStarLowerStarAdjunction A (𝟙 X))
      (upperStarIsoOpenImmersionRestriction A (𝟙 X)) = Iso.refl _ := by
    exact Iso.ext (conjugateEquiv_leftAdjointUniq_hom _ _)
  rw [h, Iso.trans_refl]

set_option backward.isDefEq.respectTransparency false in
private noncomputable def etResId (X : Scheme.{u}) :
    Etale.openImmersionRestriction A (𝟙 X) ≅ 𝟭 _ :=
  letI : (MorphismProperty.Over.map (P := @Etale) (Q := ⊤)
      (inferInstance : Etale (𝟙 X))).IsContinuous X.smallEtaleTopology X.smallEtaleTopology :=
    Scheme.isContinuous_overMap (inferInstance : Etale (𝟙 X)) le_rfl
  Functor.sheafPushforwardContinuousId'
    (MorphismProperty.Over.mapId (P := @Etale) (Q := ⊤) X) A X.smallEtaleTopology

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
set_option linter.flexible false in
omit [Abelian A] [IsGrothendieckAbelian.{u + 1} A] in
private lemma etResId_conj (X : Scheme.{u}) :
    conjugateIsoEquiv Adjunction.id (Etale.openImmersionRestrictionLowerStarAdjunction A (𝟙 X))
      (etResId A X) = (Etale.lowerStarId A X).symm := by
  apply Iso.ext
  apply NatTrans.ext
  funext G
  apply Sheaf.hom_ext
  refine NatTrans.ext (funext fun W ↦ ?_)
  simp [conjugateEquiv_apply_app, Etale.openImmersionRestrictionLowerStarAdjunction,
    Etale.localizationRestrictionLowerStarAdjunction, etResId, Etale.lowerStarId,
    GrothendieckTopology.lowerStarId,
    MorphismProperty.Over.mapPullbackAdj, Functor.sheafPushforwardContinuousId',
    Functor.sheafPushforwardContinuousId, Functor.sheafPushforwardContinuousIso,
    Etale.openImmersionRestriction, Etale.localizationRestriction, Etale.lowerStar,
    ← Functor.map_comp]
  congr 1

private lemma et_up_res_id (X : Scheme.{u}) :
    Etale.upperStarIsoOpenImmersionRestriction A (𝟙 X) ≪≫ etResId A X =
      Etale.upperStarId A X := by
  apply (conjugateIsoEquiv Adjunction.id (Etale.upperStarLowerStarAdjunction A (𝟙 X))).injective
  rw [conjugateIsoEquiv_trans _ (Etale.openImmersionRestrictionLowerStarAdjunction A (𝟙 X)) _,
    etResId_conj, Etale.conjugateIsoEquiv_upperStarId]
  have h : conjugateIsoEquiv (Etale.openImmersionRestrictionLowerStarAdjunction A (𝟙 X))
      (Etale.upperStarLowerStarAdjunction A (𝟙 X))
      (Etale.upperStarIsoOpenImmersionRestriction A (𝟙 X)) = Iso.refl _ := by
    exact Iso.ext (conjugateEquiv_leftAdjointUniq_hom _ _)
  rw [h, Iso.trans_refl]
set_option linter.flexible false in
-- Conjugation transfers the sectionwise identity law to extension by zero.
private lemma comparison_identity (Λ : Type (u + 1)) [CommRing Λ] (X : Scheme.{u}) :
    openImmersionLowerShriekComparisonUpperStarIso (ModuleCat.{u + 1} Λ) (𝟙 X) ≪≫
      isoWhiskerLeft (comparisonUpperStar (ModuleCat.{u + 1} Λ) X)
        (Adjunction.leftAdjointIdIso
          (openImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} Λ) (𝟙 X))
          (upperStarId (ModuleCat.{u + 1} Λ) X)) ≪≫
      (comparisonUpperStar (ModuleCat.{u + 1} Λ) X).rightUnitor =
      isoWhiskerRight
        (Adjunction.leftAdjointIdIso
          (Etale.openImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} Λ) (𝟙 X))
          (Etale.upperStarId (ModuleCat.{u + 1} Λ) X))
        (comparisonUpperStar (ModuleCat.{u + 1} Λ) X) ≪≫
      (comparisonUpperStar (ModuleCat.{u + 1} Λ) X).leftUnitor := by
  let B := ModuleCat.{u + 1} Λ
  apply identity_square (comparisonAdjunction B X)
    (Etale.openImmersionLowerShriekAdjunction B (𝟙 X))
    (openImmersionLowerShriekAdjunction B (𝟙 X))
    (openImmersionLowerShriekComparisonUpperStarIso B (𝟙 X))
    _ _ (comparisonLowerStarOpenImmersionRestrictionIso B (𝟙 X))
    (etResId B X) (resId B X)
  · dsimp only [openImmersionLowerShriekComparisonUpperStarIso, Iso.symm_symm_eq]
    exact Equiv.apply_symm_apply _ _
  · have h := id_conjugate (Etale.openImmersionLowerShriekAdjunction B (𝟙 X))
      (Etale.upperStarIsoOpenImmersionRestriction B (𝟙 X)).symm (Etale.upperStarId B X)
    have hi : (Etale.upperStarIsoOpenImmersionRestriction B (𝟙 X)).symm ≪≫
        Etale.upperStarId B X = etResId B X := by
      rw [← et_up_res_id B X]
      simp
    rw [hi] at h
    exact h
  · have h := id_conjugate (openImmersionLowerShriekAdjunction B (𝟙 X))
      (upperStarIsoOpenImmersionRestriction B (𝟙 X)).symm (upperStarId B X)
    have hi : (upperStarIsoOpenImmersionRestriction B (𝟙 X)).symm ≪≫
        upperStarId B X = resId B X := by
      rw [← up_res_id B X]
      simp
    rw [hi] at h
    exact h
  · apply Iso.ext
    apply NatTrans.ext
    funext M
    apply Sheaf.hom_ext
    refine NatTrans.ext (funext fun W ↦ ?_)
    simp [comparisonLowerStarOpenImmersionRestrictionIso, resId, etResId,
      Functor.sheafPushforwardContinuousId', Functor.sheafPushforwardContinuousId,
      Functor.sheafPushforwardContinuousIso, comparisonLowerStar,
      Etale.openImmersionRestriction, Etale.localizationRestriction,
      openImmersionRestriction, localizationRestriction]
    change M.obj.map
        ((MorphismProperty.Over.mapId (P := @WeaklyEtale) (Q := ⊤) X).hom.app
          ((toProEt X).obj (unop W))).op ≫ 𝟙 _ =
      M.obj.map ((toProEt X).map
        ((MorphismProperty.Over.mapId (P := @Etale) (Q := ⊤) X).hom.app (unop W))).op
    rw [Category.comp_id]
    congr 1

/-- The canonical comparison `ν_X^* j_! F ⟶ j_! ν_U^* F` is invertible and commutes
with composition and identity open immersions. Naturality in `F` is built into the
existing natural isomorphism `openImmersionLowerShriekComparisonUpperStarIso`. -/
theorem openImmersionLowerShriekComparison_coherence
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ] :
    (∀ {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
      (F : Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} Λ)),
      IsIso ((openImmersionLowerShriekComparisonUpperStarIso
        (ModuleCat.{u + 1} Λ) j).hom.app F)) ∧
    (∀ {V U X : Scheme.{u}} (k : V ⟶ U) (j : U ⟶ X)
      [IsOpenImmersion k] [IsOpenImmersion j]
      (F : Sheaf V.smallEtaleTopology (ModuleCat.{u + 1} Λ)),
      (comparisonUpperStar (ModuleCat.{u + 1} Λ) X).map
          ((Etale.openImmersionLowerShriekComp (ModuleCat.{u + 1} Λ) k j).hom.app F) ≫
        (openImmersionLowerShriekComparisonUpperStarIso (ModuleCat.{u + 1} Λ) j).hom.app
          ((Etale.openImmersionLowerShriek (ModuleCat.{u + 1} Λ) k).obj F) ≫
        (openImmersionLowerShriek (ModuleCat.{u + 1} Λ) j).map
          ((openImmersionLowerShriekComparisonUpperStarIso (ModuleCat.{u + 1} Λ) k).hom.app F) ≫
        (proEtaleOpenExtensionComp Λ k j).inv.app
          ((comparisonUpperStar (ModuleCat.{u + 1} Λ) V).obj F) =
      (openImmersionLowerShriekComparisonUpperStarIso
        (ModuleCat.{u + 1} Λ) (k ≫ j)).hom.app F) ∧
    (∀ (X : Scheme.{u}) (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)),
      (openImmersionLowerShriekComparisonUpperStarIso (ModuleCat.{u + 1} Λ) (𝟙 X)).hom.app F ≫
        (Adjunction.leftAdjointIdIso
          (openImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} Λ) (𝟙 X))
          (upperStarId (ModuleCat.{u + 1} Λ) X)).hom.app
            ((comparisonUpperStar (ModuleCat.{u + 1} Λ) X).obj F) =
      (comparisonUpperStar (ModuleCat.{u + 1} Λ) X).map
        ((Adjunction.leftAdjointIdIso
          (Etale.openImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} Λ) (𝟙 X))
          (Etale.upperStarId (ModuleCat.{u + 1} Λ) X)).hom.app F)) := by
  refine ⟨?_, ?_, ?_⟩
  · intro U X j _ F
    infer_instance
  · intro V U X k j _ _ F
    have h := congrArg (fun e ↦ e.inv.app F) (comparison_paste k j Λ)
    simp only [Iso.trans_inv, isoWhiskerRight_inv, isoWhiskerLeft_inv,
      Iso.symm_inv, NatTrans.comp_app, whiskerLeft_app, whiskerRight_app,
      associator_hom_app, associator_inv_app, Category.id_comp, Category.comp_id] at h
    exact paste_cancel
      ((comparisonUpperStar (ModuleCat.{u + 1} Λ) X).mapIso
        ((Etale.openImmersionLowerShriekComp (ModuleCat.{u + 1} Λ) k j).app F))
      _ _ ((proEtaleOpenExtensionComp Λ k j).app
        ((comparisonUpperStar (ModuleCat.{u + 1} Λ) V).obj F)) _ h
  · intro X F
    have h := congrArg (fun e ↦ e.hom.app F) (comparison_identity Λ X)
    simpa using h

end AlgebraicGeometry.ProEtale
