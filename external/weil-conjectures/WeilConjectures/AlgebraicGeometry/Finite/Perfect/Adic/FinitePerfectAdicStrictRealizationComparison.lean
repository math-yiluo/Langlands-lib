/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Finite.Perfect.Adic.FinitePerfectAdicScalarCoherence
public import WeilConjectures.AlgebraicGeometry.Finite.Perfect.Adic.FinitePerfectAdicQuotientTransition
import all WeilConjectures.AlgebraicGeometry.Finite.Perfect.Adic.FinitePerfectAdicScalarCoherence

/-! # Scalar realizations of ordinary fixed-scalar coordinates

The explicit scalar realization of the fixed-scalar coordinates of a module sheaf is the
restriction of the module sheaf to the slice.

Source: Stacks Project, Tags 03CY, 03DA and 06YY.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe t
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme
attribute [local instance] finitePerfectModelsAbLocallyBijective

/-- Inverse image along a pro-etale chart commutes with restriction of fixed scalars.
Source: Stacks Tag 03DA. -/
def finitePerfectAdicPullbackRestrictComparison {Y Z : Scheme.{t}} (g : Z ⟶ Y)
    {R S : Type (t + 1)} [CommRing R] [CommRing S] (q : R →+* S) :
    sheafCompose (ProEt.topology Y) (ModuleCat.restrictScalars.{t + 1, t + 1, t + 1} q) ⋙
        ProEtale.upperStar (ModuleCat.{t + 1} R) g ≅
      ProEtale.upperStar (ModuleCat.{t + 1} S) g ⋙
        sheafCompose (ProEt.topology Z) (ModuleCat.restrictScalars.{t + 1, t + 1, t + 1} q) :=
  letI := ProEt.isContinuous_overPullback g
  normalizationPullbackIso (ProEt.topology Y)
    (MorphismProperty.Over.pullback @WeaklyEtale ⊤ g) (ProEt.topology Z) q

/-- The inverse-image comparison with coefficient restriction is compatible with the
identification of inverse image along a weakly etale map with restriction.
Source: Stacks Tags 00WX and 03DA. -/
theorem finitePerfectAdic_pullbackRestrict_upperStarIso {Y Z : Scheme.{t}} (g : Z ⟶ Y)
    (hg : WeaklyEtale g) {R S : Type (t + 1)} [CommRing R] [CommRing S] (q : R →+* S)
    (G : Sheaf (ProEt.topology Y) (ModuleCat.{t + 1} S)) :
    (finitePerfectAdicPullbackRestrictComparison g q).hom.app G ≫
      (sheafCompose (ProEt.topology Z) (ModuleCat.restrictScalars.{t + 1, t + 1, t + 1} q)).map
        ((ProEtale.upperStarIsoLocalizationRestriction (ModuleCat.{t + 1} S) g hg).hom.app G) =
      (ProEtale.upperStarIsoLocalizationRestriction (ModuleCat.{t + 1} R) g hg).hom.app
        ((sheafCompose (ProEt.topology Y)
          (ModuleCat.restrictScalars.{t + 1, t + 1, t + 1} q)).obj G) := by
  let := ProEt.isContinuous_overPullback g
  let adjS := ProEtale.upperStarLowerStarAdjunction (ModuleCat.{t + 1} S) g
  let adjR := ProEtale.upperStarLowerStarAdjunction (ModuleCat.{t + 1} R) g
  let adjS' := ProEtale.localizationRestrictionLowerStarAdjunction (ModuleCat.{t + 1} S) g hg
  let adjR' := ProEtale.localizationRestrictionLowerStarAdjunction (ModuleCat.{t + 1} R) g hg
  let ρY := sheafCompose (ProEt.topology Y) (ModuleCat.restrictScalars.{t + 1, t + 1, t + 1} q)
  let ρZ := sheafCompose (ProEt.topology Z) (ModuleCat.restrictScalars.{t + 1, t + 1, t + 1} q)
  have hμ : ρY.map (adjS.unit.app G) = adjR.unit.app (ρY.obj G) ≫
      (ProEtale.lowerStar (ModuleCat.{t + 1} R) g).map ((normalizationPullbackMate
        (ProEt.topology Y) (MorphismProperty.Over.pullback @WeaklyEtale ⊤ g)
        (ProEt.topology Z) q).app G) := by
    unfold normalizationPullbackMate
    exact (Category.comp_id _).symm.trans (unit_mateEquiv_symm
      (Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
        (MorphismProperty.Over.pullback @WeaklyEtale ⊤ g) (ModuleCat.{t + 1} S) (ProEt.topology Y)
        (ProEt.topology Z))
      (Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
        (MorphismProperty.Over.pullback @WeaklyEtale ⊤ g) (ModuleCat.{t + 1} R) (ProEt.topology Y)
        (ProEt.topology Z))
      (TwoSquare.mk ((MorphismProperty.Over.pullback @WeaklyEtale ⊤ g).sheafPushforwardContinuous
          (ModuleCat.{t + 1} S) (ProEt.topology Y) (ProEt.topology Z))
        (sheafCompose (ProEt.topology Z) (ModuleCat.restrictScalars.{t + 1, t + 1, t + 1} q))
        (sheafCompose (ProEt.topology Y) (ModuleCat.restrictScalars.{t + 1, t + 1, t + 1} q))
        ((MorphismProperty.Over.pullback @WeaklyEtale ⊤ g).sheafPushforwardContinuous
          (ModuleCat.{t + 1} R) (ProEt.topology Y) (ProEt.topology Z)) (𝟙 _)) G)
  have hS := Adjunction.homEquiv_leftAdjointUniq_hom_app adjS adjS' G
  have hR := Adjunction.homEquiv_leftAdjointUniq_hom_app adjR adjR' (ρY.obj G)
  have hU : ρY.map (adjS'.unit.app G) = adjR'.unit.app (ρY.obj G) := by
    ext U x
    rfl
  apply (adjR.homEquiv _ _).injective
  change adjR.homEquiv _ _ ((normalizationPullbackMate (ProEt.topology Y)
      (MorphismProperty.Over.pullback @WeaklyEtale ⊤ g) (ProEt.topology Z) q).app G ≫
      ρZ.map ((adjS.leftAdjointUniq adjS').hom.app G)) =
    adjR.homEquiv _ _ ((adjR.leftAdjointUniq adjR').hom.app (ρY.obj G))
  rw [hR, Adjunction.homEquiv_naturality_right, Adjunction.homEquiv_unit, ← hμ, ← hU, ← hS,
    Adjunction.homEquiv_unit, Functor.map_comp]
  rfl

section Associated

variable {C : Type (t + 1)} [Category.{t} C] {J : GrothendieckTopology C}
  [HasWeakSheafify J AddCommGrpCat.{t + 1}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{t + 1}]
  {B : Type (t + 1)} [CommRing B] {R : Sheaf J RingCat.{t + 1}}
  (α : (Functor.const Cᵒᵖ).obj (RingCat.of B) ⟶ R.obj)
  [Presheaf.IsLocallyInjective J α] [Presheaf.IsLocallySurjective J α]

/-- The associated module sheaf of a map, before associated sheafification. -/
theorem finitePerfectAdicAssociated_map_unit {N N' : Sheaf J (ModuleCat.{t + 1} B)}
    (h : N ⟶ N') :
    toSheafify J ((ProEtale.finiteCoefficientModulePresheaf C B).obj
        ((sheafToPresheaf J _).obj N)).presheaf ≫
      (PresheafOfModules.toPresheaf _).map ((SheafOfModules.forget _).map
        ((finitePerfectAdicAssociated α).map h)) =
      (PresheafOfModules.toPresheaf _).map ((ProEtale.finiteCoefficientModulePresheaf C B).map
        ((sheafToPresheaf J _).map h)) ≫
        toSheafify J ((ProEtale.finiteCoefficientModulePresheaf C B).obj
          ((sheafToPresheaf J _).obj N')).presheaf :=
  (toSheafify_naturality J _).symm

omit [Presheaf.IsLocallyInjective J α] [Presheaf.IsLocallySurjective J α] in
/-- The associated-sheaf scalar comparison is the identity on underlying sheaves, before
associated sheafification. -/
theorem finitePerfectAdicAssociatedCoherence_unit {D : Type (t + 1)} [CommRing D]
    {S : Sheaf J RingCat.{t + 1}} (β : (Functor.const Cᵒᵖ).obj (RingCat.of D) ⟶ S.obj)
    [Presheaf.IsLocallyInjective J α] [Presheaf.IsLocallySurjective J α]
    [Presheaf.IsLocallyInjective J β] [Presheaf.IsLocallySurjective J β]
    (q : B →+* D) (p : R ⟶ S)
    (h : ∀ Z : Cᵒᵖ, α.app Z ≫ p.hom.app Z = RingCat.ofHom q ≫ β.app Z)
    (N : Sheaf J (ModuleCat.{t + 1} D)) :
    toSheafify J ((ProEtale.finiteCoefficientModulePresheaf C B).obj ((sheafToPresheaf J _).obj
        ((sheafCompose J (ModuleCat.restrictScalars.{t + 1} q)).obj N))).presheaf ≫
      (PresheafOfModules.toPresheaf _).map ((SheafOfModules.forget _).map
        ((finitePerfectAdicAssociatedCoherence α β q p h).hom.app N)) =
      toSheafify J ((ProEtale.finiteCoefficientModulePresheaf C D).obj
        ((sheafToPresheaf J _).obj N)).presheaf := by
  unfold finitePerfectAdicAssociatedCoherence
  rw [(finitePerfectAdicAssociated_coherence_existsUnique α β q p h).choose_spec.1 N]
  exact associatedMap_unit α β q p h N

end Associated

section Realization

set_option hygiene false in
local notation "𝓡" R => (sheafCompose (ProEt.topology X)
  (forget₂ CommRingCat.{t + 1} RingCat.{t + 1})).obj R

variable (X : Scheme.{t}) (V : X.Etale) (U : V.left.ProEt) (W : X.ProEt)
  (f : W ⟶ finitePerfectAdicChartObject V U)

/-- Restriction from the chart to `W`, followed by transport to the slice. -/
def finitePerfectAdicChartSlice (Q : Type (t + 1)) [CommRing Q] :
    Sheaf (ProEt.topology U.left) (ModuleCat.{t + 1} Q) ⥤
      Sheaf ((ProEt.topology X).over W) (ModuleCat.{t + 1} Q) :=
  have := ProEt.sliceDense X W
  ProEtale.localizationRestriction (ModuleCat.{t + 1} Q) f.left
      (finitePerfectAdicChartArrow_weaklyEtale V U W f) ⋙
    ((ProEt.sliceEquiv X W).sheafCongr ((ProEt.topology X).over W)
      (ProEt.topology W.left) (ModuleCat.{t + 1} Q)).inverse

/-- The explicit scalar realization for an arbitrary locally bijective fixed-scalar
presentation of a ring sheaf on the slice and an arbitrary map of ring sheaves. -/
def finitePerfectAdicRealizationModules {Q : Type (t + 1)} [CommRing Q]
    {R T : Sheaf (ProEt.topology X) RingCat.{t + 1}}
    (αW : (Functor.const (Over W)ᵒᵖ).obj (RingCat.of Q) ⟶ (R.over W).obj)
    [Presheaf.IsLocallyInjective ((ProEt.topology X).over W) αW]
    [Presheaf.IsLocallySurjective ((ProEt.topology X).over W) αW] (π : T ⟶ R) :
    Sheaf (ProEt.topology U.left) (ModuleCat.{t + 1} Q) ⥤ SheafOfModules.{t + 1} (T.over W) :=
  finitePerfectAdicChartSlice X V U W f Q ⋙ finitePerfectAdicAssociated αW ⋙
    SheafOfModules.restrictScalars (((ProEt.topology X).overPullback RingCat.{t + 1} W).map π)

/-- The explicit scalar realization is the general one for the canonical constant scalars and
the limit projection. -/
theorem finitePerfectAdicScalarModules_eq {A : Type t} [CommRing A]
    (d : AdicCoefficientDatum A) (n : ℕ) :
    have := finitePerfectAdicSliceScalar_injective X d W n
    have := finitePerfectAdicSliceScalar_surjective X d W n
    finitePerfectAdicScalarModules X d V U W f n =
      finitePerfectAdicRealizationModules X V U W f (finitePerfectAdicSliceScalar X d W n)
        (completedAdicProjection X d n) := rfl

/-- The object of the pro-etale site of `X` underlying an object of the slice at `W`, seen
through the chart. -/
def finitePerfectAdicChartImage (Z : Over W) : X.ProEt :=
  (MorphismProperty.Over.map ⊤ (show WeaklyEtale V.hom from inferInstance)).obj
    ((MorphismProperty.Over.map ⊤ U.prop).obj
      ((MorphismProperty.Over.map ⊤ (finitePerfectAdicChartArrow_weaklyEtale V U W f)).obj
        ((ProEt.sliceEquiv X W).functor.obj Z)))

/-- An object of the slice at `W` maps to its image through the chart, by the identity of
its underlying scheme. -/
def finitePerfectAdicChartPointIso (Z : Over W) :
    Z.left ≅ finitePerfectAdicChartImage X V U W f Z :=
  MorphismProperty.Over.isoMk (Iso.refl Z.left.left) (by
    have h₁ : Z.hom.left ≫ W.hom = Z.left.hom := MorphismProperty.Over.w Z.hom
    have h₂ : f.left ≫ (finitePerfectAdicChartObject V U).hom = W.hom :=
      MorphismProperty.Over.w f
    change 𝟙 _ ≫ ((Z.hom.left ≫ f.left) ≫ U.hom) ≫ V.hom = Z.left.hom
    rw [Category.id_comp, ← h₁, ← h₂]
    simp [finitePerfectAdicChartObject])

/-- An object of the slice at `W` maps to its image through the chart. -/
abbrev finitePerfectAdicChartPoint (Z : Over W) :
    Z.left ⟶ finitePerfectAdicChartImage X V U W f Z :=
  (finitePerfectAdicChartPointIso X V U W f Z).hom

variable {B : Type t} [CommRing B] (Rc : Sheaf (ProEt.topology X) CommRingCat.{t + 1})
  (φ : adicConstantRing X B ⟶ Rc)
  (αW : (Functor.const (Over W)ᵒᵖ).obj (RingCat.of (ULift.{t + 1} B)) ⟶ ((𝓡 Rc).over W).obj)

/-- The fixed-scalar coordinates of a module sheaf on the chart, restricted to `W` and
transported to the slice. -/
abbrev finitePerfectAdicChartModule (M : SheafOfModules.{t + 1} (𝓡 Rc)) :
    Sheaf ((ProEt.topology X).over W) (ModuleCat.{t + 1} (ULift.{t + 1} B)) :=
  (finitePerfectAdicChartSlice X V U W f (ULift.{t + 1} B)).obj
    ((ProEtale.localizationRestriction (ModuleCat.{t + 1} (ULift.{t + 1} B)) U.hom U.prop).obj
      ((finiteCoefficientSliceRestriction X B Rc φ V).obj M))

/-- The fixed-scalar coordinates of a module sheaf on the chart, restricted to `W`, map to the
restriction of the module sheaf to `W` by restriction along the chart points. -/
def finitePerfectAdicChartRestriction
    (hα : ∀ (Z : Over W) (c : ULift.{t + 1} B),
      ((sheafCompose (ProEt.topology X) (forget₂ CommRingCat.{t + 1} RingCat.{t + 1})).map
        φ).hom.app (op Z.left) ((proEtaleModuleScalarUnit X B).app (op Z.left) c) =
        αW.app (op Z) c)
    (M : SheafOfModules.{t + 1} (𝓡 Rc)) :
    (ProEtale.finiteCoefficientModulePresheaf (Over W) (ULift.{t + 1} B)).obj
        ((sheafToPresheaf _ _).obj (finitePerfectAdicChartModule X V U W f Rc φ M)) ⟶
      (PresheafOfModules.restrictScalars αW).obj
        ((SheafOfModules.forget _).obj ((SheafOfModules.overFunctor (𝓡 Rc) W).obj M)) :=
  PresheafOfModules.homMk (M₁ := (ProEtale.finiteCoefficientModulePresheaf (Over W)
      (ULift.{t + 1} B)).obj
        ((sheafToPresheaf _ _).obj (finitePerfectAdicChartModule X V U W f Rc φ M)))
    (M₂ := (PresheafOfModules.restrictScalars αW).obj
        ((SheafOfModules.forget _).obj ((SheafOfModules.overFunctor (𝓡 Rc) W).obj M)))
    { app := fun Z ↦ M.val.presheaf.map (finitePerfectAdicChartPoint X V U W f Z.unop).op
      naturality := by
        intro Z₁ Z₂ k
        change M.val.presheaf.map _ ≫ M.val.presheaf.map _ =
          M.val.presheaf.map _ ≫ M.val.presheaf.map _
        rw [← Functor.map_comp, ← Functor.map_comp]
        congr 1 }
    (by
      intro Z c x
      change M.val.map (finitePerfectAdicChartPoint X V U W f Z.unop).op
          (((sheafCompose (ProEt.topology X) (forget₂ CommRingCat.{t + 1} RingCat.{t + 1})).map
            φ).hom.app (op (finitePerfectAdicChartImage X V U W f Z.unop))
              ((proEtaleModuleScalarUnit X B).app _ c) •
            (show M.val.obj (op (finitePerfectAdicChartImage X V U W f Z.unop)) from x)) =
        αW.app Z c • (show M.val.obj (op Z.unop.left) from
          M.val.map (finitePerfectAdicChartPoint X V U W f Z.unop).op x)
      rw [PresheafOfModules.map_smul, ← hα]
      congr 1
      rw [← NatTrans.naturality_apply, ← NatTrans.naturality_apply]
      rfl)

variable [Presheaf.IsLocallyInjective ((ProEt.topology X).over W) αW]
  [Presheaf.IsLocallySurjective ((ProEt.topology X).over W) αW]
  (hα : ∀ (Z : Over W) (c : ULift.{t + 1} B),
    ((sheafCompose (ProEt.topology X) (forget₂ CommRingCat.{t + 1} RingCat.{t + 1})).map
      φ).hom.app (op Z.left) ((proEtaleModuleScalarUnit X B).app (op Z.left) c) =
      αW.app (op Z) c)

/-- The associated module sheaf of the fixed-scalar coordinates of a module sheaf, restricted to
`W`, maps to the restriction of the module sheaf, by the adjoint of restriction along the chart
points. -/
def finitePerfectAdicChartAssociated (M : SheafOfModules.{t + 1} (𝓡 Rc)) :
    (finitePerfectAdicAssociated αW).obj (finitePerfectAdicChartModule X V U W f Rc φ M) ⟶
      (SheafOfModules.overFunctor (𝓡 Rc) W).obj M :=
  (PresheafOfModules.sheafificationHomEquiv αW).symm
    (finitePerfectAdicChartRestriction X V U W f Rc φ αW hα M)

/-- Before associated sheafification, the chart comparison is restriction along the chart
points. -/
theorem finitePerfectAdicChartAssociated_unit (M : SheafOfModules.{t + 1} (𝓡 Rc)) :
    toSheafify ((ProEt.topology X).over W)
        ((ProEtale.finiteCoefficientModulePresheaf (Over W) (ULift.{t + 1} B)).obj
          ((sheafToPresheaf _ _).obj (finitePerfectAdicChartModule X V U W f Rc φ M))).presheaf ≫
      (PresheafOfModules.toPresheaf _).map ((SheafOfModules.forget _).map
        (finitePerfectAdicChartAssociated X V U W f Rc φ αW hα M)) =
      (PresheafOfModules.toPresheaf _).map
        (finitePerfectAdicChartRestriction X V U W f Rc φ αW hα M) := by
  have h := PresheafOfModules.toPresheaf_map_sheafificationHomEquiv_def αW
    (finitePerfectAdicChartAssociated X V U W f Rc φ αW hα M)
  unfold finitePerfectAdicChartAssociated at h ⊢
  simp only [Equiv.apply_symm_apply] at h
  exact h.symm

/-- The fixed-scalar coordinates are already a sheaf. -/
instance finitePerfectAdicChartModule_isIso_toSheafify (M : SheafOfModules.{t + 1} (𝓡 Rc)) :
    IsIso (toSheafify ((ProEt.topology X).over W)
      ((ProEtale.finiteCoefficientModulePresheaf (Over W) (ULift.{t + 1} B)).obj
        ((sheafToPresheaf _ _).obj (finitePerfectAdicChartModule X V U W f Rc φ M))).presheaf) := by
  apply isIso_toSheafify
  exact ((sheafCompose ((ProEt.topology X).over W)
    (forget₂ (ModuleCat.{t + 1} (ULift.{t + 1} B)) AddCommGrpCat.{t + 1})).obj
      (finitePerfectAdicChartModule X V U W f Rc φ M)).property

/-- The chart comparison is an isomorphism, since restriction along the chart points is. -/
instance finitePerfectAdicChartAssociated_isIso (M : SheafOfModules.{t + 1} (𝓡 Rc)) :
    IsIso (finitePerfectAdicChartAssociated X V U W f Rc φ αW hα M) := by
  have := finitePerfectAdicChartModule_isIso_toSheafify X V U W f Rc φ M
  have h₂ : IsIso ((PresheafOfModules.toPresheaf _).map
      (finitePerfectAdicChartRestriction X V U W f Rc φ αW hα M)) := by
    rw [NatTrans.isIso_iff_isIso_app]
    intro Z
    change IsIso (M.val.presheaf.map (finitePerfectAdicChartPoint X V U W f Z.unop).op)
    infer_instance
  rw [← finitePerfectAdicChartAssociated_unit] at h₂
  have : IsIso ((PresheafOfModules.toPresheaf _).map ((SheafOfModules.forget _).map
      (finitePerfectAdicChartAssociated X V U W f Rc φ αW hα M))) :=
    IsIso.of_isIso_comp_left (toSheafify _ _) _
  have : IsIso ((SheafOfModules.forget _).map
      (finitePerfectAdicChartAssociated X V U W f Rc φ αW hα M)) :=
    isIso_of_reflects_iso _ (PresheafOfModules.toPresheaf _)
  exact isIso_of_reflects_iso _ (SheafOfModules.forget _)

/-- The chart comparison is natural in the module sheaf. -/
theorem finitePerfectAdicChartAssociated_naturality {M M' : SheafOfModules.{t + 1} (𝓡 Rc)}
    (a : M ⟶ M') :
    (finitePerfectAdicAssociated αW).map ((finitePerfectAdicChartSlice X V U W f _).map
        ((ProEtale.localizationRestriction (ModuleCat.{t + 1} (ULift.{t + 1} B)) U.hom U.prop).map
          ((finiteCoefficientSliceRestriction X B Rc φ V).map a))) ≫
        finitePerfectAdicChartAssociated X V U W f Rc φ αW hα M' =
      finitePerfectAdicChartAssociated X V U W f Rc φ αW hα M ≫
        (SheafOfModules.overFunctor (𝓡 Rc) W).map a := by
  have := finitePerfectAdicChartModule_isIso_toSheafify X V U W f Rc φ M
  apply (SheafOfModules.forget _).map_injective
  apply (PresheafOfModules.toPresheaf _).map_injective
  apply (cancel_epi (toSheafify _ _)).1
  simp only [Functor.map_comp]
  rw [← Category.assoc, ← Category.assoc, finitePerfectAdicChartAssociated_unit,
    finitePerfectAdicAssociated_map_unit, Category.assoc, finitePerfectAdicChartAssociated_unit]
  ext Z x
  change M'.val.map (finitePerfectAdicChartPoint X V U W f Z.unop).op (a.val.app _ x) =
    a.val.app (op Z.unop.left) (M.val.map (finitePerfectAdicChartPoint X V U W f Z.unop).op x)
  exact (PresheafOfModules.naturality_apply a.val (finitePerfectAdicChartPoint X V U W f Z.unop).op
    x).symm

variable {T : Sheaf (ProEt.topology X) RingCat.{t + 1}} (π : T ⟶ 𝓡 Rc)

/-- The scalar realization of the fixed-scalar coordinates of a module sheaf on the chart is the
restriction of the module sheaf to `W`, with scalars restricted along `π`. -/
def finitePerfectAdicRealizationIsoApp (M : SheafOfModules.{t + 1} (𝓡 Rc)) :
    (finitePerfectAdicRealizationModules X V U W f αW π).obj
        ((ProEtale.upperStar (ModuleCat.{t + 1} (ULift.{t + 1} B)) U.hom).obj
          ((finiteCoefficientSliceRestriction X B Rc φ V).obj M)) ≅
      (SheafOfModules.overFunctor T W).obj ((SheafOfModules.restrictScalars π).obj M) :=
  (finitePerfectAdicRealizationModules X V U W f αW π).mapIso
      ((ProEtale.upperStarIsoLocalizationRestriction (ModuleCat.{t + 1} (ULift.{t + 1} B))
        U.hom U.prop).app ((finiteCoefficientSliceRestriction X B Rc φ V).obj M)) ≪≫
    (SheafOfModules.restrictScalars (((ProEt.topology X).overPullback RingCat.{t + 1} W).map
      π)).mapIso (asIso (finitePerfectAdicChartAssociated X V U W f Rc φ αW hα M)) ≪≫
    Iso.refl _

/-- The scalar realization of the fixed-scalar coordinates on the chart is restriction to `W`,
with scalars restricted along `π`. -/
def finitePerfectAdicRealizationIso :
    finiteCoefficientSliceRestriction X B Rc φ V ⋙
        ProEtale.upperStar (ModuleCat.{t + 1} (ULift.{t + 1} B)) U.hom ⋙
          finitePerfectAdicRealizationModules X V U W f αW π ≅
      SheafOfModules.restrictScalars π ⋙ SheafOfModules.overFunctor T W :=
  NatIso.ofComponents (finitePerfectAdicRealizationIsoApp X V U W f Rc φ αW hα π) (by
    intro M M' a
    let Rz := finitePerfectAdicRealizationModules X V U W f αW π
    let u := ProEtale.upperStarIsoLocalizationRestriction (ModuleCat.{t + 1} (ULift.{t + 1} B))
      U.hom U.prop
    let sR := finiteCoefficientSliceRestriction X B Rc φ V
    let ρ := SheafOfModules.restrictScalars
      (((ProEt.topology X).overPullback RingCat.{t + 1} W).map π)
    have hu := u.hom.naturality (sR.map a)
    have hs := finitePerfectAdicChartAssociated_naturality X V U W f Rc φ αW hα a
    change Rz.map ((ProEtale.upperStar _ U.hom).map (sR.map a)) ≫
        (Rz.map (u.hom.app (sR.obj M')) ≫
          ρ.map (finitePerfectAdicChartAssociated X V U W f Rc φ αW hα M') ≫ 𝟙 _) =
      (Rz.map (u.hom.app (sR.obj M)) ≫
          ρ.map (finitePerfectAdicChartAssociated X V U W f Rc φ αW hα M) ≫ 𝟙 _) ≫
        (SheafOfModules.overFunctor T W).map ((SheafOfModules.restrictScalars π).map a)
    rw [← Rz.map_comp_assoc, hu, Rz.map_comp_assoc, Category.assoc]
    congr 1
    change ρ.map ((finitePerfectAdicAssociated αW).map
      ((finitePerfectAdicChartSlice X V U W f _).map
        ((ProEtale.localizationRestriction _ U.hom U.prop).map (sR.map a)))) ≫ _ = _
    rw [← ρ.map_comp_assoc, hs, ρ.map_comp_assoc]
    rfl)

end Realization

private theorem finitePerfectAdic_unit_square {C : Type*} [Category* C]
    {A B A' B' B'' D E : C} (u : A ⟶ A') [Epi u]
    {v : B ⟶ B'} {w : B ⟶ B''} {a : A' ⟶ B'} {c : B' ⟶ B''}
    {b : B'' ⟶ E} {d : A' ⟶ D} {e : D ⟶ E} {m : A ⟶ B}
    {r : A ⟶ D} {s : B ⟶ E}
    (hR : u ≫ a = m ≫ v) (hC : v ≫ c = w) (h₀ : w ≫ b = s)
    (h₁ : u ≫ d = r) (h : m ≫ s = r ≫ e) : a ≫ c ≫ b = d ≫ e := by
  apply (cancel_epi u).1
  calc
    u ≫ a ≫ c ≫ b = m ≫ v ≫ c ≫ b := by
      rw [← Category.assoc u a, hR, Category.assoc]
    _ = m ≫ w ≫ b := by rw [← Category.assoc v c, hC]
    _ = m ≫ s := by rw [h₀]
    _ = r ≫ e := h
    _ = u ≫ d ≫ e := by rw [← h₁, Category.assoc]

section Square

set_option hygiene false in
local notation "𝓡" R => (sheafCompose (ProEt.topology X)
  (forget₂ CommRingCat.{t + 1} RingCat.{t + 1})).obj R

variable (X : Scheme.{t}) (V : X.Etale) (U : V.left.ProEt) (W : X.ProEt)
  (f : W ⟶ finitePerfectAdicChartObject V U)
  {B₁ B₀ : Type t} [CommRing B₁] [CommRing B₀] (q : B₁ →+* B₀)
  {Rc₁ Rc₀ : Sheaf (ProEt.topology X) CommRingCat.{t + 1}} (s : Rc₁ ⟶ Rc₀)
  (φ₁ : adicConstantRing X B₁ ⟶ Rc₁) (φ₀ : adicConstantRing X B₀ ⟶ Rc₀)
  (αW₁ : (Functor.const (Over W)ᵒᵖ).obj (RingCat.of (ULift.{t + 1} B₁)) ⟶ ((𝓡 Rc₁).over W).obj)
  (αW₀ : (Functor.const (Over W)ᵒᵖ).obj (RingCat.of (ULift.{t + 1} B₀)) ⟶ ((𝓡 Rc₀).over W).obj)
  [Presheaf.IsLocallyInjective ((ProEt.topology X).over W) αW₁]
  [Presheaf.IsLocallySurjective ((ProEt.topology X).over W) αW₁]
  [Presheaf.IsLocallyInjective ((ProEt.topology X).over W) αW₀]
  [Presheaf.IsLocallySurjective ((ProEt.topology X).over W) αW₀]
  (hα₁ : ∀ (Z : Over W) (c : ULift.{t + 1} B₁),
    ((sheafCompose (ProEt.topology X) (forget₂ CommRingCat.{t + 1} RingCat.{t + 1})).map
      φ₁).hom.app (op Z.left) ((proEtaleModuleScalarUnit X B₁).app (op Z.left) c) =
      αW₁.app (op Z) c)
  (hα₀ : ∀ (Z : Over W) (c : ULift.{t + 1} B₀),
    ((sheafCompose (ProEt.topology X) (forget₂ CommRingCat.{t + 1} RingCat.{t + 1})).map
      φ₀).hom.app (op Z.left) ((proEtaleModuleScalarUnit X B₀).app (op Z.left) c) =
      αW₀.app (op Z) c)
  (p : (𝓡 Rc₁) ⟶ (𝓡 Rc₀))
  (hps : (sheafCompose (ProEt.topology X) (forget₂ CommRingCat.{t + 1} RingCat.{t + 1})).map s = p)
  (hαp : ∀ Z, αW₁.app Z ≫ (((ProEt.topology X).overPullback RingCat.{t + 1} W).map p).hom.app Z =
    RingCat.ofHom (RingHom.ulift q) ≫ αW₀.app Z)
  {T : Sheaf (ProEt.topology X) RingCat.{t + 1}} (π₁ : T ⟶ 𝓡 Rc₁) (π₀ : T ⟶ 𝓡 Rc₀)
  (hπ : π₁ ≫ (sheafCompose (ProEt.topology X) (forget₂ CommRingCat.{t + 1} RingCat.{t + 1})).map
    s = π₀)
  (coh : sheafCompose (ProEt.topology U.left)
      (ModuleCat.restrictScalars.{t + 1} (RingHom.ulift q)) ⋙
      finitePerfectAdicRealizationModules X V U W f αW₁ π₁ ≅
    finitePerfectAdicRealizationModules X V U W f αW₀ π₀)
  (hcoh : ∀ G : Sheaf (ProEt.topology U.left) (ModuleCat.{t + 1} (ULift.{t + 1} B₀)),
    (PresheafOfModules.toPresheaf _).map ((SheafOfModules.forget _).map (coh.hom.app G)) =
      (PresheafOfModules.toPresheaf _).map ((SheafOfModules.forget _).map
        ((finitePerfectAdicAssociatedCoherence αW₁ αW₀ (RingHom.ulift.{t + 1, t + 1} q)
          (((ProEt.topology X).overPullback RingCat.{t + 1} W).map p) hαp).hom.app
          ((finitePerfectAdicChartSlice X V U W f _).obj G))))
  {M₁ : SheafOfModules.{t + 1} (𝓡 Rc₁)} {M₀ : SheafOfModules.{t + 1} (𝓡 Rc₀)}
  (g : M₁ ⟶ (SheafOfModules.restrictScalars
    ((sheafCompose (ProEt.topology X) (forget₂ CommRingCat.{t + 1} RingCat.{t + 1})).map
      s)).obj M₀)
  (δ : (finiteCoefficientSliceRestriction X B₁ Rc₁ φ₁ V).obj M₁ ⟶
    (sheafCompose (ProEt.topology V.left)
      (ModuleCat.restrictScalars.{t + 1} (RingHom.ulift q))).obj
        ((finiteCoefficientSliceRestriction X B₀ Rc₀ φ₀ V).obj M₀))
  (hδ : ∀ (U' : V.left.ProEt) x, δ.hom.app (op U') x =
    g.val.app (op (finitePerfectAdicChartObject V U')) x)

-- The explicit square compares two presentations of the realization on the slice.
include hps hαp hcoh hδ in
/-- The explicit part of the realization square, after replacing inverse image by restriction:
both composites restrict `g` to `W`. -/
theorem finitePerfectAdicRealization_square_explicit :
    (finitePerfectAdicRealizationModules X V U W f αW₁ π₁).map
        ((ProEtale.localizationRestriction _ U.hom U.prop).map δ) ≫
      coh.hom.app ((ProEtale.localizationRestriction _ U.hom U.prop).obj
        ((finiteCoefficientSliceRestriction X B₀ Rc₀ φ₀ V).obj M₀)) ≫
      (SheafOfModules.restrictScalars (((ProEt.topology X).overPullback RingCat.{t + 1} W).map
        π₀)).map (finitePerfectAdicChartAssociated X V U W f Rc₀ φ₀ αW₀ hα₀ M₀) =
    (SheafOfModules.restrictScalars (((ProEt.topology X).overPullback RingCat.{t + 1} W).map
        π₁)).map (finitePerfectAdicChartAssociated X V U W f Rc₁ φ₁ αW₁ hα₁ M₁) ≫
      (SheafOfModules.overFunctor T W).map ((SheafOfModules.restrictScalars π₁).map g ≫
        (finitePerfectAdicRestrictComp π₁ _ π₀ hπ M₀).hom) := by
  subst hps
  have hR := finitePerfectAdicAssociated_map_unit αW₁ ((finitePerfectAdicChartSlice X V U W f _).map
    ((ProEtale.localizationRestriction _ U.hom U.prop).map δ))
  have hC := finitePerfectAdicAssociatedCoherence_unit αW₁ αW₀ (RingHom.ulift q)
    (((ProEt.topology X).overPullback RingCat.{t + 1} W).map
      ((sheafCompose (ProEt.topology X) (forget₂ CommRingCat.{t + 1} RingCat.{t + 1})).map s)) hαp
    ((finitePerfectAdicChartSlice X V U W f _).obj ((ProEtale.localizationRestriction _ U.hom
      U.prop).obj ((finiteCoefficientSliceRestriction X B₀ Rc₀ φ₀ V).obj M₀)))
  have h₀ := finitePerfectAdicChartAssociated_unit X V U W f Rc₀ φ₀ αW₀ hα₀ M₀
  have h₁ := finitePerfectAdicChartAssociated_unit X V U W f Rc₁ φ₁ αW₁ hα₁ M₁
  apply (SheafOfModules.forget _).map_injective
  apply (PresheafOfModules.toPresheaf _).map_injective
  simp only [Functor.map_comp]
  rw [hcoh]
  refine finitePerfectAdic_unit_square (toSheafify _ _) hR hC h₀ h₁ ?_
  ext Z x
  change M₀.val.map (finitePerfectAdicChartPoint X V U W f Z.unop).op
      (δ.hom.app (op ((MorphismProperty.Over.map ⊤ U.prop).obj
        ((MorphismProperty.Over.map ⊤ (finitePerfectAdicChartArrow_weaklyEtale V U W f)).obj
          ((ProEt.sliceEquiv X W).functor.obj Z.unop)))) x) =
    g.val.app (op Z.unop.left) (M₁.val.map (finitePerfectAdicChartPoint X V U W f Z.unop).op x)
  rw [hδ]
  exact (PresheafOfModules.naturality_apply g.val (finitePerfectAdicChartPoint X V U W f Z.unop).op
    x).symm

-- Unfolding the realization isomorphisms requires unifying two presentations of the slice.
include hps hαp hcoh hδ in
/-- The scalar realizations of consecutive fixed-scalar coordinates carry a semilinear map of
coordinates induced by `g` to the restriction of `g` to `W`, compatibly with the inverse-image
comparison and the ordinary scalar compositor. -/
theorem finitePerfectAdicRealization_square :
    (finitePerfectAdicRealizationModules X V U W f αW₁ π₁).map
        ((ProEtale.upperStar (ModuleCat.{t + 1} (ULift.{t + 1} B₁)) U.hom).map δ ≫
          (finitePerfectAdicPullbackRestrictComparison U.hom
            (RingHom.ulift.{t + 1, t + 1} q)).hom.app
            ((finiteCoefficientSliceRestriction X B₀ Rc₀ φ₀ V).obj M₀)) ≫
      coh.hom.app ((ProEtale.upperStar (ModuleCat.{t + 1} (ULift.{t + 1} B₀)) U.hom).obj
        ((finiteCoefficientSliceRestriction X B₀ Rc₀ φ₀ V).obj M₀)) ≫
      (finitePerfectAdicRealizationIso X V U W f Rc₀ φ₀ αW₀ hα₀ π₀).hom.app M₀ =
    (finitePerfectAdicRealizationIso X V U W f Rc₁ φ₁ αW₁ hα₁ π₁).hom.app M₁ ≫
      (SheafOfModules.overFunctor T W).map ((SheafOfModules.restrictScalars π₁).map g ≫
        (finitePerfectAdicRestrictComp π₁ _ π₀ hπ M₀).hom) := by
  let u₁ := ProEtale.upperStarIsoLocalizationRestriction (ModuleCat.{t + 1} (ULift.{t + 1} B₁))
    U.hom U.prop
  let u₀ := ProEtale.upperStarIsoLocalizationRestriction (ModuleCat.{t + 1} (ULift.{t + 1} B₀))
    U.hom U.prop
  let Rz₁ := finitePerfectAdicRealizationModules X V U W f αW₁ π₁
  let Rz₀ := finitePerfectAdicRealizationModules X V U W f αW₀ π₀
  let G₀ := (finiteCoefficientSliceRestriction X B₀ Rc₀ φ₀ V).obj M₀
  let ρ₁ := SheafOfModules.restrictScalars
    (((ProEt.topology X).overPullback RingCat.{t + 1} W).map π₁)
  let ρ₀ := SheafOfModules.restrictScalars
    (((ProEt.topology X).overPullback RingCat.{t + 1} W).map π₀)
  have hL1 : (finitePerfectAdicPullbackRestrictComparison U.hom
      (RingHom.ulift.{t + 1, t + 1} q)).hom.app G₀ ≫
      (sheafCompose (ProEt.topology U.left)
        (ModuleCat.restrictScalars.{t + 1} (RingHom.ulift.{t + 1, t + 1} q))).map (u₀.hom.app G₀) =
      u₁.hom.app ((sheafCompose (ProEt.topology V.left)
        (ModuleCat.restrictScalars.{t + 1} (RingHom.ulift.{t + 1, t + 1} q))).obj G₀) :=
    finitePerfectAdic_pullbackRestrict_upperStarIso U.hom U.prop _ G₀
  have hn := coh.hom.naturality (u₀.hom.app G₀)
  have hu := u₁.hom.naturality δ
  have hE := finitePerfectAdicRealization_square_explicit X V U W f q s φ₁ φ₀ αW₁ αW₀ hα₁ hα₀
    p hps hαp π₁ π₀ hπ coh hcoh g δ hδ
  change Rz₁.map ((ProEtale.upperStar _ U.hom).map δ ≫
      (finitePerfectAdicPullbackRestrictComparison U.hom
            (RingHom.ulift.{t + 1, t + 1} q)).hom.app G₀) ≫
      coh.hom.app ((ProEtale.upperStar _ U.hom).obj G₀) ≫
      (Rz₀.map (u₀.hom.app G₀) ≫
        ρ₀.map (finitePerfectAdicChartAssociated X V U W f Rc₀ φ₀ αW₀ hα₀ M₀) ≫ 𝟙 _) =
    (Rz₁.map (u₁.hom.app _) ≫
        ρ₁.map (finitePerfectAdicChartAssociated X V U W f Rc₁ φ₁ αW₁ hα₁ M₁) ≫ 𝟙 _) ≫ _
  simp only [Category.comp_id, Category.assoc]
  rw [← reassoc_of% hn, ← Rz₁.map_comp_assoc, Category.assoc, hL1, hu, Rz₁.map_comp_assoc, hE]

include hps hαp hcoh hδ in
/-- The realization square, composed with identifications of the restrictions of the module
sheaves and a compatible map between them. -/
theorem finitePerfectAdicRealization_square_comp {Y₁ Y₀ : SheafOfModules.{t + 1} T}
    (C₁ : (SheafOfModules.restrictScalars π₁).obj M₁ ≅ Y₁)
    (C₀ : (SheafOfModules.restrictScalars π₀).obj M₀ ≅ Y₀) (τ : Y₁ ⟶ Y₀)
    (hC : (SheafOfModules.restrictScalars π₁).map g ≫
        (finitePerfectAdicRestrictComp π₁ _ π₀ hπ M₀).hom ≫ C₀.hom = C₁.hom ≫ τ) :
    (finitePerfectAdicRealizationModules X V U W f αW₁ π₁).map
        ((ProEtale.upperStar (ModuleCat.{t + 1} (ULift.{t + 1} B₁)) U.hom).map δ ≫
          (finitePerfectAdicPullbackRestrictComparison U.hom
            (RingHom.ulift.{t + 1, t + 1} q)).hom.app
            ((finiteCoefficientSliceRestriction X B₀ Rc₀ φ₀ V).obj M₀)) ≫
      coh.hom.app ((ProEtale.upperStar (ModuleCat.{t + 1} (ULift.{t + 1} B₀)) U.hom).obj
        ((finiteCoefficientSliceRestriction X B₀ Rc₀ φ₀ V).obj M₀)) ≫
      (finitePerfectAdicRealizationIso X V U W f Rc₀ φ₀ αW₀ hα₀ π₀).hom.app M₀ ≫
        (SheafOfModules.overFunctor T W).map C₀.hom =
    ((finitePerfectAdicRealizationIso X V U W f Rc₁ φ₁ αW₁ hα₁ π₁).hom.app M₁ ≫
        (SheafOfModules.overFunctor T W).map C₁.hom) ≫
      (SheafOfModules.overFunctor T W).map τ := by
  have h := finitePerfectAdicRealization_square X V U W f q s φ₁ φ₀ αW₁ αW₀ hα₁ hα₀ p hps hαp
    π₁ π₀ hπ coh hcoh g δ hδ
  rw [reassoc_of% h, Category.assoc, ← Functor.map_comp, ← Functor.map_comp, Category.assoc, hC]

end Square

end AlgebraicGeometry.Scheme
