/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Etale.EtaleAmbientAdjointLocality
public import WeilConjectures.AlgebraicGeometry.Etale.Compact.EtaleCompactSupportGraphDerivedIsoSupplement
public import WeilConjectures.AlgebraicGeometry.DerivedCategories
import WeilConjectures.AlgebraicGeometry.Etale.Compact.EtaleCompactSupportNormalization
import WeilConjectures.AlgebraicGeometry.Unbounded.UnboundedEtaleCompactSupportComparisonsSupplement

/-! # Graph-normalized chart models

Source: blueprint main-20261015, sec-smooth-purity/sk-lem-sp-reduction/
sk-lem-sp-reduction-exceptional.proof.md, Charts, specified left identification;
Stacks Project Tags 0F7I, 0F7J, 0F7K
(blueprint: lem-sp-chart-normalized-model-identification).

The helper isomorphisms assemble existing comparison maps. The theorem identifies these
actual maps on bounded-below inputs and supplies the simultaneous graph-normalized datum.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry.Etale

/-- Canonical composition on three independently specified compactifications: compare the
first model with the restricted closure, apply the proper/open tower, and compare the result.
Source: Stacks Project Tags 0F7J and 0F7B; blueprint Charts, specified left identification
(blueprint: lem-sp-chart-normalized-model-identification). -/
noncomputable def chartModelComposition
    (R : Type (u + 1)) [CommRing R] [Finite R]
    {U V Y : Scheme.{u}} (e : U ⟶ V) (f : V ⟶ Y) [QuasiCompact e]
    [QuasiCompact (e ≫ f)] (ce : Compactification e) (cf : Compactification f)
    (cg : Compactification (e ≫ f)) :
    rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} R) ce ⋙
        rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} R) cf ≅
      rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} R) cg :=
  Functor.isoWhiskerRight
      (rightDerivedLowerShriekOfCompactificationIso R ce (cg.ofComp cf).restrict) _ ≪≫
    rightDerivedLowerShriekOfCompactificationCompIso R cf (cg.ofComp cf) ≪≫
    rightDerivedLowerShriekOfCompactificationIso R (cf.comp (cg.ofComp cf)) cg

/-- The displayed map lambda: the inverse graph-normalized etale comparison, followed by
canonical compact-support composition on the three chosen models.
Source: blueprint Charts, specified left identification; Stacks Project Tag 0F7J
(blueprint: lem-sp-chart-normalized-model-identification). -/
noncomputable def chartNormalizedModelComparison
    (R : Type (u + 1)) [CommRing R] [Finite R]
    (N : EtaleCompactSupportNormalization R)
    {U V Y : Scheme.{u}} [IsNoetherian U] [IsNoetherian V]
    (e : U ⟶ V) (f : V ⟶ Y) [Etale e] [IsSeparated e] [QuasiCompact e]
    [QuasiCompact (e ≫ f)] (ce : Compactification e) (cf : Compactification f)
    (cg : Compactification (e ≫ f)) :
    (etaleLowerShriek (ModuleCat.{u + 1} R) e inferInstance).mapDerivedCategory ⋙
        rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} R) cf ≅
      rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} R) cg :=
  Functor.isoWhiskerRight (N.comparison e ce).symm _ ≪≫
    chartModelComposition R e f ce cf cg

private theorem chart_refinement_normalization
    (R : Type (u + 1)) [CommRing R] [Finite R]
    (N : EtaleCompactSupportNormalization R)
    {U V : Scheme.{u}} [IsNoetherian U] [IsNoetherian V]
    (e : U ⟶ V) [Etale e] [IsSeparated e]
    {c d : Compactification e} (r : c.Refinement d) :
    (rightDerivedLowerShriekOfCompactificationIso R d c).hom ≫
      (N.comparison e c).hom = (N.comparison e d).hom := by
  have : IsLocallyNoetherian d.Z := LocallyOfFiniteType.isLocallyNoetherian d.g
  have : CompactSpace d.Z := QuasiCompact.compactSpace_of_compactSpace d.g
  rw [unboundedEtaleCompactSupport_refinement_normalization R e r N]
  simpa only [unboundedEtaleRefinementOpenComparison, Iso.symm_hom, Category.assoc] using
    N.refinement e c d r

private theorem chart_pairwise_normalization
    (R : Type (u + 1)) [CommRing R] [Finite R]
    (N : EtaleCompactSupportNormalization R)
    {U V : Scheme.{u}} [IsNoetherian U] [IsNoetherian V]
    (e : U ⟶ V) [Etale e] [IsSeparated e]
    (c d : Compactification e) :
    (rightDerivedLowerShriekOfCompactificationIso R c d).hom ≫
      (N.comparison e d).hom = (N.comparison e c).hom := by
  have hc := chart_refinement_normalization R N e (Compactification.infFst c d)
  have hd := chart_refinement_normalization R N e (Compactification.infSnd c d)
  rw [← hd, ← Category.assoc]
  have h := (unboundedEtaleCompactSupport_comparison_coherence R e).2 c d
    (Compactification.inf c d)
  rw [← Iso.trans_hom, h]
  exact hc

private theorem chart_pairwise_inverse
    (R : Type (u + 1)) [CommRing R] [Finite R]
    (N : EtaleCompactSupportNormalization R)
    {U V : Scheme.{u}} [IsNoetherian U] [IsNoetherian V]
    (e : U ⟶ V) [Etale e] [IsSeparated e]
    (c d : Compactification e) :
    (N.comparison e c).inv ≫ (rightDerivedLowerShriekOfCompactificationIso R c d).hom =
      (N.comparison e d).inv := by
  apply (cancel_mono (N.comparison e d).hom).1
  rw [Category.assoc, chart_pairwise_normalization]
  simp

private theorem chart_pairwise_symm
    (R : Type (u + 1)) [CommRing R] [Finite R]
    {U V : Scheme.{u}} [IsNoetherian U] [IsNoetherian V]
    (e : U ⟶ V) [IsSeparated e] [LocallyOfFiniteType e] [QuasiCompact e]
    (c d : Compactification e) :
    (rightDerivedLowerShriekOfCompactificationIso R c d).symm =
      rightDerivedLowerShriekOfCompactificationIso R d c := by
  obtain ⟨hi, ht⟩ := unboundedEtaleCompactSupport_comparison_coherence R e
  have h := ht c d c
  rw [hi] at h
  apply Iso.ext
  apply (cancel_epi (rightDerivedLowerShriekOfCompactificationIso R c d).hom).1
  exact (Iso.hom_inv_id _).trans (congrArg Iso.hom h).symm

private theorem chart_normalized_tower
    {C D E : Type*} [Category C] [Category D] [Category E]
    {F F' S : C ⥤ D} {G G' : D ⥤ E} {H H' : C ⥤ E}
    (c : F ≅ S) (a : F' ≅ F) (b : G' ≅ G) (d : H' ≅ H)
    (t : F' ⋙ G' ≅ H') (k : F ⋙ G ≅ H)
    (hk : k.hom = NatTrans.hcomp a.inv b.inv ≫ t.hom ≫ d.hom) (K : C) :
    G'.map (c.inv.app K ≫ a.inv.app K) ≫ t.hom.app K ≫ d.hom.app K =
      b.hom.app (S.obj K) ≫ G.map (c.inv.app K) ≫ k.hom.app K := by
  rw [hk]
  simp only [Functor.NatTrans.hcomp_eq_whiskerLeft_comp_whiskerRight, NatTrans.comp_app,
    Functor.whiskerLeft_app, Functor.whiskerRight_app, Functor.map_comp, Category.assoc]
  rw [← b.hom.naturality_assoc]
  simp

private theorem chart_comparison_ambient
    (R : Type (u + 1)) [CommRing R] [Finite R]
    (N : EtaleCompactSupportNormalization R)
    {U V Y : Scheme.{u}} [IsNoetherian U] [IsNoetherian V] [IsNoetherian Y]
    (e : U ⟶ V) (f : V ⟶ Y) [Etale e] [IsSeparated e]
    [QuasiCompact e] [QuasiCompact (e ≫ f)]
    (ce : Compactification e) (cf : Compactification f)
    (cg : Compactification (e ≫ f)) :
    chartNormalizedModelComparison R N e f ce cf cg =
      etaleAmbientLeftComparison R N e f cf cg := by
  apply Iso.ext
  ext K
  simp only [chartNormalizedModelComparison, chartModelComposition, etaleAmbientLeftComparison,
    Iso.trans_hom, Iso.symm_hom, Functor.isoWhiskerRight_hom, NatTrans.comp_app,
    Functor.whiskerRight_app]
  rw [← Functor.map_comp_assoc]
  rw [show (N.comparison e ce).inv.app K ≫
      (rightDerivedLowerShriekOfCompactificationIso R ce (cg.ofComp cf).restrict).hom.app K =
      (N.comparison e (cg.ofComp cf).restrict).inv.app K from
    NatTrans.congr_app (chart_pairwise_inverse R N e ce (cg.ofComp cf).restrict) K]

private theorem chart_comparison_formula
    (R : Type (u + 1)) [CommRing R] [Finite R]
    (N : EtaleCompactSupportNormalization R)
    {U V Y : Scheme.{u}} [IsNoetherian U] [IsNoetherian V] [IsNoetherian Y]
    (e : U ⟶ V) (f : V ⟶ Y) [Etale e] [IsSeparated e] [QuasiCompact e]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    [HasCompactification e] [HasCompactification f] [HasCompactification (e ≫ f)]
    (ce : Compactification e) (cf : Compactification f)
    (cg : Compactification (e ≫ f))
    (K : DerivedCategory (Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} R))) :
    (chartNormalizedModelComparison R N e f ce cf cg).hom.app K =
      (rightDerivedLowerShriekIso R cf).hom.app
          ((etaleLowerShriek (ModuleCat.{u + 1} R) e inferInstance).mapDerivedCategory.obj K) ≫
        (rightDerivedLowerShriek (ModuleCat.{u + 1} R) f).map
          ((N.comparison e (HasCompactification.compactification e)).inv.app K) ≫
        (unboundedEtaleLowerShriekCompIso R e f).hom.app K ≫
        (rightDerivedLowerShriekOfCompactificationIso R
          (HasCompactification.compactification (e ≫ f)) cg).hom.app K := by
  let a := cg.ofComp cf
  let c := HasCompactification.compactification e
  let d := HasCompactification.compactification (e ≫ f)
  have hn := NatTrans.congr_app (chart_pairwise_inverse R N e c a.restrict) K
  rw [← chart_pairwise_symm R e a.restrict c] at hn
  have ht := chart_normalized_tower
    (N.comparison e c) (rightDerivedLowerShriekIso R a.restrict)
    (rightDerivedLowerShriekIso R cf) (rightDerivedLowerShriekIso R (cf.comp a))
    (rightDerivedLowerShriekOfCompactificationCompIso R cf a)
    (unboundedEtaleLowerShriekCompIso R e f)
    (unboundedEtaleLowerShriekCompIso_tower R e f cf a) K
  have hg := congrArg (fun z ↦ z.hom.app K)
    ((unboundedEtaleCompactSupport_comparison_coherence R (e ≫ f)).2 (cf.comp a) d cg)
  rw [chart_comparison_ambient]
  simp only [etaleAmbientLeftComparison, Iso.trans_hom, Iso.symm_hom,
    Functor.isoWhiskerRight_hom, NatTrans.comp_app, Functor.whiskerRight_app]
  simp only [Iso.trans_hom, NatTrans.comp_app] at hg
  rw [← hn, ← hg]
  simpa only [rightDerivedLowerShriekIso, NatTrans.comp_app, Iso.symm_hom,
    Category.assoc] using congrArg (fun z ↦ z ≫
    (rightDerivedLowerShriekOfCompactificationIso R d cg).hom.app K) ht

end AlgebraicGeometry.Etale
