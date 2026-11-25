/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.EtaleSheaves
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs
import WeilConjectures.AlgebraicGeometry.EtaleSetInverseImageStalkGerm
import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtaleOver
import WeilConjectures.Mathlib.CategoryTheory.Sites.ConstantSheafEquivalence

/-!
# Descent of lissity along a surjective etale map

Source: smooth purity blueprint, final paragraph of
`lem-weil-pbc-finite-pushforward-generic-constructible`.
(blueprint: lem-weil-pbc-lisse-etale-surjective-descent).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme

private noncomputable def overSetIsoRestriction {X : Scheme.{u}} (U : X.Etale)
    (F : Sheaf X.smallEtaleTopology (Type (u + 1))) :
    (Etale.overSheafEquiv U (Type (u + 1))).functor.obj (F.over U) ≅
      (AlgebraicGeometry.Etale.localizationRestriction
        (Type (u + 1)) U.hom U.prop).obj F :=
  (fullyFaithfulSheafToPresheaf _ _).preimageIso
    (Functor.isoWhiskerRight (NatIso.op (Etale.etaleToOverCompForgetIso U).symm) F.obj)

private theorem isConstant_over_iff_setRestriction {X : Scheme.{u}} (U : X.Etale)
    (F : Sheaf X.smallEtaleTopology (Type (u + 1))) :
    (F.over U).IsConstant (X.smallEtaleTopology.over U) ↔
      ((AlgebraicGeometry.Etale.localizationRestriction
        (Type (u + 1)) U.hom U.prop).obj F).IsConstant U.left.smallEtaleTopology := by
  rw [← Sheaf.isConstant_sheafCongr_functor_iff
    (J := X.smallEtaleTopology.over U) (K := U.left.smallEtaleTopology)
    (Etale.overEquiv U) Over.mkIdTerminal (F.over U)]
  constructor
  · intro h
    have : ((Etale.overSheafEquiv U (Type (u + 1))).functor.obj
        (F.over U)).IsConstant U.left.smallEtaleTopology := h
    exact Sheaf.isConstant_congr _ (overSetIsoRestriction U F)
  · intro h
    have : ((Etale.overSheafEquiv U (Type (u + 1))).functor.obj
        (F.over U)).IsConstant U.left.smallEtaleTopology := h
    exact Sheaf.isConstant_congr _ (overSetIsoRestriction U F).symm

/-- Lissity of a set sheaf descends through a surjective etale cover.

Source: smooth purity blueprint, `sk-prop-sf-cbc`, proof of
`lem-weil-pbc-finite-pushforward-generic-constructible`, final paragraph;
step 5 of `lem-weil-pbc-finite-map-generic-lisse-preservation`.
(blueprint: lem-weil-pbc-lisse-etale-surjective-descent).

Proof: Choose an etale cover of T trivializing p inverse image F. Compose its
members with p. Surjectivity makes the composite family a cover of Y, and
etaleness is preserved by composition. Restriction of p inverse image F to each
member is canonically the restriction of F to that member viewed over Y;
this follows from the equivalence between the localized small etale site and
the small etale site of the member. Transport each constant trivialization
through this equivalence. This proves local constancy of F. For any geometric
point s over Y, surjectivity supplies a point of T above its image. Because p is
etale and the field of s is separably closed, s lifts to a geometric point t
of T with t followed by p equal to s. The inverse-image stalk isomorphism
identifies the stalk of F at s with the stalk of p inverse image F at t, which
is finite by hypothesis. Thus F has finite geometric stalks. For an empty base
the cover and the stalk conditions are vacuous, so the same argument applies. -/
theorem isLisseEtaleSheafOfSets_of_etale_surjective_pullback
    {Y T : Scheme.{u}} (p : T ⟶ Y) [Etale p] [Surjective p]
    (F : Sheaf Y.smallEtaleTopology (Type (u + 1)))
    (hF : IsLisseEtaleSheafOfSets ((etaleSetPullback p).obj F)) :
    IsLisseEtaleSheafOfSets F := by
  classical
  have : JointlySurjective etalePrecoverage :=
    inferInstanceAs (JointlySurjective (precoverage @AlgebraicGeometry.Etale))
  obtain ⟨𝒰, h𝒰⟩ := hF.1
  let a₁ := Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
    (MorphismProperty.Over.pullback @AlgebraicGeometry.Etale ⊤ p) (Type (u + 1))
    (Y.smallGrothendieckTopology @AlgebraicGeometry.Etale)
    (T.smallGrothendieckTopology @AlgebraicGeometry.Etale)
  let siteAdj := MorphismProperty.Over.mapPullbackAdj
    @AlgebraicGeometry.Etale ⊤ p inferInstance trivial
  let a₂ := siteAdj.sheafPushforwardContinuous (E := Type (u + 1))
    (T.smallGrothendieckTopology @AlgebraicGeometry.Etale)
    (Y.smallGrothendieckTopology @AlgebraicGeometry.Etale)
  let ρ : etaleSetPullback p ≅ AlgebraicGeometry.Etale.localizationRestriction
      (Type (u + 1)) p inferInstance := a₁.leftAdjointUniq a₂
  let 𝒱 : Cover.{u} etalePrecoverage Y :=
    Cover.mkOfCovers 𝒰.I₀ 𝒰.X (fun i ↦ 𝒰.f i ≫ p) (by
      intro y
      obtain ⟨t, ht⟩ := p.surjective y
      obtain ⟨i, a, ha⟩ := 𝒰.exists_eq t
      exact ⟨i, a, by simpa [Scheme.Hom.comp_apply, ha] using ht⟩)
      (fun i ↦ by have := 𝒰.map_prop i; infer_instance)
  refine isFiniteLocallyConstantSheafOfTypes_of_finite_sheafFiber ⟨𝒱, ?_⟩ ?_
  · intro i
    rw [isConstant_over_iff_setRestriction]
    have hconst := (isConstant_over_iff_setRestriction
      (𝒰.etalePrecoverageToEtale i) ((etaleSetPullback p).obj F)).mp (h𝒰 i)
    let R := AlgebraicGeometry.Etale.localizationRestriction
      (Type (u + 1)) (𝒰.f i) (𝒰.map_prop i)
    have : (R.obj ((etaleSetPullback p).obj F)).IsConstant
        (𝒰.X i).smallEtaleTopology := hconst
    let e := R.mapIso (ρ.app F)
    have hconst' := Sheaf.isConstant_congr (𝒰.X i).smallEtaleTopology e
    have := hconst'
    let c : R.obj ((AlgebraicGeometry.Etale.localizationRestriction
        (Type (u + 1)) p inferInstance).obj F) ≅
        ((AlgebraicGeometry.Etale.localizationRestriction
          (Type (u + 1)) (𝒰.f i ≫ p) inferInstance).obj F) :=
      (fullyFaithfulSheafToPresheaf _ _).preimageIso
        (Functor.isoWhiskerRight
          (NatIso.op (MorphismProperty.Over.mapComp
            (Q := ⊤) (𝒰.map_prop i) (inferInstance : Etale p)).symm) F.obj)
    exact Sheaf.isConstant_congr (𝒰.X i).smallEtaleTopology c
  · intro Ω _ _ s
    obtain ⟨t, ht⟩ := p.surjective (s default)
    obtain ⟨a, ha, _⟩ := exists_fac_of_etale_of_isSepClosed p s t ht
    obtain ⟨c, hc, _⟩ := AlgebraicGeometry.etaleSetInverseImageStalkGerm Y T p F Ω a
    have : Finite ((pointSmallEtale a).sheafFiber.obj ((etaleSetPullback p).obj F)) :=
      hF.finite_sheafFiber Ω a
    have hfinite : Finite ((pointSmallEtale (a ≫ p)).sheafFiber.obj F) :=
      Finite.of_surjective c hc.2
    simpa only [ha] using hfinite

end AlgebraicGeometry.Scheme
