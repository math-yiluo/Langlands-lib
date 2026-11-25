/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.EtaleSheaves
import WeilConjectures.AlgebraicGeometry.EtaleSetInverseImageRestriction
import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtaleOver
import WeilConjectures.Mathlib.CategoryTheory.Sites.ConstantSheafEquivalence

/-!
# Local constancy under open restriction

Source: finite pushforward constructibility blueprint, step 2; Stacks Project, Tag 093R.
(blueprint: lem-weil-pbc-etale-locally-constant-open-pullback).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme

private noncomputable def overRestrictionIso {X : Scheme.{u}} (V : X.Etale)
    (F : Sheaf X.smallEtaleTopology (Type (u + 1))) :
    (Etale.overSheafEquiv V (Type (u + 1))).functor.obj (F.over V) ≅
      (AlgebraicGeometry.Etale.localizationRestriction (Type (u + 1)) V.hom V.prop).obj F :=
  (fullyFaithfulSheafToPresheaf _ _).preimageIso
    (Functor.isoWhiskerRight (NatIso.op (Etale.etaleToOverCompForgetIso V).symm) F.obj)

private lemma constant_over_iff_setPullback {X : Scheme.{u}} (V : X.Etale)
    (F : Sheaf X.smallEtaleTopology (Type (u + 1))) :
    (F.over V).IsConstant (X.smallEtaleTopology.over V) ↔
      ((etaleSetPullback V.hom).obj F).IsConstant V.left.smallEtaleTopology := by
  obtain ⟨ρ, _⟩ := etaleSetInverseImageRestriction V.hom
  let e := overRestrictionIso V F ≪≫ (ρ.app F).symm
  rw [← Sheaf.isConstant_sheafCongr_functor_iff (J := X.smallEtaleTopology.over V)
    (K := V.left.smallEtaleTopology) (Etale.overEquiv V) Over.mkIdTerminal (F.over V)]
  constructor
  · intro h
    let : CategoryTheory.Sheaf.IsConstant V.left.smallEtaleTopology
        ((Etale.overSheafEquiv V (Type (u + 1))).functor.obj (F.over V)) := h
    exact Sheaf.isConstant_congr _ e
  · intro h
    let : CategoryTheory.Sheaf.IsConstant V.left.smallEtaleTopology
        ((etaleSetPullback V.hom).obj F) := h
    exact Sheaf.isConstant_congr _ e.symm

private lemma constant_setPullback {X Y : Scheme.{u}} (g : Y ⟶ X) [Etale g]
    (F : Sheaf X.smallEtaleTopology (Type (u + 1))) [F.IsConstant X.smallEtaleTopology] :
    ((etaleSetPullback g).obj F).IsConstant Y.smallEtaleTopology := by
  exact (constant_over_iff_setPullback (Etale.mk g) F).mp (F.isConstant_over _)

/-- Restricting a locally constant set-valued etale sheaf to an open subscheme preserves
local constancy. No finiteness or Noetherian hypothesis is needed.

Source: blueprint `lemma-detection-proper-direct-image--1`, step 2;
Stacks Project, Modules on Sites, Lemma 093R; Etale Cohomology, Tags 03S2 and 00XZ.
(blueprint: lem-weil-pbc-etale-locally-constant-open-pullback).

Proof: Choose an etale cover trivializing F on its localized sites. Base change that
cover along the open immersion U into X. The resulting family is an etale cover of U.
For each original cover member V, the new member is the open subscheme V times_X U.
Identify etale sheaves on V with sheaves on the site of X localized at V. Restriction
to V times_X U is localization once more. Under this identification the restriction
of F is constant: the over-pullback functor carries the constant sheaf to the constant
sheaf, by the adjunction for constant sheaves (equivalently, sheafify the restricted
constant presheaf; the localization functor preserves covering families).
The etale inverse-image restriction comparison identifies the restriction of the
inverse image on U with that same twice-localized sheaf; its unit compatibility makes
the two restrictions agree. Isomorphic sheaves have the same constant-sheaf property.
Thus the base-changed cover is a trivializing cover of the inverse image on U. -/
theorem isLocallyConstantEtaleSheafOfSets_open_pullback
    {X : Scheme.{u}} (F : Sheaf X.smallEtaleTopology (Type (u + 1)))
    (U : X.Opens) (hF : IsLocallyConstantEtaleSheafOfSets F) :
    IsLocallyConstantEtaleSheafOfSets ((etaleSetPullback U.ι).obj F) := by
  obtain ⟨𝒰, h𝒰⟩ := hF
  let : etalePrecoverage.IsStableUnderBaseChange :=
    inferInstanceAs (precoverage @Etale).IsStableUnderBaseChange
  obtain ⟨c, _⟩ := etaleSetInverseImageCompositionUnits.2.2
  refine ⟨𝒰.pullback₂ U.ι, fun i ↦ ?_⟩
  apply (constant_over_iff_setPullback _ _).mpr
  have h₁ := (constant_over_iff_setPullback (𝒰.etalePrecoverageToEtale i) F).mp (h𝒰 i)
  let : CategoryTheory.Sheaf.IsConstant (𝒰.X i).smallEtaleTopology
      ((etaleSetPullback (𝒰.f i)).obj F) := h₁
  have h₂ := constant_setPullback (Limits.pullback.fst (𝒰.f i) U.ι)
    ((etaleSetPullback (𝒰.f i)).obj F)
  let : CategoryTheory.Sheaf.IsConstant
      (Cover.etalePrecoverageToEtale (𝒰.pullback₂ U.ι) i).left.smallEtaleTopology
      ((etaleSetPullback (Limits.pullback.fst (𝒰.f i) U.ι)).obj
        ((etaleSetPullback (𝒰.f i)).obj F)) := h₂
  let e : (etaleSetPullback (Limits.pullback.fst (𝒰.f i) U.ι)).obj
      ((etaleSetPullback (𝒰.f i)).obj F) ≅
      (etaleSetPullback (Limits.pullback.snd (𝒰.f i) U.ι)).obj
        ((etaleSetPullback U.ι).obj F) :=
    ((c X (𝒰.X i) (Limits.pullback (𝒰.f i) U.ι) (𝒰.f i)
        (Limits.pullback.fst (𝒰.f i) U.ι)).app F) ≪≫
      eqToIso (congrArg (fun m ↦ (etaleSetPullback m).obj F) Limits.pullback.condition) ≪≫
      ((c X U (Limits.pullback (𝒰.f i) U.ι) U.ι
        (Limits.pullback.snd (𝒰.f i) U.ι)).app F).symm
  exact Sheaf.isConstant_congr _ e

end AlgebraicGeometry.Scheme
