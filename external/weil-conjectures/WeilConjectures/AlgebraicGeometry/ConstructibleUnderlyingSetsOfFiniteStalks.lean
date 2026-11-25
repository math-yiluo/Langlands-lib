/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.EtaleSheaves
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Point.Basic
import WeilConjectures.ConstructibleSheaf.Pullback
import all WeilConjectures.AlgebraicGeometry.ConstructibleModuleUnderlyingSets
import WeilConjectures.AlgebraicGeometry.FundamentalGroup.FiniteStalksComparison

/-!
# Constructibility after forgetting modules with finite stalks

Source: Stacks Project, Tags 095E and 09Z6.
(blueprint: lem-weil-pbc-constructible-underlying-sets-of-finite-stalks).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme

private theorem finiteLocallyConstant_underlyingSets {Λ : Type (u + 1)}
    [CommRing Λ] {Y : Scheme.{u}}
    (G : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (hG : IsFiniteLocallyConstantSheaf G)
    (hfin : ∀ (Ω : Type u) [Field Ω] [IsSepClosed Ω] (s : Spec (.of Ω) ⟶ Y),
      Finite (((pointSmallEtale s).sheafFiber (A := ModuleCat.{u + 1} Λ)).obj G)) :
    IsLisseEtaleSheafOfSets
      ((sheafCompose Y.smallEtaleTopology
        (CategoryTheory.forget (ModuleCat.{u + 1} Λ))).obj G) := by
  let := hG
  constructor
  · obtain ⟨d⟩ := IsLocallyConstantSheaf.nonempty_locallyConstantDatum (F := G)
    refine ⟨d.cover, fun i ↦ ?_⟩
    let := d.isConstant i
    change ((sheafCompose (Y.smallEtaleTopology.over (d.cover.etalePrecoverageToEtale i))
      (CategoryTheory.forget (ModuleCat.{u + 1} Λ))).obj
      (G.over (d.cover.etalePrecoverageToEtale i))).IsConstant _
    infer_instance
  · refine isFiniteSheaf_of_finite_algClosed_stalks _ fun Ω _ _ s ↦ ?_
    let P := pointSmallEtale s
    let M := (P.sheafFiber (A := ModuleCat.{u + 1} Λ)).obj G
    have : Finite M := hfin Ω s
    let : Limits.PreservesFilteredColimitsOfSize.{u, u}
        (CategoryTheory.forget (ModuleCat.{u + 1} Λ)) :=
      Limits.preservesFilteredColimitsOfSize_shrink.{u, u + 1, u, u + 1} _
    let e := (P.sheafFiberCompIso.{u, u, u + 1, u + 1, u + 1, u + 2, u + 2}
      (CategoryTheory.forget (ModuleCat.{u + 1} Λ))).app G
    exact Finite.of_equiv M e.toEquiv.symm

/-- Module constructibility and finite geometric stalks imply set constructibility.

Source: Stacks Project, Tags 095E and 09Z6, and the finite-stalk refinement of
`lem-weil-pbc-finite-pushforward-finite-stalk-module`, step 1.
(blueprint: lem-weil-pbc-constructible-underlying-sets-of-finite-stalks)

Proof: Retain the source stratification. Forget each module locally constant datum.
Inverse image commutes with forgetting modules, by filtered left Kan extensions and
sheafification. The inverse-image stalk comparison identifies every stalk on a
stratum with a source geometric stalk, hence makes it finite as a set. The
point-ulift isomorphism reconciles the universes in the hypothesis. Transport local
constancy and stalk finiteness through the forgetful comparison isomorphism on each
stratum. This works for empty strata and the zero sheaf and uses no finiteness of the
coefficient ring. -/
theorem isConstructibleEtaleSheafOfSets_of_finite_module_stalks
    (Λ : Type (u + 1)) [CommRing Λ]
    {X : Scheme.{u}} (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (hF : IsConstructibleSheaf F)
    (hfin : ∀ (Ω : Type u) [Field Ω] [IsSepClosed Ω] (s : Spec (.of Ω) ⟶ X),
      Finite ((((pointSmallEtale s).ulift.{u + 1}).sheafFiber
        (A := ModuleCat.{u + 1} Λ)).obj F)) :
    IsConstructibleEtaleSheafOfSets
      ((sheafCompose X.smallEtaleTopology (CategoryTheory.forget AddCommGrpCat.{u + 1})).obj
        ((sheafCompose X.smallEtaleTopology
          (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj F)) := by
  obtain ⟨S, hS⟩ := hF
  refine ⟨S, fun k ↦ ?_⟩
  let G := (Etale.upperStar (ModuleCat.{u + 1} Λ) (S.immersion k)).obj F
  have hG : IsFiniteLocallyConstantSheaf G := hS k
  have hGfin (Ω : Type u) [Field Ω] [IsSepClosed Ω] (s : Spec (.of Ω) ⟶ S.domain k) :
      Finite (((pointSmallEtale s).sheafFiber (A := ModuleCat.{u + 1} Λ)).obj G) := by
    have : Finite ((((pointSmallEtale (s ≫ S.immersion k)).ulift.{u + 1}).sheafFiber
      (A := ModuleCat.{u + 1} Λ)).obj F) := hfin Ω (s ≫ S.immersion k)
    let e := ((pointSmallEtale (s ≫ S.immersion k)).uliftSheafFiberIso.{u + 1}
      (ModuleCat.{u + 1} Λ)).app F
    have : Finite (((pointSmallEtale (s ≫ S.immersion k)).sheafFiber
      (A := ModuleCat.{u + 1} Λ)).obj F)  := Finite.of_equiv
        ((((pointSmallEtale (s ≫ S.immersion k)).ulift.{u + 1}).sheafFiber
          (A := ModuleCat.{u + 1} Λ)).obj F) e.toLinearEquiv.toEquiv
    let e' := (Etale.upperStarCompSheafFiberIso (ModuleCat.{u + 1} Λ)
      (S.immersion k) s).app F
    exact Finite.of_equiv _ e'.toLinearEquiv.toEquiv.symm
  have hUG := finiteLocallyConstant_underlyingSets G hG hGfin
  obtain ⟨e⟩ := underlyingSetPullbackIso (S.immersion k) F
  constructor
  · obtain ⟨𝒰, h𝒰⟩ := hUG.1
    refine ⟨𝒰, fun i ↦ ?_⟩
    let := h𝒰 i
    exact Sheaf.isConstant_congr _
      (((S.domain k).smallEtaleTopology.overPullback (Type (u + 1))
        (𝒰.etalePrecoverageToEtale i)).mapIso e.symm)
  · refine isFiniteSheaf_of_finite_algClosed_stalks _ fun Ω _ _ s ↦ ?_
    have : Finite ((pointSmallEtale s).sheafFiber.obj
        ((sheafCompose (S.domain k).smallEtaleTopology
          (CategoryTheory.forget (ModuleCat.{u + 1} Λ))).obj G)) :=
      hUG.finite_sheafFiber Ω s
    exact Finite.of_equiv _
      (((pointSmallEtale s).sheafFiber (A := Type (u + 1))).mapIso e).toEquiv.symm

end AlgebraicGeometry.Scheme
