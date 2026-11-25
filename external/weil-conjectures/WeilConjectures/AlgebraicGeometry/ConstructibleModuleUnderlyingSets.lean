/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.IsConstructibleEtaleModuleSheaf
public import WeilConjectures.AlgebraicGeometry.EtaleSheaves
import WeilConjectures.AlgebraicGeometry.FiniteLocallyConstantModuleValues
import WeilConjectures.AlgebraicGeometry.FundamentalGroup.FiniteStalksComparison

/-!
# Constructibility after forgetting module structure

Source: Stacks Project, Tags 095E and 09Z6.
(blueprint: lem-weil-pbc-constructible-module-underlying-sets).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme

private theorem underlyingSetPullbackIso {Λ : Type (u + 1)} [CommRing Λ]
    {X Y : Scheme.{u}} (g : Y ⟶ X)
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    Nonempty (((etaleSetPullback g).obj
      ((sheafCompose X.smallEtaleTopology (CategoryTheory.forget (ModuleCat.{u + 1} Λ))).obj F)) ≅
      (sheafCompose Y.smallEtaleTopology (CategoryTheory.forget (ModuleCat.{u + 1} Λ))).obj
        ((Etale.upperStar (ModuleCat.{u + 1} Λ) g).obj F)) := by
  let B := MorphismProperty.Over.pullback @Etale ⊤ g
  let U := CategoryTheory.forget (ModuleCat.{u + 1} Λ)
  have hfiltered (V : Y.Etaleᵒᵖ) : IsFiltered (CostructuredArrow B.op V) :=
    IsFiltered.of_equivalence (structuredArrowOpEquivalence B V.unop)
  let (V : Y.Etaleᵒᵖ) : IsFiltered (CostructuredArrow B.op V) := hfiltered V
  let : Limits.PreservesFilteredColimitsOfSize.{u, u + 1} U :=
    Limits.preservesFilteredColimitsOfSize_shrink.{u + 1, u + 1, u, u + 1} U
  let (V : Y.Etaleᵒᵖ) : U.PreservesPointwiseLeftKanExtensionAt F.obj B.op V := by
    infer_instance
  have hpres : U.PreservesLeftKanExtension F.obj B.op := by infer_instance
  have hs : Y.smallEtaleTopology.PreservesSheafification U := by infer_instance
  let e := U.leftKanExtensionCompIsoOfPreserves F.obj B.op
  exact ⟨(presheafToSheaf Y.smallEtaleTopology (Type (u + 1))).mapIso e.symm ≪≫
    (sheafComposeNatIso Y.smallEtaleTopology U
      (sheafificationAdjunction Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))
      (sheafificationAdjunction Y.smallEtaleTopology (Type (u + 1)))).app
        (B.op.leftKanExtension F.obj)⟩

private theorem finiteLocallyConstant_underlyingSets {Λ : Type (u + 1)}
    [CommRing Λ] [Finite Λ] {Y : Scheme.{u}}
    (G : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (hG : IsFiniteLocallyConstantSheaf G) :
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
    let : Module.Finite Λ M := (ModuleCat.isFinitelyGenerated_iff M).mp
      (IsFiniteSheaf.isFinitelyGenerated_sheafFiber Ω s)
    let : Finite M := Module.finite_of_finite Λ
    let : Limits.PreservesFilteredColimitsOfSize.{u, u}
        (CategoryTheory.forget (ModuleCat.{u + 1} Λ)) :=
      Limits.preservesFilteredColimitsOfSize_shrink.{u, u + 1, u, u + 1} _
    let e := (P.sheafFiberCompIso.{u, u, u + 1, u + 1, u + 1, u + 2, u + 2}
      (CategoryTheory.forget (ModuleCat.{u + 1} Λ))).app G
    exact Finite.of_equiv M e.toEquiv.symm

/-- Finite module trivializations give a constructible underlying sheaf of sets.

Source: Stacks Project, Tag 095E(3), and the passage from (3) to (1) in Tag 09Z6.
(blueprint: lem-weil-pbc-constructible-module-underlying-sets).

Proof: Retain the finite locally closed partition witnessing module constructibility.
Its parts are constructible, so the same domains and immersions form a stratification
in the set-valued definition. Forgetting modules commutes with inverse image and with
restriction to each member of the trivializing etale cover. The underlying set of each
finite constant module is finite, and forgetting carries its constant sheaf to the
constant sheaf of this set. Hence the set pullback to every stratum is locally constant.
At any geometric point of that stratum, lift to a member of the cover. Its stalk is the
finite underlying set of that member's constant module, since stalks commute with
restriction and constants. Thus the pullback is finite locally constant on every
stratum, as required. The empty partition and the zero module cause no exception. -/
theorem isConstructibleEtaleSheafOfSets_of_module
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    {X : Scheme.{u}} (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (hF : IsConstructibleEtaleModuleSheaf F) :
    IsConstructibleEtaleSheafOfSets
      ((sheafCompose X.smallEtaleTopology (CategoryTheory.forget AddCommGrpCat.{u + 1})).obj
        ((sheafCompose X.smallEtaleTopology
          (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj F)) := by
  obtain ⟨S, hS⟩ := hF
  let T : Stratification X :=
    { toStratification := S.toStratification
      domain := S.domain
      immersion := S.immersion
      isImmersion := S.isImmersion
      range_immersion := S.range_immersion }
  refine ⟨T, fun k ↦ ?_⟩
  let G := (Etale.upperStar (ModuleCat.{u + 1} Λ) (S.immersion k)).obj F
  have hG : IsFiniteLocallyConstantSheaf G :=
    (finite_locally_constant_module_values_iff G).1.mp (hS k)
  have hUG := finiteLocallyConstant_underlyingSets G hG
  obtain ⟨e⟩ := underlyingSetPullbackIso (S.immersion k) F
  constructor
  · obtain ⟨𝒰, h𝒰⟩ := hUG.1
    refine ⟨𝒰, fun i ↦ ?_⟩
    let := h𝒰 i
    exact Sheaf.isConstant_congr _
      (((S.domain k).smallEtaleTopology.overPullback (Type (u + 1))
        (𝒰.etalePrecoverageToEtale i)).mapIso e.symm)
  · refine isFiniteSheaf_of_finite_algClosed_stalks _ fun Ω _ _ s ↦ ?_
    have hfinite : Finite ((pointSmallEtale s).sheafFiber.obj
        ((sheafCompose (S.domain k).smallEtaleTopology
          (CategoryTheory.forget (ModuleCat.{u + 1} Λ))).obj G)) :=
      hUG.finite_sheafFiber Ω s
    exact @Finite.of_equiv _ _ hfinite
      (((pointSmallEtale s).sheafFiber (A := Type (u + 1))).mapIso e).toEquiv.symm

end AlgebraicGeometry.Scheme
