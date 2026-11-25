/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.SixFunctors.Etale.LowerShriek.EtaleMap
public import WeilConjectures.AlgebraicGeometry.IsConstructibleEtaleModuleSheaf
import WeilConjectures.AlgebraicGeometry.ConstructibleEtaleModuleSheafComparisonExtension
import WeilConjectures.AlgebraicGeometry.EtaleLowerShriekBaseChangeModules
import WeilConjectures.AlgebraicGeometry.EtaleStratifiedFinite
import WeilConjectures.AlgebraicGeometry.FiniteEtalePushforwardLocallyConstant
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.FiniteEtale
import WeilConjectures.ConstructibleSheaf.Pullback
import WeilConjectures.Mathlib.CategoryTheory.Sites.Point.ConstantSheaf

/-!
# Constructibility of extension by zero of a finite constant module sheaf

Source: Stacks Project, Tag 03S8, Lemma 59.73.1(3)
(blueprint: lem-weil-pbc-etale-free-sheaf-constructible).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme

private theorem finiteLocallyConstant_constant_module
    (T : Scheme.{u}) {Λ : Type (u + 1)} [CommRing Λ]
    (M : ModuleCat.{u + 1} Λ) [Finite M] :
    IsFiniteLocallyConstantSheaf
      ((constantSheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj M) := by
  have hc : ((constantSheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj M).IsConstant
      T.smallEtaleTopology := Sheaf.isConstant_of_iso _ (Iso.refl _)
  have hl := hc.isLocallyConstantSheaf
  refine { toIsLocallyConstantSheaf := hl, isFinitelyGenerated_sheafFiber := ?_ }
  intro Ω _ _ t
  have : Limits.PreservesFilteredColimitsOfSize.{u, u}
      (CategoryTheory.forget (ModuleCat.{u + 1} Λ)) :=
    Limits.preservesFilteredColimitsOfSize_shrink.{u, u + 1, u, u + 1} _
  have hM : ConcreteCategory.IsFinitelyGenerated M :=
    (ModuleCat.isFinitelyGenerated_iff M).2 Module.Finite.of_finite
  exact hM.of_iso ((pointSmallEtale t).sheafFiberConstantSheafIso M).symm

/-- Extension by zero of a finite constant module sheaf along an etale morphism between
quasi-compact quasi-separated schemes is constructible. Sheaves valued in `ModuleCat Λ`
encode module sheaves over the constant ring sheaf `Λ_X`. The functor `etaleLowerShriek`
sheafifies the presheaf whose value on `V` is the direct sum over `Hom_X(V, U)` of the
constant module sheaf's sections on `V`; restriction reindexes by composition and restricts
sections. Thus its value here is the node's `j_! underline M_U`, including the free
rank-one case `M = Λ`.

Source: Stacks Project, Tag 03S8, Lemma 59.73.1(3)
(blueprint: lem-weil-pbc-etale-free-sheaf-constructible).

Proof:
1. Choose a finite partition of `X` into constructible locally closed subschemes such
   that the base change of `j` to each stratum is finite etale, by Tag 03S0
   (`lem-weil-pbc-etale-stratified-finite`).
2. Pull back the extension to each stratum. Tag 03S6 identifies this pullback with the
   extension of the constant module sheaf on the base-changed source
   (`lem-weil-pbc-etale-shriek-base-change-modules`).
3. For each finite etale base change, extension by zero agrees with direct image,
   by Tag 03S7 (`lem-weil-pbc-etale-shriek-star-finite-modules`).
4. This direct image is finite locally constant by Tag 095B
   (`lem-weil-pbc-etale-finite-pushforward-locally-constant`).
5. The partition therefore witnesses constructibility, as in
   `def-weil-pbc-etale-constructible-sheaf` and `def-weil-pbc-etale-sheaves` on the site
   `def-weil-pbc-etale-site`. Finiteness of `Λ` supplies the Noetherian coefficient
   hypothesis of Tag 03S8; finiteness of `M` supplies finite constant values.
-/
/- Core stalk constructibility argument for Tag 03S8(3).
Source: Stacks Project, Tag 03S8, proof lines 12198-12212.
The finite stratification, base change, finite-etale comparison, and finite pushforward
steps produce the constructibility witness.
(blueprint: lem-weil-pbc-etale-free-sheaf-constructible-core).
-/
theorem isConstructibleSheaf_etaleLowerShriek_constant_core
    {X U : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X]
    [CompactSpace U] [QuasiSeparatedSpace U]
    {Λ : Type (u + 1)} [CommRing Λ] [Finite Λ]
    (j : U ⟶ X) [Etale j] (M : ModuleCat.{u + 1} Λ) [Finite M] :
    IsConstructibleSheaf
      (FA := fun A B : ModuleCat.{u + 1} Λ => A →ₗ[Λ] B)
      (CA := fun A : ModuleCat.{u + 1} Λ => A)
      ((Etale.etaleLowerShriek (ModuleCat.{u + 1} Λ) j inferInstance).obj
        ((constantSheaf U.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj M)) := by
  obtain ⟨S, _, hf⟩ := exists_etale_stratified_finite j
  let T : Stratification X :=
    { toStratification := S.toStratification
      domain := S.domain
      immersion := S.immersion
      isImmersion := S.isImmersion
      range_immersion := S.range_immersion }
  refine ⟨T, fun i ↦ ?_⟩
  have := (hf i).1
  have := (hf i).2
  let g := S.immersion i
  have : IsFinite (Limits.pullback.fst g j) := by
    rw [← Limits.pullbackSymmetry_hom_comp_snd g j]
    infer_instance
  let N := (constantSheaf U.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj M
  have hconstant := finiteLocallyConstant_constant_module U M
  have hpull := IsFiniteLocallyConstantSheaf.upperStar (Limits.pullback.snd g j) N
  have hpush := finiteLocallyConstant_lowerStar_of_finite_etale
    (Limits.pullback.fst g j) ((Etale.upperStar _ (Limits.pullback.snd g j)).obj N)
  have hshriek := IsFiniteLocallyConstantSheaf.of_iso
    (asIso (Etale.etaleLowerShriekToLowerStar (ModuleCat.{u + 1} Λ)
      (Limits.pullback.fst g j) ((Etale.upperStar _ (Limits.pullback.snd g j)).obj N))).symm
  have hbase := Etale.isIso_etaleLowerShriekBaseChangeMap Λ g j
  let e := asIso ((Etale.etaleLowerShriekBaseChangeMap Λ g j).app N)
  have : IsFiniteLocallyConstantSheaf
      ((Etale.upperStar (ModuleCat.{u + 1} Λ) (Limits.pullback.snd g j) ⋙
      Etale.etaleLowerShriek (ModuleCat.{u + 1} Λ) (Limits.pullback.fst g j)
        inferInstance).obj N) := hshriek
  exact IsFiniteLocallyConstantSheaf.of_iso e

/-- (blueprint: lem-weil-pbc-etale-free-sheaf-constructible) -/
theorem isConstructibleEtaleModuleSheaf_etaleLowerShriek_constant
    {X U : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X]
    [CompactSpace U] [QuasiSeparatedSpace U]
    {Λ : Type (u + 1)} [CommRing Λ] [Finite Λ]
    (j : U ⟶ X) [Etale j] (M : ModuleCat.{u + 1} Λ) [Finite M] :
    IsConstructibleEtaleModuleSheaf
      ((Etale.etaleLowerShriek (ModuleCat.{u + 1} Λ) j inferInstance).obj
        ((constantSheaf U.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj M)) := by
  apply (isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf _).2
  exact isConstructibleSheaf_etaleLowerShriek_constant_core j M

end AlgebraicGeometry.Scheme
