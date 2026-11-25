/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs
import WeilConjectures.AlgebraicGeometry.ProEtaleAbelianClosedSupport

/-! Condensed module equivalence for a surjective closed immersion. -/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

/-- Pullback on condensed module objects along a surjective closed immersion is an
 equivalence.

Source: Stacks Project Tags 09AA and 09AH, empty-complement case; the module adjunction
lift in `CondensedOpenClosedRecollement.lean`.
Proof: use the empty open subscheme as the complementary open. Every sheaf
on this empty scheme is zero, so abelian closed support makes both the unit and
counit invertible. Lift the invertible unit and counit to module objects and
compose with extension along the coefficient comparison isomorphism.
(auxiliary; not a blueprint node)
-/
theorem condensedSurjectiveClosedPullback_isEquivalence
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X Z : Scheme.{u}} (i : Z ⟶ X)
    [IsClosedImmersion i] [Surjective i] :
    (CondensedRing.upperStar Λ i).IsEquivalence := by
  let j := (⊥ : X.Opens).ι
  have hU : IsEmpty (⊥ : X.Opens).toScheme := ⟨fun x ↦ x.property⟩
  let := hU
  have hij : Set.range j = (Set.range i)ᶜ := by
    rw [Set.range_eq_univ.mpr i.surjective, Set.compl_univ]
    exact Set.range_eq_empty j
  have hqc : QuasiCompact j := by infer_instance
  obtain ⟨hc, hu⟩ := abelian_closed_support_counit_and_unit i j hij
  have hunitAb (F : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) :
      IsIso ((upperStarLowerStarAdjunction Ab.{u + 1} i).unit.app F) := by
    apply hu F
    refine Sheaf.isZero_of_isZero_obj _ ?_
    rintro ⟨V⟩
    have : IsEmpty V.left := ⟨fun v ↦ by
      have x : (⊥ : X.Opens).toScheme := V.hom.base v
      exact x.property⟩
    exact (Scheme.ProEt.isTerminalSectionsOfIsEmpty
      ((upperStar Ab.{u + 1} j).obj F) V).isZero
  have : IsIso (upperStarLowerStarAdjunction Ab.{u + 1} i).unit :=
    NatIso.isIso_of_isIso_app _
  have : (upperStar Ab.{u + 1} i).IsEquivalence :=
    (upperStarLowerStarAdjunction Ab.{u + 1} i).toEquivalence.isEquivalence_functor
  let adj := (upperStarLowerStarAdjunction Ab.{u + 1} i).mapModAdjunction
    (condensedRingObj Λ X)
  have hunit (M) : IsIso (adj.unit.app M) := by
    have hh : IsIso ((Mod.forget _).map (adj.unit.app M)) := by
      change IsIso (adj.unit.app M).hom
      dsimp only [adj]
      rw [Adjunction.mapModAdjunction_unit_app_hom]
      infer_instance
    exact isIso_of_reflects_iso _ (Mod.forget _)
  have hcounit (N) : IsIso (adj.counit.app N) := by
    have hh : IsIso ((Mod.forget _).map (adj.counit.app N)) := by
      change IsIso (adj.counit.app N).hom
      dsimp only [adj]
      rw [Adjunction.mapModAdjunction_counit_app_hom]
      infer_instance
    exact isIso_of_reflects_iso _ (Mod.forget _)
  have : ((upperStar Ab.{u + 1} i).mapMod (condensedRingObj Λ X)).IsEquivalence :=
    adj.toEquivalence.isEquivalence_functor
  have : (Mod.comap (asIso (condensedPullbackHom Λ i)).inv).IsEquivalence :=
    (Mod.comapEquivalenceOfIsIso (condensedPullbackHom Λ i)).isEquivalence_inverse
  have : (Mod.extendScalars (condensedPullbackHom Λ i)).IsEquivalence :=
    Functor.isEquivalence_of_iso (Mod.extendScalarsIsoComapInv
      (condensedPullbackHom Λ i)).symm
  change (((upperStar Ab.{u + 1} i).mapMod (condensedRingObj Λ X)) ⋙
    Mod.extendScalars (condensedPullbackHom Λ i)).IsEquivalence
  infer_instance

end AlgebraicGeometry.ProEtale
