/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.FunctionField
public import WeilConjectures.ConstructibleSheaf.Defs
import WeilConjectures.AlgebraicGeometry.NormalConstantGenericUnit
import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.FullyFaithful

/-!
# Open-subscheme unit for a constant sheaf on an integrally closed integral scheme

This is the nonempty-open conjunct of Stacks Project Tag 09Z5, separated from the generic-point
argument so it can be developed independently.
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Etale

/-- The unit to the pushforward from every nonempty open subscheme is an isomorphism.
Source: Stacks Project, Tag 09Z5, nonempty-open part.
(blueprint: lem-weil-pbc-normal-constant-generic-open-unit)

Proof: a nonempty open subscheme of an integral scheme contains its generic point. The map
from the spectrum of the generic local ring therefore factors through the open immersion as
h = g ≫ j. The generic-point unit identifies the constant sheaf F with h_*h^*F, and the
direct-image composition isomorphism identifies this with j_*g_*h^*F. Thus F belongs to the
essential image of j_*. Direct image along an open immersion is fully faithful, so the unit of
j^* ⊣ j_* is an isomorphism at every object in this essential image, in particular at F.
-/
theorem isIso_unit_constantSheaf_open_unit
    (Λ : Type (u + 1)) [CommRing Λ] {Y : Scheme.{u}} [IsIntegral Y]
    (hY : ∀ y : Y, IsIntegrallyClosed (Y.presheaf.stalk y))
    (M : ModuleCat.{u + 1} Λ) {U : Scheme.{u}} (j : U ⟶ Y) [IsOpenImmersion j]
    [Nonempty U] :
    IsIso ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) j).unit.app
      ((constantSheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj M)) := by
  let A := ModuleCat.{u + 1} Λ
  let F := (constantSheaf Y.smallEtaleTopology A).obj M
  let h := Y.fromSpecStalk (genericPoint Y)
  have hη : genericPoint Y ∈ Set.range j := by
    apply ((genericPoint_spec Y).mem_open_set_iff j.isOpenEmbedding.isOpen_range).mpr
    obtain ⟨x⟩ := ‹Nonempty U›
    exact ⟨j x, trivial, x, rfl⟩
  have hsub : Set.range h ⊆ Set.range j := by
    intro y hy
    have hyη : y ⤳ genericPoint Y := by
      simpa only [h, Scheme.range_fromSpecStalk, Set.mem_ofPred_eq] using hy
    have hηy : genericPoint Y ⤳ y := (genericPoint_spec Y).specializes trivial
    have heq : y = genericPoint Y := (hyη.antisymm hηy).eq
    simpa only [heq] using hη
  let g := IsOpenImmersion.lift j h hsub
  have hg : h = g ≫ j := (IsOpenImmersion.lift_fac j h hsub).symm
  have hu : IsIso ((upperStarLowerStarAdjunction A h).unit.app F) :=
    isIso_unit_constantSheaf_generic_unit Λ hY M
  let H := (upperStar A h).obj F
  let e : F ≅ (lowerStar A j).obj ((lowerStar A g).obj H) :=
    asIso ((upperStarLowerStarAdjunction A h).unit.app F) ≪≫
      ((lowerStarComp A g j h hg).app H).symm
  exact (upperStarLowerStarAdjunction A j).isIso_unit_app_of_iso e

end AlgebraicGeometry.Etale
