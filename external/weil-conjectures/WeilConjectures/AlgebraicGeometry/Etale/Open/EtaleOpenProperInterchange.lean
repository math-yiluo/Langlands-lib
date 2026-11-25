/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStarCoherence
public import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
import WeilConjectures.AlgebraicGeometry.Proper.Open.ProperOpenInterchangeCoherence

/-!
# Open extension by zero and proper derived pushforward

Source: Stacks Project, More on Etale Cohomology, Tag 0F7B,
`lemma-shriek-proper-and-open`, Cartesian open-immersion specialization, case (b)
(blueprint: lem-weil-pbc-etale-open-proper-interchange).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Etale

/-- For a proper morphism `p : T ⟶ B` and a quasi-compact open immersion `i : V ⟶ B`,
extension by zero along `i` commutes with proper derived pushforward in their Cartesian
square, on bounded-below derived categories of etale sheaves of modules over a finite
commutative ring. The two projections from `pullback p i` are `b = pullback.fst p i`
and `p_V = pullback.snd p i`.

Source: Stacks Project, More on Etale Cohomology, Tag 0F7B,
`lemma-shriek-proper-and-open`, case (b)
(blueprint: lem-weil-pbc-etale-open-proper-interchange).

Proof plan:
Apply `AlgebraicGeometry.Etale.properOpenInterchangeCoherence`
[lem-cbc-proper-open-interchange-coherence] with top-left `pullback p i`, top-right `T`,
bottom-left `V`, bottom-right `B`, top open `pullback.fst p i`, bottom open `i`, left proper
map `pullback.snd p i`, and right proper map `p`. The square commutes by
`pullback.condition p i`. The top map is an open immersion by base change
[lem-weil-pbc-open-immersion-base-change], and the left map is proper by base change
[lem-weil-pbc-proper-base-change]. The derived isomorphism supplied by that theorem is
exactly the claimed isomorphism of functors. Finite coefficient rings are torsion, so
case (b) of Tag 0F7B applies without a residue-characteristic restriction.
-/
theorem nonempty_iso_etale_open_proper_interchange
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    {T B V : Scheme.{u}} (p : T ⟶ B) (i : V ⟶ B)
    [IsProper p] [IsOpenImmersion i] [QuasiCompact i] :
    Nonempty
      (rightDerivedLowerStarPlus (ModuleCat.{u + 1} Λ) (pullback.snd p i) ⋙
          (openImmersionLowerShriek (ModuleCat.{u + 1} Λ) i).mapDerivedCategoryPlus ≅
        (openImmersionLowerShriek (ModuleCat.{u + 1} Λ)
            (pullback.fst p i)).mapDerivedCategoryPlus ⋙
          rightDerivedLowerStarPlus (ModuleCat.{u + 1} Λ) p) := by
  obtain ⟨_, γ, _⟩ := properOpenInterchangeCoherence Λ
  exact ⟨γ (pullback.fst p i) i (pullback.snd p i) p pullback.condition⟩

end AlgebraicGeometry.Etale
