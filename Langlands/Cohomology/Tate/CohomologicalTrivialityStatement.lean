import Langlands.Cohomology.Tate.ZeroDefinitions
import Mathlib.GroupTheory.Sylow

/-!
# Cohomological triviality and the comparison theorem

Three propositions on actual Tate cohomology of finite groups: for a `p`-group,
two consecutive vanishing degrees force vanishing in every degree; vanishing in
one degree is detected on the Sylow subgroups; and a morphism of integral
representations that is surjective, bijective and injective in three consecutive
degrees on every Sylow subgroup is bijective in every degree. The module defines
propositions only.
-/

open CategoryTheory CategoryTheory.Limits

universe u

namespace Langlands.Tate

/-- For a finite `p`-group, vanishing of two consecutive integral Tate cohomology
groups implies vanishing in every integer degree. -/
def PGroupTateVanishing : Prop :=
  ∀ (p : ℕ), p.Prime → ∀ (P : Type u) [Group P] [Fintype P], IsPGroup p P →
    ∀ (C : Rep.{u} IntegralScalar.{u} P) (q : ℤ),
      IsZero (tateCohomology C q) → IsZero (tateCohomology C (q + 1)) →
        ∀ n : ℤ, IsZero (tateCohomology C n)

/-- Tate cohomology in a fixed integer degree vanishes once its restrictions to
all Sylow subgroups vanish. -/
def SylowTateVanishing : Prop :=
  ∀ (R G : Type u) [CommRing R] [Group G] [Fintype G] (C : Rep.{u} R G) (n : ℤ),
    (∀ (p : ℕ), p.Prime → ∀ (P : Sylow p G) [Fintype P.1],
      IsZero (tateCohomology (Rep.res P.1.subtype C) n)) →
    IsZero (tateCohomology C n)

/-- A morphism of integral representations of a finite group which, on every
Sylow subgroup, is surjective, bijective and injective on Tate cohomology in
three consecutive degrees induces bijections in every integer degree. -/
def TateComparison : Prop :=
  ∀ (G : Type u) [Group G] [Fintype G] (D E : Rep.{u} IntegralScalar.{u} G) (f : D ⟶ E),
    (∀ (p : ℕ), p.Prime → ∀ (P : Sylow p G) [Fintype P.1], ∃ m : ℤ,
      Function.Surjective
          ((tateCohomologyFunctor m).map ((Rep.resFunctor P.1.subtype).map f)) ∧
        Function.Bijective
          ((tateCohomologyFunctor (m + 1)).map ((Rep.resFunctor P.1.subtype).map f)) ∧
        Function.Injective
          ((tateCohomologyFunctor (m + 2)).map ((Rep.resFunctor P.1.subtype).map f))) →
    ∀ n : ℤ, Function.Bijective ((tateCohomologyFunctor n).map f)

end Langlands.Tate
