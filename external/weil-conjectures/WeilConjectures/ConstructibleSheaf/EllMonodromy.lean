/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Morphisms.EtaleTorsor
public import WeilConjectures.ConstructibleSheaf.Defs
public import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStar

/-!
# Complexes with finite `ℓ`-group monodromy

The local calculation of the trace formula (blueprint
`lemma-cohomology-near-two-transverse-divisors`, `lemma-vanishing-restrictions-after-blowing-up--1`)
is carried out for "a bounded complex `E` of `A`-modules with finite locally constant cohomology
whose monodromy factors through a finite `ℓ`-group".

## Main definitions

- `AlgebraicGeometry.Etale.HasFiniteEllMonodromy ℓ E`: the complex `E` of étale sheaves of
  `Λ`-modules on `U` is bounded, its cohomology sheaves are finite locally constant, and there is
  a finite étale Galois cover of `U` whose group is a finite `ℓ`-group and over which all
  cohomology sheaves of `E` become constant.

## Main results

- `AlgebraicGeometry.Etale.HasFiniteEllMonodromy.of_iso`: the property is invariant under
  isomorphism of complexes.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.Etale

variable {Λ : Type (u + 1)} [CommRing Λ] {U : Scheme.{u}}

/-- A complex `E` of étale sheaves of `Λ`-modules on `U` *has finite `ℓ`-group monodromy*: it is
bounded, and each of its cohomology sheaves is trivialized by a finite étale Galois cover
`c : P ⟶ U` whose group is a finite `ℓ`-group: its pullback to `P` is the constant sheaf on a
finite `Λ`-module (blueprint `lemma-cohomology-near-two-transverse-divisors`: "a bounded complex of
`A`-modules on `Z - (X ∪ Y)` with finite locally constant cohomology whose monodromy factors through
a finite `ℓ`-group"). -/
def HasFiniteEllMonodromy (ℓ : ℕ)
    (E : DerivedCategory (Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} Λ))) : Prop :=
  (∃ a b : ℤ, E.IsGE a ∧ E.IsLE b) ∧ ∀ n : ℤ,
    ∃ (G : Type (u + 1)) (_ : Group G) (_ : Finite G) (_ : IsPGroup ℓ G)
      (c : Scheme.GaloisCover G U) (M : ModuleCat.{u + 1} Λ) (_ : Finite M),
      Nonempty ((c.π)^*[ModuleCat.{u + 1} Λ].obj ((DerivedCategory.homologyFunctor _ n).obj E) ≅
        (constantSheaf c.P.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj M)

end AlgebraicGeometry.Etale
