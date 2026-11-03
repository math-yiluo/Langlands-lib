# Reducedness in semisimple rank one from negation and positive-root uniqueness

This module is a derived, conditional assembly step toward the published
`RootReducednessStatement` (`Langlands.GroupScheme.Reductive.RootReducednessStatement`).
It proves the published `RankOneRootReducednessStatement`
(`Langlands.GroupScheme.Reductive.RankOneRootReducednessStatement`) from two
published statements, which enter as explicit hypotheses:

* `RelativeRootNegationStatement`
  (`Langlands.GroupScheme.Rational.RelativeRootNegationStatement`): the actual
  relative roots of a maximal split torus in a connected reductive group are
  stable under negation;
* `RankOnePositiveRootUniquenessStatement`
  (`Langlands.GroupScheme.Reductive.RankOnePositiveRootStatement`): if any two
  roots of a split maximal torus are linearly dependent over `ℤ`, then for every
  cocharacter `ν` at most one root `α` satisfies `0 < ⟨α, ν⟩`.

Neither hypothesis is proved here. They are separate obligations. The module
changes none of the three statement files or the files they import.

The model is Milne, *Algebraic Groups* (2017), Theorem 21.11(b) and its proof
(printed pp. 428–429, PDF pp. 444–445). There, `G_α = C_G(T_α)` has
semisimple rank one, and the root group `U_α = U_{G_α}(λ)` (Definition 21.10, any
cocharacter `λ` with `⟨α, λ⟩ > 0`) is isomorphic to `𝔾_a`. The weights of `T`
on `Lie(U_α)` are the positive rational multiples of `α` in `Φ`, so `α` is the
only one, and "the only rational multiples of `α` in `Φ` are `±α`". The module
isolates the elementary lattice step that turns "at most one root is positive
on a given cocharacter" plus negation stability into "any two roots are equal
or opposite". Milne leaves this step implicit.

## Setting

The universe is an arbitrary `u`. The setting is a field `k : Type u` and a
commutative group scheme `T` over `Spec k`. `latticePairing T` is the published
`ℤ`-bilinear pairing `⟨χ, ν⟩` between the actual character lattice and the
actual cocharacter lattice of `T` (`Langlands/GroupScheme/Torus/Lattice.lean`).
For a split torus this pairing is perfect, by the published
`IsSplitTorus.isPerfPair_latticePairing`
(`Langlands/GroupScheme/Absolute/RegularPerturbation.lean`). The two lattice
lemmas below use only its left separation: a character that pairs to zero with
every cocharacter is zero.

## Lattice lemmas and the chosen positive cocharacter

`IsSplitTorus.exists_latticePairing_pos`: let `T` be split and `α ≠ 0` a
character. Then some cocharacter `ν` has `0 < ⟨α, ν⟩`. Proof: otherwise
`⟨α, ν⟩ ≤ 0` and `⟨α, -ν⟩ = -⟨α, ν⟩ ≤ 0` for every `ν`. So `⟨α, ν⟩ = 0` for
every `ν`, and left separation gives `α = 0`.

`IsSplitTorus.positiveCocharacter` (a noncomputable definition): for split `T`
and a character `α ≠ 0`, a cocharacter `ν` with `0 < ⟨α, ν⟩`, chosen with
`Exists.choose` from the previous lemma. It is a choice, not a canonical
cocharacter: any cocharacter positive on `α` would serve. Milne's Definition
21.10 likewise takes an arbitrary `λ` with `⟨α, λ⟩ > 0`. The companion lemma
`IsSplitTorus.latticePairing_positiveCocharacter_pos` states
`0 < ⟨α, hT.positiveCocharacter hα⟩`.

`IsSplitTorus.latticePairing_ne_zero_of_not_linearIndependent`: let `T` be
split, and let `α, β` be characters with `β ≠ 0` such that `![α, β]` is not
linearly independent over `ℤ`. If `⟨α, ν⟩ ≠ 0`, then `⟨β, ν⟩ ≠ 0`. Proof:
suppose `⟨β, ν⟩ = 0`. The goal becomes linear independence, which by
Mathlib's `LinearIndependent.pair_iff` means: `m • α + n • β = 0` implies
`m = 0` and `n = 0`. Pairing the relation with any cocharacter `μ` gives
`m ⟨α, μ⟩ + n ⟨β, μ⟩ = 0`. At `μ = ν` this reads `m ⟨α, ν⟩ = 0`, so `m = 0`
because `ℤ` has no zero divisors. If `n ≠ 0`, then `n ⟨β, μ⟩ = 0` gives
`⟨β, μ⟩ = 0` for every `μ`, and left separation gives `β = 0`, a
contradiction. So `n = 0`.

## The conditional theorem

`rankOneRootReducedness_of_negation_of_positiveRootUniqueness`:

```
(hneg : RelativeRootNegationStatement.{u})
(hpos : RankOnePositiveRootUniquenessStatement.{u}) :
RankOneRootReducednessStatement.{u}
```

Fix the data of `RankOneRootReducednessStatement`. These are a field
`k : Type u`, `G` with `hG : IsConnectedReductive G`, a split `T`, a maximal
torus `i : T.toGrp ⟶ G`, the instance `IsAffineHom G.X.hom` taken from
`hG.isAffineHom`, and the hypothesis `hdep` that no two roots are linearly
independent over `ℤ`. Let `α, β ∈ roots i`. Roots are nonzero by definition
(`mem_roots`).

1. Let `ν = hT.positiveCocharacter hα`, so `0 < ⟨α, ν⟩` by
   `IsSplitTorus.latticePairing_positiveCocharacter_pos`.
2. `hdep α β` and the second lattice lemma give `⟨β, ν⟩ ≠ 0`.
3. If `0 < ⟨β, ν⟩`, then `hpos` applied to `ν`, `α`, `β` gives `α = β`.
4. If `⟨β, ν⟩ < 0`, then `-β` is a root. The published
   `IsMaximalTorus.isMaximalSplitTorus`
   (`Langlands/GroupScheme/Torus/MaximalSplitComparison.lean`) makes `i` a
   maximal split torus, `relativeRoots_eq_roots` identifies relative and
   absolute roots, and `hneg` gives `-β ∈ roots i`. Since
   `⟨-β, ν⟩ = -⟨β, ν⟩ > 0`, `hpos` applied to `ν`, `α`, `-β` gives `α = -β`.

The theorem and the definition use only the axioms `propext`,
`Classical.choice` and `Quot.sound`.

## Provenance

Derived. Milne's proof of Theorem 21.11(b) obtains the conclusion from the
one-dimensionality of `Lie(U_α)` in the rank-one group `G_α`. The present
decomposition is internal: `RankOnePositiveRootUniquenessStatement` carries the
geometric content (Milne §20.e), `RelativeRootNegationStatement` carries
`-α ∈ Φ`, and this module supplies the lattice argument connecting them.
