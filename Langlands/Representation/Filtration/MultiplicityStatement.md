# Jordan–Hölder multiplicities of a single constituent

This module defines the multiplicity with which a given representation occurs
among the composition factors of a representation, using the Library's actual
composition series, and states, as a separate proposition, that this number
does not depend on the composition series. It proves nothing.

## Objects

All three declarations are in the namespace `Langlands` and work over any
field `k` and any monoid `G`. The carrier of `A` and the carrier of `τ` may lie
in independent universes. There is no smoothness, admissibility or
finite-dimensionality hypothesis.

- `ObjectRepFiltration.factorMultiplicity s τ` is, for one filtration
  `s : ObjectRepFiltration A n` of the Library (a chain of `n + 1` invariant
  subspaces from `0` to all of `A`), the number of indices `i : Fin n` whose
  graded quotient `s.gradedRepresentation i` admits a
  `Representation.Equiv` to `τ`. It is the cardinality `Nat.card` of that
  finite set of indices. It counts for the given filtration only; it chooses
  no series.
- `HasJordanHolderMultiplicity A τ m` says that `A` has an actual composition
  series (`ObjectRepFiltration.HasSimpleFactors`: every graded quotient is
  irreducible) in which exactly `m` composition factors are equivalent to `τ`.
- `JordanHolderMultiplicityIndependenceStatement` says that for every field
  `k`, every monoid `G`, every `A` and `τ`, and any two composition series
  `s` and `t` of `A`, possibly of different lengths `n` and `n'`, the counts
  `s.factorMultiplicity τ` and `t.factorMultiplicity τ` are equal.

### Reading the definitions

If `A` has no composition series (infinite length), then
`HasJordanHolderMultiplicity A τ m` is false for every `m`. If `A` has finite
length, then the independence statement says that exactly one `m` satisfies
it, the multiplicity of `τ` in `A`. Without the independence statement the
predicate only records that some series has `m` such factors; downstream
statements that need "the" multiplicity should assume or cite the
independence statement rather than reprove it.

Irreducibility of `τ` is not a hypothesis. On a composition series every
factor is irreducible, and an equivalence carries irreducibility, so a
reducible `τ` has count `0` on every composition series.

`HaveSameJordanHolderFactors A B` in
`Langlands.Representation.Filtration.ObjectDefinitions` compares whole
multisets of factors by a permutation of indices; this module adds the count
of one constituent, which that relation does not provide.

## Original sources and derived content

Provenance: derived.

- Silberger, *The Langlands quotient theorem for p-adic groups*, Math. Ann.
  236 (1978), §1, printed p.97 (PDF page 3), source ID
  `provided-5423f8a28c0b7ad5a7f9a07a3d55d399d5162a798fecd70bf11a5d75fa8b9354`,
  SHA-256 `4f437d7ee21c65e43ede0a34b9a6b274cf4d947c23ad7637976bd38fd72fdac5`:
  for an admissible representation `π_1` of `G` and an irreducible admissible
  class `π_2`, "We write `[π_2, π_1]` … for the number of factors in a
  composition series for `π_1` which are equivalent to `π_2`." This notation
  is used in §§2 and 5 of that paper (multiplicities of composition factors of
  induced representations and of exponents).
- Bernstein and Zelevinsky, *Induced representations of reductive p-adic
  groups. I*, Ann. Sci. ENS (4) 10 (1977), §1.2, printed p.443 (PDF page 4),
  source ID `bernstein-zelevinsky-1977-induced-i`, SHA-256
  `8424600228ab72c5937e45edceefcae410a2a0b8f5ebf282185691542aa89092`:
  `JH(π)` is the set of classes of irreducible subquotients and, when
  `l(π) < ∞`, `JH^0(π)` is the set of irreducible quotients of a
  Jordan–Hölder series, "each element `ω ∈ JH(π)` is contained in `JH^0(π)`
  with some multiplicity".

`HasJordanHolderMultiplicity A τ m` is Silberger's `[τ, A] = m`, with the
composition series quantified existentially. Both sources treat the number as
well defined by the Jordan–Hölder theorem without stating it;
`JordanHolderMultiplicityIndependenceStatement` makes that theorem explicit.
The definitions are more general than the sources: any field and monoid,
any carriers, and no admissibility hypothesis. Silberger's restriction to
admissible `π_1` and irreducible admissible `π_2` is a special case.

## Proof sketch for the independence statement

This is the Jordan–Hölder theorem for modules over the monoid algebra `k[G]`.
The invariant subspaces of `A` form a modular lattice, order-isomorphic to the
submodule lattice of `A` as a `k[G]`-module. On a composition series every
graded quotient is irreducible, hence nonzero, so consecutive steps are
covering relations and the series is a composition series of that lattice.
Mathlib's `CompositionSeries.jordan_holder` (`Mathlib.Order.JordanHolder`)
gives a bijection between the factors of two such series that start at `0` and
end at `A`, matching intervals related by the second isomorphism theorem. Each
matched pair of graded quotients is therefore equivalent as representations,
so the bijection preserves the property "equivalent to `τ`" and the two counts
agree.
