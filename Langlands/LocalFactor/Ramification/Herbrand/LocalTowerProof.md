# Herbrand's quotient theorem and the tower laws

`Langlands.Ramification.Local.finiteHerbrandQuotientTower` proves all six clauses
of `FiniteHerbrandQuotientTower` for the supplied realizations `T` of `L` and `S`
of `E`. The fields `K₀`, `K`, `L`, and `E` lie in independent universes. The
theorem works in either characteristic with the base structure required by
`LocalField.TopologicalData`. The subgroup formula and the two fixed-field
quotient formulas come from `LocalQuotientProof`.

## The restriction kernel and its integer ring

For the independently presented field `E`, let `H` be the kernel of normal
restriction from `Gal(L/K)` to `Gal(E/K)`. The automorphisms in `H` fix the
image of `E` pointwise. Forgetting that an automorphism fixes `E` thus gives a
multiplicative equivalence from `Gal(L/E)` to `H`. The equivalence preserves
the action on the integers of `L` and hence the orders of its lower groups.

The Galois fixed-field property identifies the image of `E` with the elements
of `L` fixed by `H`. The comparison `QuotientBridge.algHom_mem_integers_iff`
applied to the `K₀`-algebra map `E → L` identifies the supplied integers of
`E` with the fixed subring in the supplied integers of `L`. The map intertwines
the two actions under the isomorphism from `Gal(L/K)/H` to `Gal(E/K)` induced
by restriction. Consequently the lower groups on the fixed subring correspond
to the lower groups of `E/K` and have the same orders.

## Real indices

- `herbrandPhiTower` applies the rational composition theorem to `H`, using
  the lower quotient formula from `LocalQuotientProof` and the comparisons of
  lower group orders above. The Herbrand functions are the identity on
  nonpositive indices. Continuity extends the equality on rational indices
  to every real index.
- `herbrandPsiTower` applies the injective function `φ_(L/K)` to the desired
  equality and simplifies with the phi tower law and the inverse identities.
- `upperRestrictionCompatibility` derives the scalar tower `K₀ → E → L`
  inside the proof by composing the given algebra maps. At `v = -1`, both
  upper groups are full and restriction is surjective. For `v > -1`, each
  upper group is constant from `v` to some nonnegative rational index. The
  smaller of these two rational indices works for both groups. The rational
  upper quotient theorem at this common index, followed by the equivariant
  transport from the fixed subring, gives the formula for normal restriction.

## Source

Jean-Pierre Serre, *Local Fields*, translated by Marvin Jay Greenberg,
GTM 67, Springer (1979), IV §1 Proposition 2 (p. 62) and IV §3
Lemma 5 and Propositions 14–15 (pp. 73–75). The registered source is
`serre-1979-local-fields`, `/home/taskhub/central-library/Serre--Local Fields--1979.pdf`,
SHA-256 `109b461d42915da70771c70c4b551a363fc1f33412331ae2671c5c85be433112`.
