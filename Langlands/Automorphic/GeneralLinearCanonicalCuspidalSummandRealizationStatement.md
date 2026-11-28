# Cuspidal summand realizations on the canonical general linear quotient

`Langlands.Automorphic.DiscreteHeckeIsolation.GeneralLinearCanonicalCuspidalSummandRealizationStatement`
uses a number field `F : Type` with compact additive adele quotient. Let `P` be an irreducible
closed invariant subspace of canonical `L²([GL_{r+1}])`, contained in the full almost-everywhere
cuspidal subspace. There is a cuspidal operator realization `S` of `GL_{r+1}` and an injective
complex-linear map `j` taking the forms of `S` to their classes for the canonical measure.
The closure of its range is `P`. At each finite place `p`, the map intertwines the matrix-model
local action on the forms of `S` with `canonicalL2LocalAction F r p`, which inserts a local
matrix at `p` before acting on `L²`.

The existence and density are the summand-to-realization direction of Getz–Hahn, Theorem 9.7.3
after Theorem 9.7.1 and Lemma 9.7.2. The Library's `GeneralLinearCuspidalSummandRealizationStatement`
expresses this on a positive-torus quotient. For the chosen canonical split component, its
quotient compares with `[G]` by `RestrictionSplitCentre.canonicalL2Equiv`. The canonical form
class relation specifies the image of each vector. Full support of quotient Haar measure makes
the class map faithful on continuous functions. The local intertwining follows because right
translations of these functions descend to the same right translations on their classes.

J. R. Getz and H. Hahn, *An Introduction to Automorphic Representations*, Springer, 2024,
`getz-hahn-2024-automorphic-representations`, SHA-256
`a125cf9c0f445972cbbd3552b4fb9905ca948108a05880f90eaa43558d09a507`, (2.20), p. 68 (PDF p. 85),
and Theorem 9.7.3, pp. 265–266 (PDF pp. 277–278), with Theorem 9.7.1 and Lemma 9.7.2, p. 264
(PDF p. 276).
