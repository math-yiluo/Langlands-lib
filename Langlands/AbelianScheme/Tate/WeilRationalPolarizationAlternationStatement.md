# Conditional alternation of rational and adelic polarization Weil pairings

`RationalPolarizationWeilAlternationStatement` asserts alternation of
the existing rational and adelic Weil pairings pulled back in the
second variable by an actual relative polarization. It is a
proposition definition; this file does not prove it.

The homomorphism `lam` goes from the actual abelian scheme A over a
quasi-separated base S into its constructed dual abelian scheme. The
hypothesis is the published `IsPolarization` predicate: an actual
isogeny with an ample Mumford presentation on every geometric fibre
after a possible field extension. The statement retains the seven
tensor/Picard propositions, the square and universal-base-change
propositions required by that predicate, the actual dual witness and
geometry, and the inverse Poincare line bundle with its evaluation.

`RelativeFiniteWeilTransitionStatement` and
`RelativeFiniteWeilAlternationStatement` are explicit theorem
hypotheses. The first is needed to construct the inverse-limit Weil
pairings. The second supplies the relative finite scheme-diagonal
identity for actual polarizations. The conclusions hold for every
test scheme T over S, including nonreduced test schemes.

The four conclusions use Mathlib's `LinearMap.IsAlt`, which means
that pairing any input with itself gives zero:

- The rational pullback is alternating over Q for every selected
  predicate on positive torsion orders. This includes the full system
  and orders coprime to any natural modulus.
- The rational prime-adic pullback is alternating over the p-adic
  rationals for every prime p, expressed by `Fact p.Prime`.
- The adelic bundle of the selected rational pullback is alternating
  over the existing finite adele ring of Q, for every explicit
  `RationalProfiniteIntegerAdeleComparison`. The full adelic pairing
  is the case retaining all positive orders.
- The away adelic pullback is alternating over the existing
  `PrimeToFiniteAdeles m` for every natural modulus m and every coupled
  `PrimeToRationalProfiniteIntegerAdeleComparison h m`.

The full scalar comparison and its coupled away comparison act on both
inputs and their corresponding twist. The rational selected carriers
are Q tensor over Z with the actual selected integral inverse limits.
The rational prime-adic carriers are the p-adic rationals tensor over
the p-adic integers with the actual integral prime-adic inverse limits.
All outputs remain in the respective constructed rational
roots-of-unity twists. No compatible primitive roots or twist
trivialization is chosen, and the inherited convention is
beta(lam(y))(x).

This is an internal consequence target. The intended route starts from
the existing integral polarization alternation target: the relative
finite diagonal identity makes every integral inverse-limit coordinate
zero. Scalar extension then preserves alternation. A proof must handle
the mixed terms in tensor sums, using the skew identity implied by
integral alternation, as well as the pure-tensor diagonal formula. The
adelic conclusions have the same underlying functions as their
rational pullbacks, so follow from their existing application
identities. A separate proof must implement this route or another
valid one without changing the target.

The deep relative finite alternation and transition theorems remain
explicit dependencies. This statement adds no axiom and claims no
unconditional alternation, nondegeneracy, perfectness, continuity, or
monodromy equivariance.
