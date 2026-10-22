# Canonical prime-power coordinates of actual Tate limits

This module constructs the maps from actual integral Tate limits to their
prime-adic components and to the products of those components. It proves
continuity, compatibility with away restriction, and naturality for actual
group-scheme homomorphisms. It does not assert that the comparison maps are
isomorphisms. Those exact-map assertions belong to a subsequent statement
unit and a separate proof task.

## Actual carriers and coordinate projections

Work first in `Langlands.GroupScheme.Tate.PrimeComparison`. Let `G` be a
commutative group object in schemes over `S`, and `T : Over S` a test scheme.
The imported `GroupScheme.Tate.Integral G T P` consists of families of actual
`n`-torsion sections, indexed by positive `n` satisfying `P n`, compatible
with multiplication by `m / n` when `n` divides `m`.
`GroupScheme.Tate.PrimeAdic.Integral G T p` is the existing coherent sequence
of actual `p^n`-torsion sections, with its `ℤ_[p]`-module structure and its
subspace topology from the product of discrete torsion levels.

For a prime `p`, represented by `[Fact p.Prime]`, and
`hP : ∀ n : ℕ, P (p ^ n)`, the imported
`Langlands.TateTwist.Divisibility.primePowerIndex P p hP n` is the selected
positive index `p^n`. This module reuses that arithmetic helper from
`TwistPrimeComparison`. Positivity follows from primality of `p`. In particular,
the sequence includes exponent zero, corresponding to torsion order one.

`toPrime G T P p hP` reads precisely these coordinates of a compatible
family. It is an additive homomorphism. Its defining compatibility is the
original divisibility compatibility at `p^n ∣ p^(n+1)`; this is exactly the
successive transition in the imported prime-adic module. The lemma
`evaluation_toPrime` identifies evaluation of its output at exponent `n`
with evaluation of its input at `primePowerIndex P p hP n`.
`continuous_toPrime` follows from continuity of the original evaluations,
continuity into a product, and the induced topology on the coherent subtype.

`fullToPrime` specializes `P` to the always-true predicate. `awayToPrime`
specializes to `Nat.Coprime n m`, with an explicit hypothesis
`Nat.Coprime p m`; its index membership follows from coprimality of powers.
The excluded modulus `m` may be any natural number. For prime `m`, this is
the usual away-from-`m` system. The corresponding continuity lemmas are
`continuous_fullToPrime` and `continuous_awayToPrime`.
`awayToPrime_restrictAway` proves that extracting a retained component after
restricting the full limit gives the original full component. This equality
is definitional, since both sides read the same torsion coordinates.

## Product comparison maps and restriction

`PrimeProduct G T` is the dependent product of the existing integral
prime-adic modules indexed by `Nat.Primes`. The local `primeFact` instance
supplies primality for each index. The imported
`Langlands.TateTwist.Divisibility.AwayPrime m` is the subtype of these
primes coprime to `m`; `AwayPrimeProduct G T m` is the product over this
subtype. Both products carry their existing coordinatewise additive
structures and product topologies.

`toPrimeProduct G T` and `toAwayPrimeProduct G T m` assemble respectively
`fullToPrime` and `awayToPrime` in every retained coordinate. They are actual
additive maps from the full and away Tate limits, not chosen comparison
isomorphisms. `continuous_toPrimeProduct` and
`continuous_toAwayPrimeProduct` follow from the component continuity laws.

`primeProductRestrict G T m` forgets the prime components not coprime to `m`.
It is additive and continuous (`continuous_primeProductRestrict`). The
square formed by full and away comparison maps and the two restrictions
commutes by `toPrimeProduct_restrictAway`. The proof is definitional.

## Homomorphism functoriality

For an actual group-scheme homomorphism `f : G ⟶ H`, `toPrime_map` says that
reading a prime-power coordinate commutes with the existing map induced by
`f` on torsion sections. This is definitional: the underlying operation is
postcomposition by `f` on both sides.

`primeProductMap T f` and `awayPrimeProductMap T m f` take the product of
the already constructed `PrimeAdic.map` at the appropriate primes. The
lemmas `toPrimeProduct_map` and `toAwayPrimeProduct_map` express naturality
of the comparison maps. Both follow directly from their coordinate
formulas. `primeProductRestrict_map` similarly proves naturality of product
restriction by definitional equality.

`continuous_primeProductMap` and `continuous_awayPrimeProductMap` compose
the continuous coordinate projection with the imported continuous
prime-adic map, then use continuity into a product. The `_id`, `_comp`, and
`_mul` lemmas for both product maps follow by additive-map extensionality,
function extensionality over the primes, and the corresponding imported
`PrimeAdic.map` identity. Composition is in categorical order: first `f`,
then `g`, induces the composite of the map for `f` followed by that for `g`.
Multiplication of group-object homomorphisms is the multiplicative notation
for their pointwise group law; it becomes addition of the induced additive
maps.

## Bundled abelian schemes

The namespace `Langlands.AbelianScheme.Tate.PrimeComparison` specializes
the product carriers, comparison maps, and product homomorphisms to
`A.toGrp` for an actual `A : AbelianScheme S`. Its comparison maps have the
existing `Full A T` and `Away A T m` as domains. It exposes their continuity
and naturality, and `primeProductMap_add` and `awayPrimeProductMap_add`
translate the group-object law into addition of actual abelian-scheme
homomorphisms. The remaining generic laws apply to this specialization
through these abbreviations.

Taking `T = Over.mk s` for an actual geometric point `s` gives the desired
maps on the torsion fibres. The imported `kernelLevelEquiv` and
`fibreLevelEquiv` identify the section-based levels with the points of the
actual multiplication kernels and their fibres; no new abstract torsion
groups are supplied in this module.

## Provenance and limits

The source convention is Harris–Taylor, *The Geometry and Cohomology of
Some Simple Shimura Varieties* (2001), Chapter I, printed p.18 (PDF p.26):
the full Tate module is the limit over positive torsion orders, and the
away version restricts those orders by coprimality. The registered source is
`harris-taylor-2001-geometry-cohomology-simple-shimura`, SHA-256
`5be28164b61d6f6cc28dd9e6b990d669504f3470860b230ebbc97e3da10af56b`.

The coordinate maps and naturality laws here are derived from those limit
conventions and the published actual `Integral` and `PrimeAdic`
constructions. The arbitrary test scheme and commutative group scheme are
explicit generalizations. The construction follows the published
`Tate/TwistPrimeComparison` coordinate-projection pattern by Worker 92,
adapted by Worker 142 to actual group-scheme torsion and actual
homomorphisms. It is not a statement that the source presents these Lean
interfaces or proves a decomposition theorem at the cited location.

No finiteness, invertibility of torsion orders on `S`, or characteristic-zero
assumption is required for these coordinate maps and their intrinsic laws.
Such hypotheses remain necessary when invoking separate finite-étaleness
or full-rank results. This unit proves neither bijectivity nor inverse
continuity of the product comparison maps, and makes no claim about scalar
comparison with profinite integers, rationalization, restricted products,
Weil pairings, or monodromy.
