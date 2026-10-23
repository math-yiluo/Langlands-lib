# Positive multiplication on actual Tate limits

This file states the topological lattice condition needed to equip rational
Tate modules with a topology that contains the integral module as an open
subgroup. It defines propositions; it does not prove them or install a topology
on a rationalization.

## Source and derived scope

Harris–Taylor, *The Geometry and Cohomology of Some Simple Shimura Varieties*
(2001), Chapter I, printed p.18 (PDF p.26), defines the full Tate module using
all positive torsion orders, the away module using orders coprime to the
excluded primes, and their rationalizations by tensoring over the integers
with the rationals. The registered source is
`harris-taylor-2001-geometry-cohomology-simple-shimura`, SHA256
`5be28164b61d6f6cc28dd9e6b990d669504f3470860b230ebbc97e3da10af56b`.

The positive-multiplication condition here is derived infrastructure for those
constructions; it is not presented as a theorem quoted from that page. The
generality of a commutative group scheme and an arbitrary test scheme is also
derived. The statement concerns the algebraic torsion-section inverse limits
already defined in `Integral`, with the existing topology inherited from the
product of discrete torsion groups.

## Exact statements

Let `G` be a group object over a scheme `S`, with the commutativity instance
`IsCommMonObj G.X`, and let `T` be a scheme over `S`. A coordinate of
`Full G T` at a positive integer `k` is an actual section killed by `[k]`.
For `k ∣ l`, coherence uses multiplication by `l / k`.
`Away G T m` retains the positive `k` satisfying `Nat.Coprime k m`.

`Langlands.GroupScheme.Tate.FullMultiplicationOpenEmbeddings G T` says that,
for each natural number `n > 0`, the existing map

`Full G T → Full G T`, `x ↦ n • x`

is `Topology.IsOpenEmbedding`. This includes injectivity, the embedding
property for the existing topologies, and openness of the image. The
multiplication is the natural-number action on the additive group of coherent
families, so it is coordinatewise multiplication on actual torsion sections.

`AwayMultiplicationOpenEmbeddings G T m` asserts exactly the same property
for `Away G T m`. The quantifier is over **every** positive `n`, including
integers that are not coprime to `m`.

`MultiplicationOpenEmbeddings G T` is the conjunction of the full assertion
and the away assertion for every natural modulus `m`. In particular, no
primality assumption on `m` is implicit. At `m = 1` all positive orders are
retained. At `m = 0` only order one is retained, so the target still expresses
the corresponding multiplication condition on that trivial limit.

The three abbreviations in `Langlands.AbelianScheme.Tate` specialize these
same propositions to `A.toGrp` for an actual abelian scheme `A`. A geometric
fibre specialization takes `T = Over.mk s`. No comparison equivalence or
replacement carrier is supplied as an input.

## Hypotheses and remaining proof

No finite-level finiteness, finite étaleness, divisibility of the ambient
section group, finite rank, or surjectivity of the transition maps is assumed.
Compactness is a separate condition, supplied for the intended geometric
application by the existing finite-level results. These propositions retain
the actual product-subspace topology even when the discrete levels are
infinite.

The full assertion is motivated by the identity that the image of `[n]`
is the kernel of evaluation at `n`. When a coherent family has zero
`n`-coordinate, its `nk`-coordinate is killed by `k`; these coordinates give
a candidate division-by-`n` family. This also suggests continuity of the
inverse on the image. The away assertion additionally requires handling the
prime factors of `n` excluded by `m`. These observations explain the target;
none is proved in this statement file.

A separate proof must establish the exact conjunction
`Langlands.GroupScheme.Tate.MultiplicationOpenEmbeddings`. In particular,
torsionfreeness and the open-embedding property must not be assumed as extra
hypotheses. The statement makes no assertion for an arbitrary selected
predicate of torsion orders. It also makes no rational topology, continuous
rational monodromy, restricted-product comparison, or pairing claim.
