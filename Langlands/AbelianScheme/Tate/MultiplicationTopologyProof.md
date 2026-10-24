# Positive multiplication on actual full and away Tate limits

The theorem `Langlands.GroupScheme.Tate.multiplicationOpenEmbeddings` proves
exactly the published proposition
`Langlands.GroupScheme.Tate.MultiplicationOpenEmbeddings G T`, imported unchanged
from `Langlands.AbelianScheme.Tate.MultiplicationTopologyStatement`.
The component theorems are `fullMultiplicationOpenEmbeddings` and
`awayMultiplicationOpenEmbeddings` in the same namespace.

The parameters are precisely an arbitrary `S : Scheme.{u}`, a group object
`G : Grp (Over S)` with `[IsCommMonObj G.X]`, and `T : Over S`.
For every natural `n > 0`, multiplication `x ↦ n • x` is an open embedding
on `Full G T` and on `Away G T m` for every natural modulus `m`.
The topologies are the existing subspace topologies in products of discrete
actual torsion-section groups. No finiteness, divisibility, rank,
torsionfreeness, transition-surjectivity, or comparison hypothesis is added.

## Provenance

This is an internal proof of a derived Library obligation. The imported
statement's Markdown explains the motivating Harris–Taylor Tate-module
conventions and distinguishes this stronger arbitrary-test-scheme assertion
from a theorem quoted in the literature. The argument here is a direct proof
on the actual published carriers; it makes no additional source attribution.

Worker 129 implemented coordinate division and the continuous-retract argument.
The zero-extension and coordinate-continuity pattern is adapted from Worker 18's
published `Langlands.AbelianScheme.Tate.PrimeComparisonProof`.
That module's proved `fullPrimeProductComparison` and
`awayPrimeProductComparison` are imported as theorems. They are not assumed
as extra parameters. No imported statement or dependency pair is changed.

## Full limit: division on an open kernel

Fix `n > 0`. The private `evalKernel` is the kernel of the actual coordinate
homomorphism at order `n`. Its carrier is open because the order-`n` group is
discrete and evaluation is continuous.

For a family `x` in that kernel and a positive order `k`, coherence from order
`n*k` to order `n` says that `k` times the underlying section of `x_(n*k)` is
zero. Thus the same section is a point of `Level G T k`. The helper
`lowerLevel` makes this change of torsion order when its section is annihilated
by the target order, returning zero otherwise. `kernel_coordinate` proves the
annihilation condition for every coordinate used in division, so the fallback
is never used there.

`divideFull` assigns that section to the order-`k` coordinate. If `a` divides
`b`, coherence between orders `n*a` and `n*b`, together with
`(n*b)/(n*a) = b/a`, proves the required coherence of the divided family.
All comparisons pass through the injective homomorphism `toSection` into the
actual additive group of sections.

The inverse identities use coherence from order `n*k` to order `k`, whose
multiplier is `n`. For any full family, division after multiplication by `n`
recovers the family; for a family in `evalKernel`, multiplication after division
recovers that kernel element. The map `multiplyToKernel` lands in this kernel
because every order-`n` coordinate is annihilated by `n`, as proved by the
imported `level_nsmul_eq_zero`.

Each division coordinate is `lowerLevel` composed with evaluation at order
`n*k` and the kernel inclusion. A function out of a discrete level is
continuous, and `continuous_iff_evaluation` then gives continuity of division
for the original topology. Multiplication is continuous because the full limit
is a topological additive group. `fullKernelHomeomorph` packages these two maps
as a homeomorphism from the full limit onto `evalKernel`.
Composing with the open subtype inclusion proves
`fullMultiplicationOpenEmbeddings`. In particular, this argument proves
injectivity; it does not use torsionfreeness as a premise.

## Transfer along a continuous additive retract

The private lemma `nsmul_openEmbedding_retract` concerns topological additive
commutative groups `A` and `B`. Suppose continuous additive homomorphisms
`r : A →+ B` and `s : B →+ A` satisfy `r ∘ s = id`.
Then `s` is a topological embedding. If multiplication by `n` on `A` is an
open embedding, the identity

```text
s ∘ [n]_B = [n]_A ∘ s
```

and the composition criterion for embeddings show that `[n]_B` is an embedding.
Its range is exactly the inverse image under `s` of the range of `[n]_A`:
a multiple in `B` maps to a multiple in `A`, and if `s(y) = n*x`, applying
`r` gives `y = n*r(x)`. The range is consequently open by continuity of `s`.
This proves the transfer lemma without compactness or an open mapping theorem.

## Every away modulus

The published prime-product comparisons supply continuous additive
equivalences from `Full G T` to the product over all primes and from
`Away G T m` to the product over primes coprime to `m`, with continuous inverses.
`extendPrimeProduct` is an additive continuous homomorphism extending the
latter product by zero on excluded primes. Every component is either a
coordinate projection or a constant, which proves continuity.
The existing `primeProductRestrict` is its continuous additive left inverse.

Conjugating this restriction and extension by the two comparison equivalences
produces `r` and `s` for `exists_awayRetract`. Their left-inverse identity
follows from restriction after zero extension and the equivalence identities.
The transfer lemma and the full theorem give
`awayMultiplicationOpenEmbeddings` for every `m` and every positive multiplier.
The proof imposes no coprimality condition on the multiplier. It also covers
`m = 0` (no retained primes) and `m = 1` (all primes retained) uniformly.

Finally `multiplicationOpenEmbeddings` pairs the full result with the result
quantified over all away moduli, exactly as required by the unchanged target.
There is no claim here about rationalization topology, rational monodromy,
restricted products, pairings, or geometric finiteness.
