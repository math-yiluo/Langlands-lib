# Supported recovery from actual finite-series counts

Author: Worker 1080.

`Langlands.glSupportedRelativeRecovery` proves the unchanged proposition
`Langlands.GLSupportedRelativeRecoveryStatement` with all six independent
universes `uF`, `uV`, `uM`, `uW`, `uX`, and `uZ`. The fixed fine/middle data,
all actual support maps, positive ambient rank, arbitrary strictly decreasing
coarse parameter and actual common irreducible outer quotient are retained.
The competitor is irreducible and admissible; its temperedness is never
assumed or derived.

## Series and positive counts

Transport fine irreducibility and cuspidality through the actual shape
equality. Apply the public `glRelativeRegularComparison` to the supported
tempered input `π`. At the given parameter `t` this supplies a positive
count `m` of the actual fine twist `τ` both in the inner opposite Jacquet
module of `πt` and in the composed opposite Jacquet module of its entire
outer induction. Each count contains an actual finite simple composition
series. The strong-head conclusion is not needed here.

For the competing `θ`, apply the public
`glSupportedAmbientJacquetLengthReduction`, discharging its induction-length
premise by `CuspidalSupport.cuspidalInductionLength`. Its actual fine support
surjection supplies finite length and an actual ambient count. Then
`glSupportedRelativeJacquetPositiveBound` supplies an actual positive inner
count `mθ`. This step works for every admissible supported quotient and
uses no temperedness of `θ`. Its implementation twists the actual support
surjection and applies proved refined second adjointness.

## Both coarse inputs inside the common quotient's Jacquet module

The outer quotient `J` is admissible by `relativeCosocleAdmissibility` and
its given surjection from the induction of `πt`. Its standard opposite
Jacquet representation `O` is admissible by the public opposite-admissibility
theorem. Twisting preserves irreducibility and admissibility of both coarse
inputs. The public `ActualQuotientRealBlock.nonzeroAdjunctionMap` applies
proved standard second adjointness to each of the two actual surjections
onto `J`, giving nonzero maps from `πt` and `θt` into `O`. Irreducibility
makes both maps injective. This use of the named helper requires no real
block, isolation or temperedness premise on `θ`.

Suppose the untwisted inputs were inequivalent. Cancel their common scalar
character on a hypothetical twisted equivalence using `untwistIntertwining`;
its unchanged underlying bijection would give an untwisted equivalence.
Thus the twisted inputs are inequivalent too.

The private algebraic helper `product_embedding` identifies each simple
input with its actual image via `MultiplicityAdditivityProof.source_equiv_range`.
Public irreducibility transport and
`NormalRestrictionOrbit.isAtom_of_isIrreducible` make these images atoms.
If the images were equal, the two image equivalences and the literal
subrepresentation equality would identify the inputs. Distinct atoms are
disjoint. Their sum map from the actual product is therefore injective:
a zero sum of vectors in the two disjoint images forces each vector to
vanish. No semisimplicity of the whole Jacquet representation is asserted.

## Finer Jacquet transitivity and the strict inequality

Apply `normalizedRefinedOppositeJacquetMap_injective` to this product
embedding. Its target `O` is smooth by its proved admissibility. The public
binary-product equivalence identifies the source with the product of the
two inner opposite Jacquet modules. The public
`Parabolic.normalizedOppositeRefinementTransitivity` identifies the target
with the actual composed opposite Jacquet module `C` of `J`. These actual
equivalences construct an injective intertwiner from the product into `C`.

The actual composed opposite Jacquet map of the supplied outer surjection
from the induction of `πt` is surjective, as checked on coinvariant
representatives. The private helper `count_of_surjective` applies
`jordanHolderShortExactDecomposition` to its actual kernel sequence. It
constructs an actual composition-series count `mJ` for `C`, with `mJ ≤ m`.
Thus this is an existence and count assertion, not an equality between
potentially false multiplicity predicates.

Public product additivity gives count `m + mθ` on the product of the inner
Jacquet modules. Injective monotonicity along the constructed intertwiner
gives `m + mθ ≤ mJ`. Together with `mJ ≤ m` and `0 < mθ`, arithmetic yields
a contradiction. Consequently the untwisted `π` and `θ` are equivalent.

## Source and conventions

This is an internal implementation of the strict-multiplicity argument in
A. J. Silberger, *The Langlands quotient theorem for p-adic groups*
(1978), Proposition 5.7, printed pp.101–102, with the supported equality
from Lemma 5.6 and the setup on p.99. The registered original is
`provided-5423f8a28c0b7ad5a7f9a07a3d55d399d5162a798fecd70bf11a5d75fa8b9354`,
SHA256 `4f437d7ee21c65e43ede0a34b9a6b274cf4d947c23ad7637976bd38fd72fdac5`.
Worker 1080 read the whole article and inspected the relevant formula images.

The proof imports the independently proved supported all-regular comparison;
it does not apply unrestricted Lemma 5.3 to an unsupported representation.
Upper normalized induction retains right translation and positive upper
half-modulus covariance, opposite Jacquet normalization uses the positive
upper half-modulus, and the absolute value is `q^(-valuation)`. The actual
fine twist is `-vB + restrict(t)`. There is no canonical quotient assumption,
additional premise, universe equality, rank restriction, or downstream
Langlands classification input. Arbitrary-tempered quotient reflection is
proved separately.
