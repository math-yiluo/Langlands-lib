# Subgroup images in the actual norm-kernel quotient

Author: Worker 200.

This internal, derived adapter compares two existing forms of the quotient
needed by the finite-quotient unitary-detection argument. It uses the
published actual valuation image, its projection and the norm-kernel
quotient equivalence. For a split component it applies the published
`RenardCartan.finiteIndex_splitValuationImage_of_injective`. It introduces
no additional original-source translation or structural assertion.

Let `F : Type u` be a nonarchimedean local field, of arbitrary
characteristic, and let `G` be any group scheme over `Spec F`. Write
`N = rationalCommonNormKernel G`,
`Lambda = rationalDiscreteValuationImage G`, and
`p = rationalValuationImageProjection G`. These are the existing actual
common rational-character norm kernel, discrete copy of the actual
integer-valuation image, and surjective range-restricted valuation map.
The published equality `p.ker = N` is unchanged. No topology on `G(F)`
is selected or needed here.

For any normal subgroup `A` of the actual rational-point group,
`rationalNormKernelSubgroupQuotientEquiv G A` constructs

`(G(F) / N) / map(mk_N, A) ≃* Lambda / map(p, A)`.

Both subgroup images are images of this same `A`. The proof uses
`QuotientGroup.congr` along `rationalNormKernelQuotientEquiv G`.
The identity for the mapped subgroup follows from `Subgroup.map_map`
and the definitional representative formula for that equivalence.
Normality of `A` gives normality of its image in `G(F) / N`; the target
`Lambda` is already commutative, and its subgroup's normality is
installed locally for the quotient congruence. The construction adds no global
commutative-group instance to `G(F) / N`.

`rationalNormKernelSubgroupQuotientEquiv_mk` states that the class of the
class of `g` maps to the class of `p(g)`. The formula is definitional.
`finite_rationalNormKernelSubgroupQuotient` transfers finiteness from
the exact target quotient to the literal iterated quotient, using
injectivity of the equivalence.

Now let `T` be a commutative group scheme and `s : T.toGrp ⟶ G`.
`rationalSplitPointImage_map_valuationProjection` proves

`range(s(F)).map p = RenardCartan.splitValuationImage s`.

Here the right side is the existing range of the composite of `s(F)`
and the range-restricted valuation. The proof is `MonoidHom.map_range`;
the discrete image is definitionally the same group as the existing
valuation image. This identity requires neither centrality nor splitness.

`finite_rationalValuationQuotient_of_splitIndex` takes the explicit
premise that `splitValuationImage s` has finite index and proves

`Finite (Lambda / range(s(F)).map p)`.

It rewrites by the image identity, changes the discrete copy to its
underlying actual image, and uses Mathlib's finiteness instance for a
finite-index subgroup. This is the exact quotient
type accepted by the generic unitary-detection consumer.

`finite_rationalValuationQuotient_of_injective` instead takes a
connected reductive `G`, `hs : IsSplitComponent s`, and
`hinj : Function.Injective (characterRestrict s)`. It obtains the
preceding finite-index premise from the published split-component
lattice bridge. It does not prove or silently drop `hinj`.

`finite_rationalNormKernelCentralImageQuotient` gives the corresponding
finiteness of `(G(F) / N) / map(mk_N, range(s(F)))` from centrality of
`s` and finite index of its actual valuation image. Centrality places
the point image in the abstract group center and hence makes it
normal; the two preceding results then apply.
`finite_rationalNormKernelCentralImageQuotient_of_injective` specializes
this to a split component and the same explicit `hinj`, using the
centrality supplied by `IsSplitComponent`.

The construction imposes no splitness or quasisplitness condition on
the ambient reductive group. It concerns abstract quotients of actual
point groups, without any scheme-quotient rational-point comparison.
It does not establish rational-character restriction injectivity,
unconditional split-center finite index, smooth-character unitarity
on the norm kernel, or the separate local-point structure premises
needed for that unitarity. It defines no alternate representation
framework and proves no Plancherel, spectral-finiteness or analytic
measure assertion.
