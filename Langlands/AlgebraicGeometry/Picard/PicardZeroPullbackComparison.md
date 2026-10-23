# Comparing fibre restrictions under relative rigidified pullback

This module constructs `Langlands.AbelianScheme.fibreComparison_lineBundleIso`
and proves the transport lemmas needed for preservation of geometric
Picard-zero under relative pullback. It is derived internal infrastructure
for the existing `PicardZeroPullbackStatement`, rather than a transcription
of a separate literature theorem. The construction uses the published actual
scheme pullbacks, group operations, relative-space symmetry, and line-bundle
pullback functors. No imported definition is modified.

The parameters are an arbitrary scheme `S : Scheme.{u}`, an abelian scheme
`A/S`, objects `T, U : Over S`, a slice morphism `h : T ⟶ U`, an arbitrary
scheme `V`, and a morphism `s : V ⟶ T.left`. Write `A_T` and `A_U` for the
existing base changes. The additional parameter `m` is a group-scheme
homomorphism from `(A_T)_s` to `(A_U)_(s ≫ h.left)` over `V`. Its hypothesis
`hm` states that the two composites from the source fibre to `A` agree.
There is no hypothesis on flatness, surjectivity, or finiteness of any map.
In particular, `V` need not be a spectrum of an algebraically closed field.

`GroupScheme.translation_hom` shows that a group-scheme homomorphism
intertwines translation by `x` with translation by the image of `x`. The
proof uses `points_translation`, preservation of multiplication, and
associativity. `GroupScheme.isTranslationInvariant_pullback` then pulls back
the given invariance isomorphism at the image of each section. The commuting
translation square and `LineBundle.pullbackComp` identify the two composites.
This result needs only a homomorphism, without an inverse or a surjectivity
condition.

`fibreComparison_relative_map` compares the actual maps from the source
fibre to `U ×_S A`. One route goes through `m`, the target-fibre projection,
and the inverse relative-space symmetry. The other goes through the
source-fibre projection, its inverse symmetry, and `relativeSpace.map h`.
Pullback extensionality reduces their equality to the two projections.
The projection to `A` is `hm`. The projection to `U` follows from the fact
that `m` is a morphism over `V`, the pullback equations, and composition
with `s ≫ h.left`.

For an actual rigidified family `L` over `U`,
`fibreComparison_lineBundleIso` is an isomorphism from the pullback along
`m` of the fibre restriction of `familyLineBundle A L` to the fibre
restriction of the actual relative rigidified pullback of `L` along `h`.
After forgetting the rigidification, the latter is definitionally the
ordinary line-bundle pullback along `relativeSpace.map h`. Both objects
are successive pullbacks of the underlying bundle of `L`.
`LineBundle.pullbackComp` combines these pullbacks; equality of the scheme
maps gives the middle isomorphism; inverse composition comparisons recover
the other parenthesization. No rigidified-pullback coherence proposition is
assumed.

Finally, `isTranslationInvariant_fibre_relativePullback` applies the
group-homomorphism pullback lemma and transports along this constructed
line-bundle isomorphism. It is a statement about a specified fibre and a
specified compatible `m`. This module does not construct `m` and does not
prove `PicardZeroPullbackStatement`. The canonical fibre homomorphism and
its projection identity must be supplied by a separate construction before
the universal geometric-fibre conclusion can be obtained.
