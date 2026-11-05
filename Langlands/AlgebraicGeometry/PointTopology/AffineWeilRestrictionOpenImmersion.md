# Actual open immersions under affine Weil restriction

This is derived construction infrastructure for Brian Conrad, *Weil and
Grothendieck approaches to adelic points*, Example 4.2, printed pp.9–10,
registered as `conrad-2011-weil-grothendieck-adelic-points`, SHA-256
`fe4a9193aff4ef575665b40971f3da32f850a74d87b3f2d0fa28bba26b9cbabb`.
The example invokes Weil restriction along finite locally free maps and its
construction using affine opens. The particular open-locus factorization and
Yoneda proof below are derived from the Library's actual affine construction;
they are not a transcription of a proof in Conrad.

All rings and schemes lie in an arbitrary common universe `u`. Let `A → B` be
a commutative algebra, finite and projective as an `A`-module. Let `X` and `Y`
be actual objects of `Over (Spec B)`, with affine underlying schemes and
locally finite-type structure morphisms. These affine morphisms are therefore
finite type. Let `f : X ⟶ Y` be an actual relative morphism whose underlying
scheme morphism is an open immersion. No field, separability, local-ring or
topological assumption is imposed.

The principal construction is
`affineWeilRestrictionOpenImmersionIso A B f`. It is an actual isomorphism over
`Spec A` from the existing affine Weil restriction of `X` to
`openAffineWeilRestriction A B Y f.left.opensRange`. The latter is the actual
open subscheme of the affine Weil restriction of `Y` constructed in
`AffineWeilRestrictionOpenLocus`, representing restriction of scalars of the
open range of `f`. The isomorphism's hom is the explicitly constructed
`affineWeilRestrictionOpenImmersionFactor A B f`. Its composite with the
open-subscheme inclusion equals the existing coordinate morphism
`affineWeilRestrictionMap A B f`, by
`affineWeilRestrictionOpenImmersionFactor_fac`. Consequently,
`affineWeilRestrictionMap_isOpenImmersion` proves that this existing morphism
is itself an actual open immersion.

This unit supplies the compatibility needed to glue affine pieces. It does not
construct the Weil restriction of a general nonaffine scheme or prove
quasi-projectivity preservation or a local or adelic topology comparison.
Those remain separate obligations.

The implemented construction and proof proceed as follows.

1. `affineWeilRestrictionComparison_postcomp_affine` combines the published
   affine comparison formula with naturality of the coordinate point
   equivalence. Evaluating this identity on the affine representing scheme's
   identity morphism gives `affineWeilRestrictionCounit_natural`. Functoriality
   of actual base change then gives
   `affineWeilRestrictionComparison_postcomp` for every test scheme, without
   an affine or quasi-compactness assumption on that test.
2. `relativeOpenImmersionRangeIso R f` identifies any actual open immersion
   over `Spec R` with its open range over the same base. It uses Mathlib's
   `IsOpenImmersion.isoOfRangeEq` and retains the original structure maps.
   Its hom followed by the range inclusion is `f`; its inverse followed by
   `f` is the range inclusion. This helper has no affineness or finite-type
   premise.
3. Counit naturality shows that the universal morphism for the existing affine
   Weil-restriction map lands in the range of `f`. The all-test range criterion
   from `AffineWeilRestrictionOpenLocus` then shows that this existing map
   lands in the representing open locus. `relativeOpenLift` supplies the
   actual factor morphism, with the stated factorization identity.
4. `affineWeilRestrictionOpenImmersionFactor_comparison` identifies this
   factor on every test scheme `T`: applying the open-locus comparison to
   `p ≫ factor` gives the affine comparison of `p` followed by the hom of
   `relativeOpenImmersionRangeIso B f`. The proof composes with the original
   open-range inclusion, uses the two comparison factorization identities
   and postcomposition naturality, and cancels that monomorphism.
5. The affine and open-locus comparisons are bijective for all test schemes.
   Postcomposition by the range isomorphism is also bijective. These facts
   prove that postcomposition by the factor is bijective on every relative
   Hom set. Mathlib's `isIso_of_yoneda_map_bijective` yields its `IsIso`
   instance, and `asIso` supplies the displayed actual isomorphism. Finally,
   the underlying factor is an isomorphism of schemes, and its composite
   with the actual open inclusion is an open immersion, giving the claim
   about the existing coordinate morphism.
