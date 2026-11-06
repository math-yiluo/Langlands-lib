# Passing from affine tests to all tests for torus-subgroup charts

Author: Worker 1735.

The theorem `Langlands.GroupScheme.TorusSubgroupModuli.isOpenChartOfAffines`
proves exactly the published proposition `IsOpenChartOfAffinesStatement.{u}`.
For an arbitrary scheme `S : Scheme.{u}`, group scheme `G/S`, parameter scheme
`U/S`, group scheme `K/U`, and homomorphism `j : K ⟶ G_U`, the affine-test
predicate `IsOpenChartOnAffines j` implies `IsOpenChart j`. There are no added
hypotheses. Both the target family and the source test scheme in the conclusion
may be nonaffine and non-quasi-compact.

## Provenance and dependencies

This is a project-internal Zariski-local argument for the interface in
`TorusSubgroupChartAffineTests`, rather than a transcription of a literature
proof. It imports that published statement unchanged. The equality-locality
step reuses the published module `SubgroupFunctor.ZariskiLocality`.
`HomScheme.AdmissiblePresheaf` supplies restriction of equal ranges, and
`Rational.ParabolicAmbientTransport` supplies invariance of range equality under
the ambient pullback-comparison isomorphism. Morphism gluing and
open-immersion lifting use Mathlib.

## Restriction, equality, and uniqueness

`evaluate_eq_comp` restricts an equality of evaluations along any morphism of
test schemes. Its proof combines `evaluate_comp` with
`evaluate_eq_of_range_eq`.

`evaluate_eq_iff_openCover` proves that two evaluations of closed subgroup
families agree if and only if they agree on every member of an arbitrary open
cover of the test scheme. In the reverse direction, closed immersions give the
relative monomorphisms required by
`SubgroupFunctor.range_eq_iff_baseChange_openCover`. The proof uses
`range_comp_iso_eq_iff` to remove the ambient comparison isomorphism in each
restricted evaluation and then uses `range_baseChangeHom` to identify the
remaining range. Thus the result concerns equality of the represented subgroup
functors, including their values on all further tests.

`IsOpenChartOnAffines.injective_all` restricts two parameters with equal
evaluations to the affine open cover of their source. Affine injectivity makes
the restrictions equal, and the open cover's `hom_ext` gives equality of the
underlying scheme morphisms and hence of the morphisms over `S`.

## Existence of parameters is local on the source

`IsOpenChartOnAffines.exists_evaluate_iff_openCover` treats an arbitrary closed
family and an arbitrary open cover of its source test scheme. A global parameter
restricts to parameters on all the cover members. Conversely, choose such local
parameters. On the scheme-theoretic intersection of two members, their
evaluations agree because both restrict the given family. The already proved
all-test injectivity makes the parameters agree on that intersection.
`Scheme.Cover.glueMorphisms` glues their underlying morphisms. The structure-map
equation is checked with `hom_ext`, giving a morphism over `S`. Finally,
`evaluate_eq_iff_openCover` proves that its evaluation is the given family.
The overlap schemes need not be affine.

## Extending the open-pullback condition

`IsOpenChartOnAffines.isOpen_affineTarget` first keeps the target family on an
affine scheme. It takes the open set supplied by the hypothesis and applies its
criterion to every member of the affine open cover of an arbitrary source test
scheme. Local existence of parameters is equivalent to global existence by the
preceding gluing lemma. Surjectivity of the open cover identifies the local
image-containment conditions with containment of the whole source image.

`IsOpenChartOnAffines.isOpen_all` then chooses an affine open cover of an
arbitrary target `M`. The preceding lemma supplies an open subset `V k` on each
member. Let `W k` be the open subscheme defined by `V k`, and let
`c k : W k ⟶ M` be its inclusion followed by the cover map. Each `c k` is an
open immersion. Applying the local criterion to the inclusion of `V k` shows
that the family pulled back along `c k` has a parameter.

The global open set is the supremum of the open images of the maps `c k`.
If a morphism `b : T ⟶ M` has a parameter, pull the affine cover back to `T`.
At each point the local criterion places the image under `b` in the
corresponding `V k`, and hence in the global open set. Conversely, if the image
of `b` lies in that union, the inverse images of the open images of `c k`
cover `T`. On each resulting open subscheme, `IsOpenImmersion.lift` factors
`b` through the corresponding `c k`. Restricting its parameter gives a local
parameter for `b`; source-local existence then glues these parameters.
This construction does not require a separate comparison of the sets `V k`
on overlaps, a finite cover, or quasi-compactness.

The final theorem retains the closed-subgroup, torus, and smoothness fields of
the hypothesis and supplies the two all-test fields using `injective_all` and
`isOpen_all`. The construction is uniform in the arbitrary universe `u`.
