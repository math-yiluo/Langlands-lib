# Finite Galois descent of a represented unipotent radical

This internal prerequisite by Worker 1333 completes the descent of a
supplied represented unipotent radical through a finite Galois extension.
It uses Worker 1487's unipotence-reflection proof unchanged. The existing
group-scheme, subgroup-functor and `IsUnipotentRadical` predicates are
unchanged. All schemes and fields have an arbitrary common universe `u`.

For an affine group scheme `G` over a field `k`, a finite Galois extension
`L/k`, and a supplied inclusion `i : U ⟶ G_L` satisfying
`IsUnipotentRadical i`, the definition
`IsUnipotentRadical.finiteGaloisRadical` constructs an actual group
scheme `U₀` over `k`, an actual inclusion `j : U₀ ⟶ G`, and an actual
group-scheme isomorphism `e : (U₀)_L ≅ U`. Its proofs assert
`IsUnipotentRadical j` and the exact equality
`(GroupScheme.baseChange (algebraBaseMap k L)).map j = e.hom ≫ i`.
Thus the conclusion includes the full represented radical predicate,
as well as recovery of the source and the inclusion.

## Normality

`SubgroupFunctor.isNormal_range_of_baseChange` considers an arbitrary
monomorphism `i : H ⟶ G` over a scheme `S` and a quasi-compact, flat,
surjective map `b : S' ⟶ S`. If the base change of the represented image
`range i` is normal, then `range i` is normal. No closedness assumption is
needed for this result.

For a test scheme over `S`, the proof pulls a conjugating point and a
subgroup point to the test scheme's pullback over `S'`. Normality there
puts the conjugate in the pulled-back image. The base-change point
equivalence preserves multiplication and inverses. The projection from
the pulled-back test scheme is an effective epimorphism, so the published
`mem_range_of_comp_mem_range` descends the conjugate's membership in the
original monomorphism's image. Thus the conclusion concerns all relative
test schemes.

## Smoothness and connectedness

`smooth_of_baseChange` reflects smoothness of the structure morphism of
an arbitrary group scheme under a quasi-compact, flat, surjective base
change. The proof specializes Mathlib's `Smooth.DescendsAlong` instance
and `MorphismProperty.of_pullback_snd_of_descendsAlong` to the actual
pullback square.

`connectedSpace_of_baseChange` reflects connectedness of the underlying
scheme under any surjective base change. The first projection of the
actual pullback is continuous and surjective, so its connected source
has connected image equal to the original scheme.

## Greatestness

`IsUnipotentRadical.greatest_of_baseChange` considers an affine group `G`
over any field `k`, a closed subgroup inclusion `i : U ⟶ G`, and any
field extension `K/k`. It assumes that the base change of `i` satisfies
the existing `IsUnipotentRadical` predicate. For every smooth connected
normal unipotent closed subgroup `j : H ⟶ G` over `k`, it concludes
`range j ≤ range i`.

Closedness in affine `G` makes `H` affine. The proof pulls `j` back to
`K`: closedness and smoothness are preserved, smooth affine connected
groups over a field remain connected after base change, unipotence is
preserved by the published coordinate-algebra argument, and normality of
the all-test image is preserved. Greatestness of the supplied radical
over `K` gives image containment there.
`SubgroupFunctor.le_range_of_baseChange_le` reflects that containment
through the field extension, which is fpqc.

## Reflection of the full radical predicate

`IsUnipotentRadical.of_baseChange` considers a closed inclusion
`i : U ⟶ G` into an affine group over any field `k`, and any field
extension `K/k`. If its actual pullback satisfies
`IsUnipotentRadical`, the theorem proves `IsUnipotentRadical i`.

Closedness makes the source affine and the inclusion monic. The
preceding reflection lemmas supply smoothness, connectedness, normality
and greatestness over `k`. Worker 1487's
`IsUnipotent.of_baseChange` supplies unipotence over `k`; this theorem
uses the actual coordinate-cogroup comparison and contraction of a
scalar-extended stable subspace. Closedness itself remains an explicit
hypothesis of this reflection theorem. These six properties are exactly
the fields of the existing represented radical predicate.

## Changing the source

`SubgroupFunctor.range_iso_precomp` proves that replacing an inclusion's
source by an isomorphic group scheme leaves its image on every relative
test scheme unchanged. The forward implication composes a witness with
the isomorphism, and the reverse implication composes a witness with its
inverse.

`IsUnipotentRadical.precomp_iso` transports the full predicate through
such a source isomorphism. Closedness and smoothness are preserved by
composition with the isomorphism; the underlying scheme homeomorphism
transports connectedness, and the existing isomorphism transport
transports unipotence. Equality of represented images transports
normality and greatestness.

## The finite Galois construction

The imported `Rational/UnipotentRadicalDescent` constructs the actual
finite Galois source datum, its cocycle, its affine solution, and the
descended inclusion. It proves closedness and the exact recovery
equation. It requires the radical over `L` as an input, without
requiring a source datum, a cocycle or a descended source as an
additional premise.

`IsUnipotentRadical.finiteGaloisInclusion_isUnipotentRadical` applies
the full reflection theorem to that constructed inclusion. The recovery
equation identifies its pullback with the original radical inclusion
precomposed by the constructed source isomorphism. The source transport
lemma proves this pullback is a radical. The reflection theorem then
proves all six radical properties over `k`.

Finally, `IsUnipotentRadical.finiteGaloisRadical` packages the
constructed source, inclusion, source isomorphism, full radical predicate
and recovery equation in a dependent sum. It adds no existence
hypothesis beyond the supplied radical over `L`.

## Provenance and scope

These results are internal deductions from the published fpqc image
descent, field-extension fpqc, geometric connectedness and unipotence
preservation APIs, Mathlib's smooth descent and topological
connected-image theorems, the finite Galois source-descent construction,
and Worker 1487's unipotence reflection. The accompanying
`Unipotent/FieldReflectionProof` pair is reused without edits. Its
independent proof and source explanation remain in that pair.

The reflection results allow arbitrary field extensions, with no
characteristic, perfection, infinitude or splitness restriction. Only
the final source-descent construction requires the extension to be
finite Galois. The ambient group's affineness is an explicit hypothesis;
its smoothness, connectedness and solvability are not required here.

The construction starts with a represented radical over `L`. Radical
existence over a geometric field, finding a suitable finite Galois field
of definition, splitness in the torus-generated situation, and the
maximal-torus conjugacy theorem remain obligations of the host proof.
