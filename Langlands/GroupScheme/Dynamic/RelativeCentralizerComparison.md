# Actual relative cocharacter centralizers and identity components

This internal comparison module concerns the existing dynamic
cocharacter centralizer, defined by its actual constant conjugation
orbit on every scheme over the base.

Over an arbitrary commutative ring, every representative of that
centralizer is smooth if its ambient affine group is smooth.
The proof identifies the dynamic centralizer with the existing
whole-group centralizer of the multiplicative-group map. The
arbitrary-ring split-torus centralizer theorem supplies a smooth
representative. Uniqueness of representatives transfers smoothness
to the specified representative. No immersion hypothesis on the
cocharacter and no noetherian hypothesis on the ring are imposed.

`affineCentralizerBaseChangeIso` compares the actual base change
of the existing affine dynamic centralizer construction with the
same construction for the actual base-changed cocharacter. The
comparison applies to arbitrary morphisms between affine bases,
with the stated affine ambient instances, and requires no
smoothness. Its homomorphism followed by the new centralizer
inclusion is exactly the base change of the original inclusion.
It follows from the already proved all-test base-change theorem
and uniqueness of representatives.

The field comparison retains possibly disconnected ambient
groups. Let `G` and `C` be smooth affine groups over any field.
Let `χ` be a specified actual cocharacter into `G⁰`, and let
`j : C → G` be a closed representative of the centralizer of
`χ` followed by `G⁰ → G`.
The file constructs the actual scheme-theoretic intersection
`C ×_G G⁰`. Its second projection represents the centralizer
of `χ` inside `G⁰` on every test scheme. That centralizer is
connected because `G⁰` is smooth, affine and connected.
The first projection is an open and closed immersion into `C`,
by the actual pullback square and the open and closed immersion
`G⁰ → G`. The published characterization of identity components
therefore gives `identityCentralizerIntersectionIso` from this
intersection to the actual `C⁰`.

The isomorphism preserves both projections: its composite with
`C⁰ → C` is the first projection, and its composite with the
actual induced map `C⁰ → G⁰` is the second projection. Hence
that induced map itself represents the internal centralizer
on every test. Finally, `identityComponentCentralizerIso`
identifies `C⁰` with any specified representative of the
internal centralizer. Its two inclusion equations retain both
the map into `G⁰` and its composite into `G`.

The provenance is internal and derived from existing all-test
centralizer base change and restriction, arbitrary-ring
split-torus centralizer smoothness, dynamic connectedness,
actual scheme-theoretic intersections, and the existing
open-and-closed characterization of field identity components.
This supplies comparisons needed when using relative
centralizers in a family with disconnected fibres. It does
not assert reductivity of these centralizers or openness of
the reductive identity-component locus.
