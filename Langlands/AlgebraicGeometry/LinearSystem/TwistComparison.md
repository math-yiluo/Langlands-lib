# The line bundle of a linear-system morphism

For a scheme `X` over an arbitrary commutative ring `K`, an actual line bundle
`L` on `X`, and `n + 1` global sections `s_i` with no common zero,
`linearSystemTwistIso` constructs an isomorphism

`linearSystemMap(p, s)* O(1) ≅ L`.

Here projective space is the existing polynomial Proj and `O(1)` is its actual
degree-one twist. The coordinate identity
`linearSystemTwistIso_coordinate` says that the isomorphism takes the
pullback of each actual coordinate section to the specified section `s_i`.
The schemes have an arbitrary common universe, and neither a nonzero-ring
assumption nor a restriction on `n` is imposed.

For a map `p : X → S` to any scheme, `relativeLinearSystemTwistIso`
constructs the corresponding isomorphism from the pullback of
`RelativeProjectiveSpace.twistOne S n` to `L`. Its coordinate identity
preserves all relative coordinate sections. This uses the existing relative
linear-system map, the definition of the relative twist as pullback from
the lifted-integer projective space, the canonical pullback-composition
isomorphism, and the integral projection identity. Thus it compares actual
module sheaves over every base scheme.

The implementation first transports local coefficient identities. On an
inverse-image open, restriction of a pulled-back global section is the
pullback-adjunction unit applied to its restriction. Linearity transports
a coefficient relation, and a further restriction gives a global relation
when the map lands in that open. Conversely, the unit along the inclusion
of an open subscheme is injective on sections over that open. The proof
compares it with the restriction adjunction, whose unit there is an
isomorphism. Hence a coefficient identity can also be recovered from its
pullback to the open subscheme.

For a homogeneous localization chart map, the pullback of an actual
degree-zero localization section is its defining `awayLift`. This follows
from the basic-open/Spec comparison and the global-sections adjunction.
Specializing to `X_j / X_i` shows that a point map pulls back the coordinate
ratio to the existing `sectionRatio` of `s_j` and `s_i`. The known local
relation between the projective coordinate sections then gives that same
relation after pullback. On any open contained in the frame locus of `s_i`,
the restriction identity for the glued linear-system map, pullback
composition, and injectivity along the open inclusion transfer every
relation `s_j = a s_i` to the pulled-back coordinate sections.

The general helper `exists_iso_of_matching_sections` compares two module
sheaves with indexed global sections. It assumes that the first sections'
frame loci cover, that the corresponding second sections are frames there,
and that every local coefficient relation in those frames is shared.
The published theorem
`Scheme.Modules.exists_iso_app_eq_of_isFrameOn_of_eq_smul` glues the
restriction-stable pairs of frames into an actual isomorphism. On each
frame locus, every specified section has a coefficient in that frame;
linearity and the shared coefficient relation show that the isomorphism
preserves it locally. Sheaf uniqueness gives preservation globally.
For the linear-system application, the full inverse image of each
coordinate chart is exactly the frame locus of `s_i`, so the second
sections are indeed frames on the same covering opens. Choosing the
resulting isomorphism defines `linearSystemTwistIso`.

This is an internal consequence of the existing actual pullback,
homogeneous-localization, coordinate-generation-open and frame-gluing
constructions. The frame-gluing theorem is imported from the published
`Langlands.AnthropicFLT` port; this module does not reimplement its gluing.
The geometric setup is the polynomial specialization of Stacks Project,
Section 27.14, Lemma 27.14.1, in registered source
`stacks-very-ampleness-support-2026-10-29`, while the proof above is the
implemented internal ratio-and-frame argument. It constructs no immersion,
projective bundle from a nontrivial locally free sheaf, or moduli space.

The equality-of-maps step reuses
`RelativeProjectiveSpace.pullbackSection_comp_eq` from the existing twist
module, with its unchanged pullback-composition and equality-transport formula.
