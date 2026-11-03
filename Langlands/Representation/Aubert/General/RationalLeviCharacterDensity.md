# Finite coordinates and principal open density on the literal rational Levi

Author: Worker 34. The point homeomorphism and full rational norm family
are the unchanged constructions of Worker 289 and Worker 34 in
`RationalLeviNormTopology`.

This unit derives a character-space comparison, finite coordinates and
polynomial nonvanishing density from the existing actual rational-point
constructions. It makes no new original-literature assertion.

Let `F` be any nonarchimedean local field in universe `u`, and let `G`
be an affine group scheme over `F`. Retain the displayed morphism
`i : T.toGrp → G`, cocharacter `ν` and finite subset `I` of the literal
`SimpleRoot i ν`. The actual standard Levi representative is always
`L = Standard.leviScheme i ν (rootSet i ν I)`. No replacement group or
root labeling is chosen. The ambient rational points have
`RationalPointFamily.pointTopology`, the literal subgroup has its
inherited topology, and `L(F)` has `rationalPointTopology F L.X`.
Affineness of `L` follows from its published closed inclusion into `G`.

`leviRationalUnramifiedCharacterHomeomorph` applies
`Plancherel.unramifiedCharactersHomeomorph` to the actual
`leviRationalPointHomeomorph`. Its source uses every rational norm
character of `L`; its target uses the entire
`leviRationalNormCharacters i ν I` family. These are definitionally the
norms related by inverse precomposition in that generic construction.
The evaluation theorems expose precomposition by the inverse point
homeomorphism in the forward direction and by the point homeomorphism
in the inverse direction. This comparison requires no reductivity of `L`
and preserves the actual compact-open subspace topologies.

`leviRationalUnramifiedCharacterCoordinates` additionally takes the
explicit premise `hL : IsConnectedReductive L`. It composes the inverse
character comparison with the published
`rationalCanonicalUnramifiedCharacterCoordinates L hL`, producing a
multiplicative homeomorphism to
`Fin (rationalImageRank L) → ℂˣ`. Its reconstruction theorem gives the
published Laurent monomial in the basis of the actual discrete valuation
image of `L`, evaluated at the inverse image of each literal Levi
element. The formula follows directly from the rational reconstruction
theorem and the forward character comparison. It is not a formula in
an arbitrary supplied coordinate system.

`leviUnramifiedPrincipalOpen` pulls back polynomial nonvanishing along
these coordinates. Membership is exactly nonzero polynomial evaluation
on the underlying complex coordinate values. The preimage identity
identifies it with the pullback of
`rationalUnramifiedPrincipalOpen L hL p` along the inverse character
homeomorphism. Continuity therefore transports openness, and openness
of that homeomorphism transports density when `p ≠ 0`.

Evaluation of a finite product identifies its locus with the intersection
of the selected loci. A product of nonzero polynomials is nonzero, so
the finite intersection is dense. The family index has independent
universe `v`. Rank zero and an empty finite family remain allowed.
Density is also proved for any family containing one such nonzero
principal open locus.

The premise `hL` remains a structural proof obligation for application to
the full rational Weyl-conjugacy target. This unit neither deduces
connected reductivity from the point topology nor adds a premise to that
target. It supplies no generic irreducibility theorem, polynomial
witness for a representation family, equality of induced distributions,
admissibility of finite-length representations, or exact finite-length
K0 identity.
