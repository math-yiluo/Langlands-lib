# Graded pieces of the fixed parabolic support filtration

This proposition isolates the natural graded identifications still needed for
the normalized p-adic geometric lemma. It refers to the actual support-image
filtration defined in `ParabolicSupportFiltration`; it does not permit choosing
a different filtration. This module states the result and does not prove it.

## Data and conclusion

`PadicParabolicSupportGradedTheorem` quantifies over every prime, actual finite
p-adic extension, supplied compatible topology, positive rank, and pair of block
shapes. Field and representation-carrier universes remain independent. It then
accepts any finite enumeration `e` of the minimal permutations and any actual
ordered orbit decomposition `s` whose representative at `i` is the permutation
matrix for `e i`. Openness of all initial orbit unions is part of the existing
`OrderedDoubleCosets` datum. The orbit represented by `w` is `P_B w⁻¹ P_C`.

For every choice of source and target block refinements and proofs of all three
standard-intersection equalities on both sides, the conclusion is
`HasGradedPieces` for the fixed `parabolicJacquetSupportFiltration T B C s`.
Thus, for each index `i`, it asserts a natural isomorphism of functors from the
successive quotient of this filtration to the existing
`geometricPieceFunctor` for `e i`. The latter is normalized inner Jacquet,
inverse-conjugation transport, and normalized inner induction. The Levi
equalities only relabel the identical actual groups; the full triples are
hypotheses of the comparison. The target category is
`Rep.{max uF uV} ℂ (C.Levi F.Carrier)` and the source is the full category
`SmoothRep.{0,uF,uV} ℂ (B.Levi F.Carrier)`.

The comparison includes the normalizing characters already built into both
functors: positive half modulus for induction and inverse positive half for
Jacquet. It allows no extra residual character in the geometric piece. It is
natural for all morphisms of smooth representations, without admissibility,
finite-dimensionality, irreducibility, or finite-length restrictions.

## Source correspondence and scope

The source is Bernstein–Zelevinsky, *Induced representations of reductive
p-adic groups I* (1977), registered as
`bernstein-zelevinsky-1977-induced-i`, SHA-256
`8424600228ab72c5937e45edceefcae410a2a0b8f5ebf282185691542aa89092`.
Section 5.2 (printed 460) treats any orbit enumeration with open initial unions.
Sections 5.3–5.4 (printed 461) choose the support filtration and identify the
successive quotients with the locally closed orbit functors; sections 5.5–5.17
construct the comparison. Section 6.4 (printed 468–469) specializes to the
minimal inverse permutation representatives and cancels the correction
character to obtain section 2.12 (printed 448).

The formulation is a derived, concrete GL specialization using the Library's
actual normalized induction, Jacquet quotient, and refinement functors. BZ's
localized support subspaces identify with their images by exactness; the
Library's fixed filtration is defined directly by those images. Establishing
this comparison, compactness of the parabolic quotient for the smooth-induced
model, and cancellation of the normalizing characters are proof obligations,
not assumptions or conclusions already established by the filtration definition.

The statement does not assert existence of the ordering, Bruhat bijectivity,
or standard intersection refinements. Those are separate prerequisites of the
host `PadicGeometricLemmaTheorem`. Once they are proved, this statement supplies
the graded comparisons for the explicit filtration. Neither this statement nor
the existence and endpoints of that filtration constitute a proof of the host
theorem.
