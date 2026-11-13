# Langlands decomposition for a finite obtuse basis

This internal linear-algebra development supports the actual-group statement of
Renard V.3.18. It defines basis orthogonal spaces, open and closed chamber faces,
and nonnegative cones projected along selected basis directions.

Existence applies the complementary polar decomposition from the published
Renard V.5.5 basis corollary. The zero pairings of its positive term determine
the face. If the original vector is orthogonal to selected basis vectors,
obtuseness forces their pairings with both terms to vanish. Removing their
coordinates provides the required projected-cone witness.

Conversely, the negative-coordinate lemma puts every projected-cone vector in
the full nonnegative root cone. The two terms are orthogonal. Positivity of the
quadratic form and the nonnegative mixed pairings prove uniqueness; the zero
pairings recover the face index. Every selected-space decomposition is thus
also the empty-index decomposition. Finally the algebraic obtuse-angle estimate
proves the two quadratic nearest-point inequalities. All assertions concern a
finite basis and a supplied symmetric positive definite form with nonpositive
off-diagonal pairings; no group-theoretic hypotheses are introduced here.
