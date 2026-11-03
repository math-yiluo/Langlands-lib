# Twisted intersections on the actual point Weyl quotient

This internal transport unit starts from the published `pointCoxeterSystem`,
which sends a scheme relative Weyl Coxeter system through the
representative-preserving quotient equivalence `weylEquiv`. The labels remain
exactly `SimpleRoot i ν`. The normalizer and full-centralizer comparison
hypotheses are explicit; this unit does not prove those comparisons.

`pointCoxeterSystem_mem_standardSubgroup` identifies membership in standard
Coxeter subgroups under that equivalence. `pointCoxeterSystem_isMinimal_iff`
preserves and reflects minimum length in the whole double coset by transporting
both standard-subgroup multipliers and using the published length identity.
`pointMinimalRepEquiv` restricts the actual quotient equivalence to an
equivalence of the two subtypes of minimum double-coset representatives,
using that minimum-length equivalence in both directions. Its underlying
maps are `weylEquiv` and its inverse; the finite simple-root labels are
unchanged.
`pointCoxeterSystem_intersectionSubset` then identifies the actual finite
source intersection labels, by their defining reflection-conjugacy membership
test. These statements require no nonempty root system or finite Weyl group.

`point_geometricSourceIntersections` accepts the two published all-test
structural properties `IsStandardLeviTwistedIntersection` and
`IsStandardSourceTwistedIntersection`. It concludes the three exact point
subgroup equalities needed by `geometricSourceDecompositionOfEq`: the ambient
source Levi equals the standard Levi at the actual point Coxeter intersection
subset, and the source parabolic and radical restricted to `L_J` equal the
literal standard restrictions there. It applies at every minimum point Weyl
representative and every actual point normalizer lift, without choosing a
section of the quotient. The proof transports the lift back through
`normalizerEquiv`, reflects minimum length, applies the published evaluation
lemmas, and rewrites the intersection labels. The ambient point is unchanged
by this lift transport. Inverse conjugation is exactly that in
`geometricSourceIntersection` and the all-test evaluation lemmas.

All statements hold over an arbitrary field and for the displayed group scheme,
torus morphism and cocharacter, at universe `u`. No topology, local compactness,
finite-length or classification assertion enters these group identities. The
provenance is internal: the proof uses the named published quotient, subgroup,
length and rational-point evaluation lemmas. It does not prove either
structural intersection property or the final rational-point Aubert induction
compatibility, and adds no premise to that final target.
