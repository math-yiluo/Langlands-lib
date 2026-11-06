# Normalized support grades for arbitrary represented parabolics

The namespace is
`Langlands.Aubert.General.RepresentedParabolic`. This is a derived intermediate
statement toward the published `RepresentedGeometricLemmaStatement`, together
with a proof that the geometric existence statement and this intermediate
statement imply the full target. Neither premise is proved here.

The source is David Renard, *Représentations des groupes réductifs p-adiques*,
2026 version, VI.5.1, printed pp.161–172 / PDF pp.167–178. The support
filtration and passage through exact radical coinvariants appear on printed
pp.163–164 / PDF pp.169–170. The local coinvariant–induction comparison is
VI.5.1.3 on printed p.167 / PDF p.173, including the Hecke tensor argument.
The remaining modulus cancellation is on printed pp.171–172 / PDF
pp.177–178. Formula VI.5.1.12 on the latter page identifies the natural
map from the successive support quotient to the normalized intersection
piece.

`RepresentedGeometricLemmaSupportGradedStatement` retains the field,
connected reductive group, canonical rational-point topology and represented
parabolic hypotheses of the full target. It quantifies over an ordered
double-coset cover `s` of the literal point images and a family `D` of
the unchanged `GeometricLemmaIntersectionDatum`. At index `i`, the datum
is attached to `(s.representative i)⁻¹`: the existing ordered-orbit convention
uses the orbit of `P(s.representative i)⁻¹` in `P\G`.

The conclusion identifies every successive quotient of the particular
`leviJacquetSupportFiltration` with `(D i).pieceFunctor`. These are natural
isomorphisms on the full smooth source category, as required by
`HasGradedPieces`. In particular, this asserts the normalized comparison
for the actual support-image spaces, with the published intersection,
conjugation and normalizing characters. The two universe parameters `u`
and `v` are independent. No admissibility, finite-length or irreducibility
assumption is imposed.

The ordered cover and intersection data are hypotheses of this intermediate
comparison statement. They are existential conclusions of the full geometric
lemma, whose published statement and imported closure are unchanged.

`representedGeometricLemma_of_geometry_and_supportGraded` implements the
assembly. It takes the geometric statement's finite enumeration and good
representatives with their data. The canonical rational-point topology is
Hausdorff by `rationalPoint_t2Space` and second countable by
`reductiveRationalPoint_secondCountable`. Together with the already supplied
local compactness, second countability gives sigma compactness. Thus the
published finite-orbit ordering theorem applies to the two closed parabolic
point images without further topological assumptions.

The initial orbit ordering may use different representatives. The proof
uses `OrderedDoubleCosets.classifiedRepresentatives` to replace them by
inverses of the good representatives, in the order selected by the orbit
theorem. This also gives the equivalence between the two finite index
sets. The intersection data are reindexed and transported along the actual
representative equalities, preserving all their dependent fields.

The new ordered cover supplies the finite double-coset equivalence required
by the full target. The assumed support-grade comparison identifies the
grades of the constructed support-image filtration with the reindexed
intersection pieces. The identity permutation then witnesses
`IsGluedFrom`. This proves exactly the displayed conditional implication
at independent universes. The unconditional geometric existence and
normalized support-grade comparison remain proof obligations.
