# Supported rational intersection terms reduce to the common term

This internal adapter proves that the actual restricted intersection term,
followed at its source by ambient normalized Jacquet restriction, equals
`rationalCommonJacquetTerm`. Its indices are a coarse source label `I`, a
coarse target label `J`, and a minimum representative `w` for `J,I`.
The source fine subtype is `simpleImage cs w⁻¹ J ∩ I` inside `I`;
the target fine subtype is `simpleImage cs w I ∩ J` inside `J`.
The right side depends only on `w` and the target fine label.

`rationalIntersectionJacquetTerm` constructs the standard restricted term
at these two subtype intersections. Its actual fine-Levi conjugation
witness is derived from minimum-representative support, with no
additional membership assumption.

`intersectionSourceIndex_eq_common` identifies the ambient source fine
label with `simpleImage cs w⁻¹ (simpleImage cs w I ∩ J)`. The subtype
image is the source intersection itself, and `simpleImage_inv_inter`
applied at `w⁻¹` gives the second equality. This finite identity does not
require minimum-representative hypotheses.

`intersectionJacquetConjugationMembership` rewrites that source identity
in `commonJacquetConjugationMembership`, with the support witness
`⟨I, hw, rfl⟩`. Thus it derives the actual fine-Levi membership equivalence
for every specified normalizer lift of `w`. It uses the point-Coxeter
root-length and positive-simple-reflection comparisons and the standard
Levi-conjugation statement.

`standardConjugatedJacquetTerm_congr_source` transports the full actual
conjugated term across equality of source finite labels. Substitution
and proof irrelevance prove the result without changing the target label,
the lift, or any normalized functor.

`rationalRestrictedJacquetTerm_comp_ambient_eq_common` first uses
`rationalRestrictedJacquetTerm_comp_ambient` to apply actual Jacquet
restriction in stages. It then reindexes the source with the finite
identity and evaluates the supported common term. The fine-Levi
membership witness in its left side is arbitrary. Haar factorization is
derived by the imported stages theorem from continuity of the standard
projections, rather than supplied as a representation comparison.
`rationalIntersectionJacquetTerm_comp_ambient_eq_common` specializes this
result to the canonical constructed term.

The field and representation universes remain independent, with carriers
in `max (u + 1) v`. The topology is the actual point topology. Ambient
local compactness and nonarchimedeanness, closed radicals and Levis,
actual ambient and literal restricted finite-length and short-exact
preservation, continuity of standard projections, and compact-limit
decomposition of restricted radicals remain explicit. No scheme Coxeter
realization is added to the weaker point-Coxeter scope.

Provenance is internal through the finite-label inverse-intersection
identity, the actual fine-Levi conjugation construction, and normalized
Jacquet restriction in stages. This proves a comparison for the standard
restricted term. Actual geometric-intersection subgroup identities,
geometric expansion, the longest-survivor comparison, and the whole
rational Aubert compatibility statement remain separate obligations.
