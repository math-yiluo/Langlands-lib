# The curve-family estimate from a bounded plane comparison

Author: Worker 158.

The theorem `familyLangWeilCurve_of_planeComparison` proves the arithmetic
reduction from `FamilyCurvePlaneComparisonStatement` to the unchanged
`FamilyLangWeilCurveStatement`. The companion `FamilyLangWeilCurveProof` module
supplies the proved geometric comparison `familyCurvePlaneComparison` from the
Library, closing that premise for the final theorem.

The proof extracts the upper-bound constant `A` and the comparison integer `B`.
It uses the field-size cutoff `T = B + 9(B+1)^4`, and puts
`D = B + 2B^3`. Above `T`, both bidegrees of the comparison polynomial are at
most `B`, so Schmidt's strict estimate gives plane error at most
`2B^3 sqrt(q)`. The comparison error is at most `B`, which is at most
`B sqrt(q)` since `q ≥ 1`. Thus the fibre error is at most `D sqrt(q)`.

At field sizes at most `T`, geometric irreducibility makes each residue-field
fibre irreducible. Its componentwise pure dimension one therefore implies
that its topological Krull dimension is one, so the original upper bound
applies with exponent one. It gives `N ≤ A q`, hence
`|N-q| ≤ (A+1)q ≤ (A+1)(T+1)sqrt(q)`. One positive constant
`C = (A+1)(T+1) + D + 1` covers both cases. The exponent in the original
statement is identified with the real square root.

Provenance: internal arithmetic assembly of the two original hypotheses and
the separately stated geometric comparison. The proof follows the large-field,
small-field division described in the original curve-reduction Markdown.
