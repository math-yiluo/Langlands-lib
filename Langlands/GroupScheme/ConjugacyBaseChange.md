# Inner conjugacy and base change

For group schemes over a scheme `S`, the published relation `HomConjugate χ ψ`
means that one point over `S` gives an inner automorphism carrying `χ` to `ψ`.
This module constructs the base change of that conjugating point and proves
that the relation is preserved by composition, base change, and the canonical
cocharacter transport of `CocharacterTransport`.

`baseChangeBasePoint b G g` uses the inverse of the actual pullback
point equivalence `baseChangeBasePointsEquiv b G`. Its input is the section
`g` composed with `b`. The projection formula `baseChangeBasePoint_fst`
identifies the resulting section on the original group. For every test
scheme over the new base, `baseChangePointsEquiv_constantPoint` identifies
the constant family of the new section with the original constant family
on that test scheme considered over the old base.

`HomConjugate.precomp` retains the original conjugator. For
`HomConjugate.postcomp`, the conjugator is its image under the target group
morphism. The proof applies that morphism to the equality on every group of
points, using preservation of multiplication and inverses.
`HomConjugate.baseChange` uses `baseChangeBasePoint` as conjugator and
transfers the pointwise equality through the multiplicative pullback
equivalence. The constant-family formula and naturality in the group
morphism identify both sides. The published all-test-schemes criterion
then supplies equality of actual scheme morphisms.

Finally, `HomConjugate.transportCocharacter` applies these results to the
three maps defining canonical cocharacter transport: the multiplicative
group comparison, the pulled-back cocharacter, and the descent comparison.
No detection of scheme morphisms using only field-valued points is used.

These are internal constructions and deductions from the published
`HomConjugacy`, `InnerAutomorphism`, `CocharacterTransport`, and multiplicative
pullback point API. They require no smoothness, affineness, or field
hypothesis. The module supplies transport compatibility; it does not yet
construct a stabilizer subgroup or identify a reflex field.
