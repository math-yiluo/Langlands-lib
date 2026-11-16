# Radical generation for descended maximal-unramified models

`unramifiedRadicalRootGeneration` proves exactly the existing
`UnramifiedRadicalRootGenerationStatement.{u}` at arbitrary universe `u`.
It has no additional premises. A single subgroup `H` in the image of the
generic centralizer is chosen before every nonempty subset of one
apartment facet, conjugating element, characterized descended model and
reductive quotient. The conclusion identifies `Q.positivePoints` with the
preimage under `rationalExtend` of the conjugate of the subgroup generated
by `H` and the positive root fixers.

The implemented proof first establishes the supporting implication
`unramifiedRadicalRootGeneration_of_upstairs`. It applies the upstairs
assertion to the actual base change of the generic group and retains its
single subgroup `H` and centralizer bound. The final theorem discharges
that implication's input with the published theorem
`unramifiedUpstairsRadicalRootGeneration`, so no generation assertion
remains a hypothesis of the final result.

For each descended model and reductive quotient,
`SpecialFibreQuotientData.exists_unramifiedRadical` supplies an actual
radical inclusion `i` in the base-changed special fibre and identifies
`Q.unramifiedKernelPoints` with its reduction preimage mapped to the
generic group. The private smoothness lemma applies smooth base change
to the supplied smoothness of `D.neutral`; the integral algebra and
scalar tower come from the extension of valuations.

The private lemma `radicalPreimage_eq_conjugate` handles conjugation over
an arbitrary upstairs group. It transports the base-changed model by
`Int(g⁻¹)`. The published same-zero-datum conjugation theorem gives the
integral-point characterization in the original apartment, preserving
`E` through normality of `E.zeroPoints`. This generic transport leaves
the integral group scheme, smoothness, special fibre, reduction and
radical inclusion unchanged. The upstairs formula therefore applies to
the transported model and the same radical inclusion. The special-fibre
subgroup transport equality recovers the original subgroup by conjugating
by `g`. Splitting this step from the descended assembly keeps the proof
terms manageable.

Finally, `positivePoints_eq_comap_unramifiedKernelPoints` identifies the
downstairs subgroup with the preimage of the actual upstairs kernel
subgroup. Substitution of the radical identification and the conjugation
equality gives precisely the asserted preimage under `rationalExtend`.
The apartment and building versions of the positive root fixers agree by
definition. The proof preserves the given subset, model, quotient and
zero datum throughout and requires no boundedness of the facet.

The provenance of this file is internal: it composes the published
upstairs generation theorem with the published radical identification,
generic transport and unramified kernel-descent results on their actual
maps. The unchanged target Markdown records the derived
Kaletha–Prasad Corollary 8.4.12 and §9.5 assertion and its source
conventions. This proof follows the implemented composition described
above; it makes no further identification of `H` with a named torus
filtration.
