# Intrinsic generation of projective evaluation sections

This is derived infrastructure for the projective evaluation construction.
It uses the actual local frames and evaluated sections in
`ProjectiveBundle.EvaluationCoordinates` and `EvaluationMorphism`, the canonical
open-pullback section comparison in `EvaluationRestriction`, and the
frame-generation condition in `EvaluationGluing`. The nonvanishing comparisons
come from `Picard.AmpleIsoProof`, `Modules.PullbackSectionOpenProof`, and
`Modules.SectionResidueComparison`. No external literature assertion is added.

Fix schemes `X` and `S` in the same arbitrary universe, a morphism
`p : X ⟶ S`, a module sheaf `M` on `S`, a line bundle `L` on `X`, and an
actual module-sheaf morphism `ev : M ⟶ p_* L`.

`localSectionEvaluation p L ev U σ` first applies `ev` to an actual section
`σ` of `M` over a base open `U`, then applies `openSection` to regard the result
as a global section of the actual pullback of `L` to `p⁻¹U`.
`localSectionEvaluation_restrict` proves that evaluation on a restriction of
`σ` is the converted restriction of its evaluation, using naturality of `ev`.

`EvaluationGenerates p L ev` says that every point `x` of `X` has a base
open neighborhood `U` of `p(x)` and a section `σ` of `M` over `U` whose
evaluation has nonzero residue-field value at `x`, viewed in `p⁻¹U`.
This condition does not choose a frame and does not assume local freeness.
It is a condition on actual evaluated local sections; no equivalence with
surjectivity of an adjoint sheaf morphism is asserted here.

The proof of the frame criterion uses two preliminary facts:

- `LocalFrame.sum_coordinates_basisSection` writes every local section on
  an open contained in the domain of a frame as the sum of its coordinates
  times that frame's actual basis sections. It follows from the inverse
  identity for the frame's coordinate equivalence.
- `openSection_nonvan_restrict_iff` proves that converted restriction to
  an open subscheme preserves and detects nonvanishing at its points.
  The canonical `openPullbackIso` identifies the converted restriction
  with the pullback of the original converted section. A module-sheaf
  isomorphism preserves the trivialization open, and the trivialization
  open of a pulled-back line-bundle section is the inverse image of the
  original one. The residue-open comparison gives the stated criterion.

`localSectionEvaluation_eq_sum` evaluates the frame expansion. Its coefficient
at a basis section is transported by the actual ring map `p.app W` and then
by the canonical `topIso.inv` for the inverse-image open. Thus the expansion
uses precisely the scalars of the line bundle on that open.

`localEvaluationSections_generate_of_section` deduces a nonvanishing evaluated
basis member at any point where an evaluated local section is nonvanishing.
If every evaluated basis member had zero residue value, additivity and scalar
compatibility of section pullback to the residue field would make the entire
evaluated expansion zero, a contradiction.

`EvaluationGenerates.localFrame` proves pointwise generation by the evaluated
basis of every actual local frame, on every smaller base open in its domain.
For a point over such an open `W`, choose an intrinsic witness over `V` and
restrict it to `W ∩ V`. Naturality and the nonvanishing restriction criterion
preserve the witness. The finite expansion then gives a nonvanishing evaluated
basis member over the intersection. Restriction compatibility of the actual
evaluated basis sections and the same nonvanishing criterion transport it
back to `W`.

`EvaluationGenerates.frameEvaluationGenerates` specializes this result to all
chosen frame opens, giving exactly the hypothesis used by `evaluationMap`.
Conversely, `FrameEvaluationGenerates.evaluationGenerates` assumes
`IsLocallyFreeOfRank M (n + 1)`, chooses a frame open through `p(x)`, and takes
the nonvanishing evaluated basis member as its intrinsic witness.
`evaluationGenerates_iff_frameEvaluationGenerates` combines these directions.
Local freeness is needed only for the converse and the displayed equivalence.

This unit supplies an intrinsic sufficient condition for the existing actual
global projective evaluation map. It does not prove that condition for an
abelian-scheme cubic line bundle, any immersion result, or the host
large-level representability statement.
