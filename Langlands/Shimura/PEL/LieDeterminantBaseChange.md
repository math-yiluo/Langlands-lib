# Actual base-changed Lie charts and conditional determinant stability

This internal construction combines the actual chart and local-isomorphism
transport with the existing canonical Lie comparison, actual order pullback,
and reflex determinant. It derives coherence from those Library definitions;
it makes no additional original-literature translation.

For any schemes in one universe, an actual abelian scheme `B`, a morphism
`b : T ⟶ S`, and a finite chart of `B.Lie` on `U`,
`lieBaseChangeChart` pulls back that chart and composes it with the restriction
of `lieBaseChangeIso b B`. That comparison is uniquely characterized by its
cotangent/dual equation and is selected from proved existence. The result is
an actual chart of the Lie module of the actual base-changed abelian scheme
on `b ⁻¹ᵁ U`; no chart or target Lie module is supplied independently.

For an arbitrary ring `O` acting by actual integral endomorphisms of `B`,
`lieSectionDeterminant_baseChange_of_intertwine` assumes explicitly that the
pulled-back Lie action is intertwined with the actual base-changed order
action by this canonical comparison. Restricting that equation gives the
local intertwining needed for constructed-chart determinant transport. Thus
the actual determinant polynomials on every inverse-image smaller open are
coefficient pullbacks along `b.app V.left`. The schemes and finite basis type
use universe `u`, the acting ring universe `v`, and the finite family universe
`w`.

For the Harris datum in universe zero,
`harrisLieDeterminantConditionAt_baseChange_of_intertwine` combines that
identity with actual reflex polynomial pullback along `b ≫ s`.
`harrisLieDeterminantCondition_baseChange_of_intertwine` then proves the full
condition on every finite target chart and every smaller target open.
The proof pulls back the proved source Lie covering. On each constructed
inverse-image chart it transports the source condition on the entire chart.
For an arbitrary target chart and smaller open, its intersections with these
inverse-image covering opens form a covering. Restriction and chart-overlap
invariance establish the condition on those intersections; coefficientwise
structure-sheaf separatedness establishes it on the target open.

The morphism is arbitrary and section rings may contain nilpotents. There is
no flatness, reducedness or characteristic hypothesis in the generic chart
transport. The Harris condition retains its existing reflex-field base.
The action-intertwining equation is an explicit hypothesis, not a result of
this module. Removing it requires the separately assigned actual Lie
naturality theorem. These conditional results do not establish moduli
representability or scheme levels.
