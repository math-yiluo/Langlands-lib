# Original framed comparison for identity Nilp-base extension

`baseChangeIdentityComparison X` is an actual comparison, in the original
framed comparison relation, from `X.baseChange (𝟙 A)` to `X`. Its target
comparison is exactly the existing `X.target.val.baseIdComparison`, including
its original refinements and actual formal isomorphism. Its residue equality
is the forced identity-base residue equation. Its framing field proves the
original all-test `FramingSquare`; no framing-compatibility premise is added.

The specified source map has complete identity formal series. Its construction
is the inverse actual quotient-frame comparison followed by the forced
identity-coefficient comparison on the original source. Composition and the
actual integral inverse law give the full forward series certificate. The
generic identity-coefficient and inverse-chart lemmas retain arbitrary finite
coordinate types and require no domain hypothesis.

The implemented proof first constructs a generic bridge from a proved equation
of whole actual framing tensors to the normalized original chart equation.
The complete identity series of the source map identify its normalization with
the global-frame map forced by the residue equality, using extensionality of
integral formal maps. Mapping the whole tensor equation to a test chart and
composing with the actual global-frame normalization gives the chart equation.
This does not infer global tensor equality from local restrictions.

`ReducedFramingSquare.of_induced_global_square` then retains any specified
reduced-target comparison proved to be induced by the supplied actual target
isomorphism. The actual test-comparison refinement square and the normalized
framing refinement equations paste the chart square to the original finer
charts, with their own selected parent charts. Quotient reduction of the
specified identity-base comparison has exactly this inducing certificate.
The previously proved whole tensor identity supplies the remaining equation.

The resulting actual framed comparison gives
`comparisonClassOf_baseChange_id`. Quotient induction proves
`ComparisonClass.baseChange_id` for the same original framed chain quotient.
This is the identity law; the composition law and the complete Nilp functor
remain subsequent obligations.

All constructions retain the local-field and finite-dimensional central
division-algebra hypotheses, the embedded field, the coefficient and residue
fields, the fixed height-certified frame, and explicit Nilp universes {v,u}.
Covers may be infinite. This is internal coherence derived from the actual
base-extension construction, with no new representability theorem, representing
object, or universal object assumed.
