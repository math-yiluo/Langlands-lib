# Original Weil evaluation and generic fibers

This derived algebraic construction supplies the counit compatibility needed
when passing from integral Weil models to the original field schemes in
Brian Conrad, *Weil and Grothendieck approaches to adelic points* (2011),
Example 4.2, printed pages 9–10. The source chooses an upper integral model,
forms its lower Weil restriction, and compares its points with points of the
original upper scheme. The present unit proves compatibility of the existing
actual generic-fiber isomorphism with the original evaluation maps. It does
not introduce a topology or assert a full adelic comparison.

All rings, fields and schemes inhabit an arbitrary common universe. Points
are actual morphisms in the appropriate category over a spectrum.

For the general specified-tensor calculation, let A, B, C and D be commutative
rings, with A-algebra structures on B and C and C- and B-algebra structures on
D. Specify a C-algebra isomorphism e from C tensor_A B to D satisfying
e(1 tensor b) = algebraMap B D b for every b. Let R be a C-algebra with a
compatible A-action, and E a D-algebra with a compatible B-action. A specified
ring map f from R to E is required to be compatible both with C to D and
with A to B. Let B be finite projective over A and Y a locally finite-type
B-scheme. No affineness or separatedness of Y is required here.

The two `weilRestrictionTensorBaseChangeTestIso_inv_...` lemmas identify the
projections of the inverse tensor test isomorphism. They follow by cancelling
its forward isomorphism and simplifying the known pullback projections.
`specifiedTensorWeilTest_fst` and `specifiedTensorWeilTest_snd` then show that
the composite of the coefficient, tensor and scalar test identifications
preserves the lower test projection and the original upper-base projection.
The second identity uses the specified B-coefficient formula for e.

`specifiedTensorWeilTest_eq_evaluation` precomposes that composite with the
C-to-D evaluation test and postcomposes with the pullback of restriction of
scalars on Spec R. It proves that the resulting morphism is the original
A-to-B evaluation test along f. The proof compares the two pullback
projections: the first is Spec f, and the second is the original structure
map to Spec B, using the B-to-D-to-E scalar tower.

`affineChartWeilRestrictionSpecifiedTensorComparison_fst` identifies the
projection of the specified-tensor counit comparison to the original Y with
the integral counit after the three test identifications. It follows by
unfolding the existing comparison constructions and their pullback maps.
`affineChartWeilRestrictionSpecifiedTensorComparison_evaluation` consequently
identifies evaluation of that comparison on the base change of an actual
integral Weil point with the base change of its original integral evaluation.
Its proof first cancels the pullback adjunction on the lower point, then
compares both projections to the upper generic fiber. The first projection
uses the preceding test identity and naturality of the original counit;
the second follows because both morphisms are over Spec D.

For the original-field specialization, A is a domain with fraction field K,
L is a finite extension of K, and B is an integral-closure A-algebra in L,
finite projective over A. The A-actions on L through K and through B agree.
R is a K-algebra with compatible A-action, E is an L-algebra with compatible
B-action, and f from R to E is compatible with K to L.
`weilRestrictionEvaluation_integralCompatibility` derives its A-to-B
compatibility by evaluating the given equality of K-to-E maps at the image
of each a in A and rewriting the scalar-tower formulas. That auxiliary
identity needs only the displayed compatible algebra towers, not the
fraction-field, integral-closure or module-finiteness hypotheses.

Let j be an immersion of the original L-scheme X into finite-dimensional
projective space, and M actual `ProjectiveImmersionRingModelData` over B
with original fiber X and immersion j. Such data record the geometric model
and its Cartesian generic-fiber comparison; they do not assume a counit
identity. The required local finite-type instances are derived from the
model and from j.

`projectiveModelWeilGenericFiberEvaluation` starts with an R-point of the
integral Weil model, base changes it from A to K, composes with the existing
`projectiveModelWeilGenericFiberIso`, and evaluates the original K-to-L Weil
counit using f. Its output is an E-point of the originally specified X,
viewed over L via j followed by the projective structure map.

`projectiveModelWeilGenericFiberEvaluation_eq_integral` proves that this
point equals the integral A-to-B evaluation, base changed from B to L and
followed by M's original-model generic-fiber isomorphism. The proof unfolds
evaluation, applies the existing all-test generic-fiber counit comparison,
and uses the general evaluation identity above with the proved isomorphism
K tensor_A B to L. There is no separability assumption on L over K.

This is an intrinsic compatibility of the constructed evaluation map. The
number-field and function-field arithmetic specializations, its use to
identify the full adelic homeomorphisms with evaluation along the literal
adele inclusions, and the remaining whole-paper results remain obligations
of the host task.
