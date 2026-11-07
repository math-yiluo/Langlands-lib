# Conditional reduction of the inertia-block center evaluation

Authors: Worker 1153; Worker 1842 (the reused restriction-summand adapter).

Module `Langlands.Representation.CuspidalSupport.RationalInertiaBlockCenterEvaluationReduction`,
namespace `Langlands.CuspidalSupport`.

Source context: David Renard, *Représentations des groupes réductifs p-adiques*,
French version dated 9 July 2026, registered source
`renard-2026-representations-groupes-reductifs-padiques`, VI.4.5 Proposition and proof
(printed p.160 / PDF p.166), using VI.3.2(i) (printed pp.143–144 / PDF pp.149–150),
VI.4.1 (printed pp.149–151 / PDF pp.155–157), VI.4.4 Proposition (printed p.159 /
PDF p.165), and A.X (printed p.269 / PDF p.275).

This is an internal conditional reduction between published Lean propositions.
`rationalInertiaBlockCenterEvaluation_of_inputs` has the three explicit premises
`RationalNormKernelOrbitStatement`, `RationalSummandHomEquivalenceStatement`, and
`RationalSummandCenterGroupAlgebraStatement`, and concludes the exact unchanged
`RationalInertiaBlockCenterEvaluationStatement`.

The exported definition `rationalInertiaBlockCenterEvaluationEquivOfInputs`
takes these three premises and the entire original field, group, torus,
cocharacter and cuspidal-representation data. It returns an actual ring
equivalence from the displayed group algebra to the actual categorical center.
It chooses the equivalence from the existence theorem by `Classical.choose`;
no canonical choice or uniqueness is asserted.
`rationalInertiaBlockCenterEvaluationEquivOfInputs_spec` uses
`Classical.choose_spec` to prove that this chosen equivalence has both the scalar
coefficient action on every block object and the `ω(t)` action on every indicated
unramified twist. The definition returns mathematical data, while the conditional
existence theorem remains a separate theorem with its original type and proof.

The first clause of the orbit premise supplies an irreducible subrepresentation
`W` of the restriction of the original `π` to the actual common norm kernel.
Worker 1842's `restrictionSummand` and `restrictionSummandι` turn this into a smooth
irreducible representation `ρ`, in the carrier universe of `π`, and an injective
equivariant inclusion `j`. Applying the Hom-equivalence premise gives block
membership of the actual compact induction `I` of `ρ` and an equivalence of its
actual module-valued Hom functor. In particular that functor is full and faithful.

The group-algebra premise gives a complex algebra isomorphism `a` onto the center
of `End I`. The proof composes `a` with inverse categorical-center evaluation via
`rationalInertiaBlockCenterFromEnd`. The resulting ring isomorphism has the exact
group algebra and actual inertia block in the conclusion. Its scalar clause is
`rationalInertiaBlockCenterFromEnd_scalar`: a complex algebra isomorphism preserves
coefficients, and faithfulness of the Hom functor detects the scalar action on
every block object.

For an element `t` of the subgroup `T` in the statement, the action clause of the
group-algebra premise says that its image under `a`, precomposed with every map
`I → π ⊗ ω`, equals `ω(t)` times that map. Naturality of the transported categorical
center identifies this with postcomposition by its component on `π ⊗ ω`.
`rationalInertiaBlockCenterFromEnd_scalar_action` then uses the faithful Hom
functor to identify that component with `ω(t)` times the identity. The support
clause of the group-algebra premise is not needed in this categorical step.

All original local-field and carrier universes and all premises of the target
remain unchanged: the actual connected reductive group, maximal split torus,
generic cocharacter, standard-cocharacter, relative-root-system and unipotent
closedness premises, the three topological premises, and irreducible cuspidal `π`.
The block is formed from `rationalInertiaBaseLift G π`, while the summand is taken
from the restriction of the original `π`. No additional condition on those
objects is imposed.

This reduction does not prove any of its three global input propositions. It
therefore does not discharge the unconditional VI.4.5 evaluation target or complete
the host task.
