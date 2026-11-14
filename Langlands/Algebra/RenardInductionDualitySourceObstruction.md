# Actual induction and duality under a proper complex self-embedding

Module and namespace
`Langlands.Algebra.RenardInductionDualitySourceObstruction`. Worker 1222
constructed this internal coefficient audit of the second comparison in
Renard I.4.2. It instantiates the published original-action functors and
excludes an isomorphism at the actual regular source object when the
complex self-embedding is not surjective. It then excludes a natural
isomorphism of those functors and supplies an unconditional witness.

The governing source is David Renard, *Représentations des groupes réductifs
p-adiques*, French version dated 9 July 2026, registered as
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
Worker 1222 read the additive bimodule convention on printed p.6 / PDF
p.12, coefficient recovery in I.2.1 on printed p.14 / PDF p.20, and the
I.4.2 Theorem and proof on printed pp.23–24 / PDF pp.29–30. The source
asserts a natural isomorphism
`I_AB(D_A(M)) ≅ D_B(P_AB(M))`. This counterexample is derived mathematics
auditing its bare additive ring-bimodule interpretation; it is not a
counterexample asserted by the source. It does not decide the author's
intended algebra-bimodule convention.

## Algebras, actions and actual induction

The imported construction `RenardDualitySourceObstruction` supplies
`A σ = ULift ℂ`, its ordinary complex algebra structure, and
`aRingEquiv σ : A σ ≃+* ℂ`. Write `α` for this equivalence. The target
algebra is `B = ℂ` with ordinary coefficients. For every unital
endomorphism `σ : ℂ →+* ℂ`, the additional original actions are

```text
a · b = σ(α(a)) b,       b · a = b σ(α(a)).
```

The imported laws prove these actions unital, nondegenerate and commuting
with each other and with the appropriate regular B-actions.
`regular_right_commute σ` and `right_nondegenerate σ` are the exact inputs
to the actual published induction functor. Both algebras are unital
fields and hence have idempotents. All carriers and categories here
have universe `0`.

`sourceRegularObject σ` is the actual nondegenerate regular left A-module
A. `inducedObject σ` is its image under
`NondegenerateTensorFunctor.regularP`, so its carrier `PCarrier σ` is
the published additive balanced quotient `B ⊗_A A` with the residual
regular left B-action.

`inductionPairing σ` is the biadditive map
`(b,a) ↦ b σ(α(a))`. Its balancing law follows from multiplication
preservation by α and σ. The actual quotient lift
`inducedContraction σ` therefore sends `b ⊗ a` to `b σ(α(a))`.
`inducedInsertion σ` sends `b` to `b ⊗ 1`. Multiplication preservation
and the balancing relation prove both inverse identities:
`contraction_insertion` and `insertion_contraction`. The latter is
proved on pure tensors with `NonUnitalModuleTensor.hom_ext`.

The same extensionality argument proves `inducedContraction_action`:
the original B-action becomes ordinary multiplication. Injectivity of
the contraction gives `induced_unital`. The fixing-idempotent formula
for `NondegenerateScalars.scalarMul`, using the actual idempotent `1`,
then gives `inducedContraction_smul`. Consequently `inducedEquiv σ`
identifies the coefficients recovered from this actual B-action with
ordinary ℂ by a complex-linear equivalence.

## Source dual and actual right-induction value

`sourceRegular_unital` and `sourceRegular_scalarMul` compute the unit
and recovered coefficients of the regular source module. In α
coordinates these coefficients are ordinary complex multiplication.
`sourceDualObject σ` is the actual
`NonUnitalModuleDual.dualObject` of this source.

`sourceDual_apply` proves that every such functional has the formula
`f(a) = α(a) f(1)`, using its recovered coefficient linearity.
`sourceFunctional σ t` constructs the functional `a ↦ t α(a)`.
Its membership in the actual nondegenerate dual is supplied by the
imported `unitalDualEquiv`: the unit fixes every functional, so the
nondegenerate dual is the full recovered complex dual.

`coinducedObject σ` applies the published
`RenardRightHomFunctors.rightI` to `sourceDualObject σ`.
Its carrier `HCarrier σ` is thus exactly the B-nondegenerate part of
`Hom_(A.op)(B,D_A(A))`, with the published residual original right
B-action. No substitute Hom functor is assumed.

For `h` in that actual carrier, `coinducedEvaluation σ h b = h(b)(1)`.
The original right-A intertwining law, followed by `sourceDual_apply`,
proves

```text
coinducedEvaluation σ h (σ(c) b) = c * coinducedEvaluation σ h b.
```

Let `V = ComplexEmbeddingDualityObstruction.Carrier σ`, and let
`ρ = carrierRingEquiv σ : V ≃+* ℂ`. The scalar law on V is
`ρ(c • z) = σ(c) ρ(z)`. The preceding identity constructs
`coinducedForm σ h : Module.Dual ℂ V` by `z ↦ h(ρ(z))(1)`.

Conversely, `coinducedParameterHom σ φ` sends
`b` to `sourceFunctional σ (φ(ρ.symm b))`. The scalar law on V and
the linearity of φ prove that this is an original right-A intertwiner.
`coinducedParameter σ φ` proves membership in the actual Hom part:
the residual right action of B's unit fixes it by precomposition with
`b ↦ 1*b`. `coinducedForm_parameter` and `coinducedParameter_form`
prove both inverse identities by evaluation and extensionality.
Thus `coinducedAddEquiv σ` is an additive equivalence
`HCarrier σ ≃+ Module.Dual ℂ V`.

This equivalence is asserted only to be additive. Its relevant residual
action law is `coinducedForm_action_sigma`:

```text
coinducedForm σ (op (σ(c)) • h) = c • coinducedForm σ h.
```

Indeed, the original right B-action precomposes the Hom map by left
B-multiplication, and the evaluation identity above applies. This
restricted action calculation is what the final obstruction uses.
The construction does not identify the B-recovered coefficients on
the entire Hom part with ordinary pointwise coefficients on this dual.

## Actual dual-induced value and obstruction

`dualInducedObject σ` is the actual `D_B(P_AB(A))`.
`dualInducedEquiv σ` is the complex-linear equivalence with ordinary ℂ
obtained by composing `unitalDualEquiv`, the dual of
`(inducedEquiv σ).symm`, and `LinearMap.ringLmapEquivSelf ℂ ℂ ℂ`.
The coefficients on its source are recovered from the original right
B-action. Its coordinate is evaluation at `inducedInsertion σ 1`.

`dualInducedEquiv_action` proves that this coordinate sends
`op b • ψ` to `b * dualInducedEquiv σ ψ`. The implemented proof compares
the original B-action with recovered coefficient multiplication on
`PCarrier σ` by the injective contraction, then applies the linearity
of the actual functional ψ. `dualInducedEquiv_symm_mul` gives the
inverse form of the same action law.

For any original right-B intertwiner
`f : DPCarrier σ → HCarrier σ`, `restrictionLinearMap σ f` is the map

```text
z ↦ coinducedForm σ
      (f ((dualInducedEquiv σ).symm (ρ z))).
```

It is complex-linear from V to `Module.Dual ℂ V`. Additivity follows
by composing the actual additive maps. For scalar multiplication,
`ρ(c • z) = σ(c)ρ(z)` becomes the original right action of
`op (σ(c))` through `dualInducedEquiv_symm_mul`; f intertwines that
action, and `coinducedForm_action_sigma` turns it into pointwise
multiplication by c. No coefficient equality for the two bimodule
actions is assumed.

If f were bijective, the additive equivalences on either side would
make `restrictionLinearMap σ f` bijective. The imported theorem
`ComplexEmbeddingDualityObstruction.no_linearEquiv_dual σ hσ`
excludes the resulting complex-linear equivalence when σ is not
surjective: V is infinite-dimensional and its full algebraic dual has
strictly larger dimension. This proves `no_bijective_intertwiner`.

`no_objectIso` uses the inverse of an alleged isomorphism
`coinducedObject σ ≅ dualInducedObject σ` as f. The categorical inverse
identities give pointwise inverse identities for the underlying actual
`NonUnitalModuleHom` maps, contradicting that theorem.

`coinducedDualFunctor σ` and `dualInducedFunctor σ` are precisely the
two contravariant composites in the second I.4.2 comparison, formed
from the published original-action functors. `no_naturalIso` evaluates
an alleged natural isomorphism at `Opposite.op (sourceRegularObject σ)`
and applies `no_objectIso`. Finally, `exists_counterexample` uses the
published unconditional proper-endomorphism construction to supply
σ and its nonsurjectivity proof.

## Scope

This construction settles the second comparison under the bare
additive interpretation: even an abstract natural isomorphism fails
in this example. It uses actual functor values rather than just a
failure of a proposed evaluation formula.

The compatible-input statement `DualityInductionStatement`, with
`IsScalarTower ℂ Aᵐᵒᵖ B`, and its published proof
`Langlands.Algebra.dualityInduction` remain separate. The present
example has the bare commuting actions; it supplies no such common
coefficient hypothesis. The published first-comparison obstruction
and the separate transposition Lemma (I.4.2.1) are unchanged. This
internal construction and its intrinsic laws do not claim exact proof
acceptance of a new Library statement or completion of Chapter I.
