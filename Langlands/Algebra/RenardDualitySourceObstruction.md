# Actual source functors in the additive coefficient obstruction

Module and namespace
`Langlands.Algebra.RenardDualitySourceObstruction`. Worker 1222 constructed
this internal comparison for the coefficient audit of Renard I.4.2. It
instantiates the actual original-action functors, identifies their recovered
complex modules, and proves that the first natural isomorphism fails under
the bare additive ring-bimodule hypotheses.

The source motivating this audit is David Renard, *Représentations des
groupes réductifs p-adiques*, French version dated 9 July 2026, registered as
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
Worker 1222 read the bimodule convention on printed p.6 / PDF p.12, scalar
recovery in I.2.1 on printed p.14 / PDF p.20, and the I.4.2 Theorem and
proof on printed pp.23–24 / PDF pp.29–30. The source asserts natural
isomorphisms for the two duality composites; it does not assert this
counterexample. Its opening convention defines a ring bimodule by
commuting original additive actions. The counterexample is derived
mathematics auditing that interpretation, rather than a replacement for
the theorem with a common complex coefficient structure.

## Algebras and original actions

For every unital endomorphism `σ : ℂ →+* ℂ`, `A σ` is `ULift ℂ` with its
ordinary complex algebra structure. `aRingEquiv σ : A σ ≃+* ℂ` forgets the
lift. The parameter distinguishes these selected action instances.
Set `B = ℂ` with ordinary multiplication and coefficients, and give B
additional original A-actions

```text
a · b = σ(aRingEquiv σ a) * b,
b · a = b * σ(aRingEquiv σ a).
```

`leftAction` and `rightAction` supply all additive and associative action
laws. `left_unital` and `right_unital` show that the actual unit fixes
every element. Thus `left_nondegenerate` and `right_nondegenerate` supply
the source nondegeneracy hypotheses with the idempotent `1`.
`left_right_commute`, `left_regular_commute` and `regular_right_commute`
verify respectively commutation of the additional A-actions, the left
A-action with regular right B-multiplication, and regular left
B-multiplication with the right A-action. Ordinary left and right
B-multiplication commute by associativity as usual. Both algebras are
unital fields, hence algebras with idempotents.

The source categories and all carriers here have universe `0`. There is
no topological, continuity, finiteness or endomorphism-surjectivity
assumption. The final obstruction uses a nonsurjective `σ`, whose
unconditional existence is imported from
`ComplexEmbeddingDualityObstruction`.

## Actual tensor and dual values

`regularObject` is the published nondegenerate regular left B-module.
`forgetfulObject σ` is the value of
`NondegenerateTensorFunctor.regularF` at this actual object, using the
original left A-action above. Its carrier `FCarrier σ` is therefore the
published additive balanced quotient `B ⊗_B B`, with its residual
original left A-action.

`tensorContraction` is the published regular tensor contraction
`b ⊗ n ↦ b n`. Its injectivity and the inverse `z ↦ 1 ⊗ z` come from
the actual tensor quotient, without assuming an identification of
carriers. `tensorContraction_action` is proved on pure tensors using
`NonUnitalModuleTensor.hom_ext`; it says that the residual A-action
becomes multiplication through `σ`. Injectivity then gives
`tensor_unital`.

For any nondegenerate module over an idempotented complex algebra,
`NondegenerateScalars.complexModule` recovers the complex coefficients
from the original algebra action. Applying its fixing-idempotent formula
with `1` gives `tensorContraction_smul`:

```text
tensorContraction σ (c • t) = σ(c) * tensorContraction σ t.
```

Here the left-hand scalar multiplication is precisely the one recovered
from A, while the complex numbers on the right have their ordinary
coefficients. Consequently `tensorEquiv σ` is a complex-linear
equivalence between this actual tensor value and
`ComplexEmbeddingDualityObstruction.Carrier σ`, the restriction module.

`unitalDualEquiv` is a general auxiliary comparison for a unital ring R
with the compatible complex algebra multiplication required by the
published dual construction. For an actual nondegenerate module M whose
unit acts identically, the nondegenerate part of its recovered complex
dual is the full algebraic dual: every functional is fixed by `1`.
The equivalence sends a dual subtype element to its functional and
uses that fixing identity for the inverse. Its complex linearity uses
`NonUnitalModuleDual.canonical_smul_val`; it compares the coefficients
recovered from the residual right action with ordinary pointwise
coefficients on the dual.

`dualForgetfulObject σ` is the actual nondegenerate dual
`D_A(F_AB(B))`. Combining `unitalDualEquiv`, `tensor_unital` and the
dual of `tensorEquiv σ` yields

```text
dualTensorEquiv σ :
  D_A(F_AB(B)) ≃ₗ[ℂ] Module.Dual ℂ (Carrier σ).
```

The displayed coefficients on the left are recovered from its original
right A-action. The dual on the right is the full complex algebraic dual
of the restricted source, with ordinary complex codomain and ordinary
pointwise coefficients.

## Actual Hom value and its recovered coefficients

`regularDualObject` is the actual `D_B(B)`.
`regular_scalarMul` checks directly that coefficients recovered from
the regular B-action are ordinary multiplication. Hence
`regularDual_apply` proves that every element of this dual has formula
`φ(z) = z φ(1)`. `regularFunctional t` constructs the element with formula
`z ↦ t z`, using the full-dual comparison just described.

`pseudoDualObject σ` applies the published
`RenardRightHomFunctors.rightPseudoF` to `regularDualObject`.
Thus its carrier `HCarrier σ` is exactly the A-nondegenerate part of
`Hom_(B.op)(B, D_B(B))` with its published residual right A-action.
It is not a separately supplied model of that functor value.

`doubleEvaluation σ h` evaluates `h` at `1`, then evaluates the resulting
functional at `1`. The actual right-B intertwining law and
`regularDual_apply` give `pseudo_apply`:

```text
h(b)(z) = doubleEvaluation σ h * b * z.
```

Conversely, `parameterHom t` constructs `b ↦ (z ↦ t b z)` as an original
right-B intertwiner. `parameter σ t` proves that it belongs to the actual
nondegenerate Hom part: the residual right action of `1` fixes it,
because the supplied left A-action of `1` on B is the identity.
`doubleEvaluation_parameter` and `parameter_doubleEvaluation` prove both
inverse identities by evaluation and extensionality.

The residual action is precomposition with the supplied left A-action
on B. `doubleEvaluation_action` therefore gives

```text
doubleEvaluation σ (op a • h) =
  σ(aRingEquiv σ a) * doubleEvaluation σ h.
```

This proves `pseudo_unital`. Applying the recovered-coefficient formula
with `op 1` gives `doubleEvaluation_smul`, with right-hand side
`σ(c) * doubleEvaluation σ h`. It is the scalar law for the actual
residual right A-module, rather than the inherited ordinary pointwise
coefficients on the ambient Hom space. These identities construct

```text
homEquiv σ : HCarrier σ ≃ₗ[ℂ] Carrier σ.
```

## Obstruction and categorical consequence

For a nonsurjective `σ`, the imported internal algebraic construction
proves that `Carrier σ` is infinite-dimensional and has strictly smaller
complex dimension than its full algebraic dual. In particular,
`no_linearEquiv_dual σ hσ` excludes every complex-linear equivalence
between these two modules.

`no_bijective_intertwiner` excludes every bijective original right-A
intertwiner from `pseudoDualObject σ` to `dualForgetfulObject σ`.
The implemented proof uses
`NondegenerateScalars.complexToLinearMap` to make such an intertwiner
linear for exactly the coefficients recovered from the two right
A-actions. Bijectivity would then give a linear equivalence. Composing
it with `homEquiv σ` and `dualTensorEquiv σ` contradicts
`no_linearEquiv_dual σ hσ`. No proposed evaluation formula is assumed.

`no_objectIso` turns an isomorphism in the actual full subcategory into
such a bijection. The two categorical inverse identities give the
pointwise left and right inverse identities for the underlying
`NonUnitalModuleHom` maps.

`pseudoDualFunctor σ` and `dualForgetfulFunctor σ` are exactly the two
published contravariant composites in the first I.4.2 comparison:

```text
D_B ⋙ rightPseudoF_AB,
(regularF_AB).op ⋙ D_A.
```

Both have domain `(NondegenerateModuleCat ℂ).op` and codomain
`NondegenerateModuleCat (A σ).op` where, in this last expression,
`.op` means the opposite scalar ring, not the opposite category.
In Lean the codomain is
`NondegenerateModuleCat (A σ)ᵐᵒᵖ`.
`no_naturalIso` evaluates any proposed natural isomorphism at
`Opposite.op regularObject` and applies `no_objectIso`.
`exists_counterexample` combines this result with
`exists_nonsurjective_endomorphism`, producing an unconditional witness.

This settles the failure of the first comparison with only the specified
commuting original additive actions. It does not assert that Renard
intended that convention for algebra bimodules. In particular, it does
not contradict the Library's `DualityForgetfulStatement` or
`DualityInductionStatement`, which require compatibility with common
complex coefficients through `IsScalarTower`. The second comparison and
the transposition Lemma (I.4.2.1) are not refuted by this module. Updating
the source ledger and resolving the common-coefficient theorem's proof
obligations remain separate work.
