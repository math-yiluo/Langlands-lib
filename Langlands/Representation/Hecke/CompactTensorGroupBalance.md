# Group balancing in the original Hecke tensor

`HeckeAlgebra.leftTranslated μ g` is left translation on the original
Hecke-algebra carrier, transported through `HeckeAlgebra.toTestFunction`.
It is a complex-linear equivalence and satisfies

```text
leftTranslated μ g a (x) = a(g⁻¹ x).
```

Keeping this map on the Hecke-algebra type synonym allows its existing module
instances to be used without identifying them with scalar test-function
instances. `leftTranslated_apply` is the displayed evaluation identity.

The supporting result `Homomorphism.tensor_group_balanced` concerns
locally compact Hausdorff nonarchimedean groups `G` and `H`, arbitrary supplied
left Haar measures `μG` and `μH`, a continuous homomorphism `φ : H →* G`,
and any smooth complex representation `ρ` of `H` on an algebraic vector space
`V`. It proves, inside the original `NonUnitalModuleTensor.Tensor`, that

```text
rightRepresentation μG φ h⁻¹ T ⊗ w = T ⊗ ρ(h)w.
```

The right action in this quotient is the published `Homomorphism.rightModule`,
and the left coefficient action is `heckeNonUnitalModule μH ρ hρ`.
No replacement tensor product or additional balancing relations are imposed.
By `rightRepresentation_apply` the first test is
`x ↦ haarScale (φ h) * T(x * (φ h)⁻¹)`, so the equality retains the modular
factor required for Haar distributions.

The proof has three steps.

1. `haarInversion_normalizedIndicator` proves that distribution inversion fixes
   a compact-open normalized indicator. The modular character is one on the
   subgroup by the published compact-open modular-character theorem; subgroup
   membership is invariant under inversion. This identity itself needs no Haar,
   Hausdorff, or Borel-space assumptions.
2. `Homomorphism.rightModule_leftTranslate` proves
   `op(leftTranslated μH h a) • T = op a • rightRepresentation μG φ h⁻¹ T`.
   It applies the genuine weighted `rightModule_integral` and substitutes
   `t = h*s` using left invariance of `μH`. Multiplicativity of `haarScale`
   and the right-representation formula identify the integrands.
3. For the tensor identity, intersect smooth stabilizers of
   `rightRepresentation μG φ h⁻¹ T` and `w`, then choose a compact open
   subgroup inside that intersection. Its normalized indicator `e` fixes
   both vectors. The original Hecke balancing law, the translated-test
   identity, and `integratedAction_leftTranslate` give the displayed equality.

This is derived infrastructure for the original Hecke-tensor argument of
Renard III.2.6, printed pp.75–77 / PDF pp.81–83, source
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
The proof uses `CompactInductionRightFormula`, `ActionLocalUnits`,
`IntegratedConvolution`, and `NonUnitalModuleTensor`. It does not assert
bijectivity of the compact-induction comparison.

The two group universes `uG`, `uH` and coefficient-carrier universe `v` are
independent. There is no second-countability, unimodularity, closed-image,
or topology-on-coefficients assumption.
