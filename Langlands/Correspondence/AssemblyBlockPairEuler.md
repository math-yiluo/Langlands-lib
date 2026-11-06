# Local block-pair Euler comparisons for assembly

This module is an internal bridge between the published algebraic
Weil–Deligne Euler statements and the arithmetic rational L-factor
interfaces used by segment-pair assembly. Its proposition
`AssemblyBlockPairEulerReductionStatement` is the conjunction of two
implications, for every prime `p` and `F : PadicField.{uF} p`, with an
independent Weil carrier universe `uP`:

- `WDEulerPairBlockStatement.{0,uF,uP,uP}` implies
  `ArithmeticBlockPairLFactor.{uF,uP} F`.
- `WDEulerDualPairBlockStatement.{0,uF,uP,uP}` implies
  `ArithmeticDualBlockPairLFactor.{uF,uP} F`, defined in this module.

The theorem `assemblyBlockPairEulerReduction` proves this conjunction.
The two algebraic block formulas remain premises. No unconditional
block formula, epsilon compatibility, classification, or correspondence
inheritance theorem is asserted.

For the second implication, write `ω` for the actual local norm character,
`I` for local inertia, `Φ` for the published local geometric Frobenius,
and `Z(B)` for the zero-monodromy pair attached to `B`.
`ArithmeticDualBlockPairLFactor` asserts, for arbitrary local Weil
representations `B, B'` and natural numbers `a, b`,

`L_I,Φ((block ω B (a+1) ⊗ block ω B' (b+1))∨)`

`= ∏_{0 ≤ j < min(a+1,b+1)} L_I,Φ((Z(ω^j B) ⊗ Z(B'))∨)`.

Here `L_I,Φ` is `LocalFactor.WeilDeligne.rationalLFactorClass` on genuine
pair classes. The dual is taken after tensoring. Thus the positive twist
`ω^j` on the right becomes `ω^(-j)` on the corresponding dual Weil
representation. Both sides are rational functions over `ℂ`, without
evaluating at a complex parameter.

The generic theorem `rationalLFactor_zeroTensorTwist` works over any
field `K`, group `G`, norm character `ν`, normal subgroup `I`, and
character `χ` trivial on `I`, with independent carrier universes for
the two finite-dimensional representations. It identifies the factor
of `Z(twist χ A) ⊗ Z(B)` with the rational factor of
`(χ Φ : K)` times Frobenius on `(A ⊗ B)^I`.
The proof computes the tensor action and verifies that its monodromy
is zero on pure tensors. It then uses the subtype inclusion of the
actual invariant subspace into the tensor carrier. Triviality of `χ`
on inertia gives precisely the image required by the published
`rationalLFactor_eq_of_embedding`; the same action computation proves
that the inclusion intertwines the specified scaled Frobenius.
The invariant space is taken after tensoring the Weil representations.

The generic theorem `rationalLFactor_dual_zeroTensorTwist` uses
`tensorDualEquiv` to pass from the dual tensor to the tensor of the
two dual pairs. An identity-carrier equivalence, justified by the
published `Langlands.dual_twist`, replaces the dual of the first
zero-monodromy twist by the inverse-character twist of the dual.
`dualZeroMonodromyEquiv` treats the second factor.
The preceding invariant-space comparison, now with `χ⁻¹`, finishes
the proof. The negative-transpose monodromy remains zero.

For the two local implications, the proof specializes the supplied
algebraic statements to `ℂ`, the actual local Weil group, `I`, `ω`,
and `Φ`. The published `localNormCharacter_on_inertia` supplies
triviality on inertia. The rational-factor conjunct of each premise
gives its scalar-Frobenius product. The generic comparisons identify
each factor with the required actual twisted zero-monodromy tensor.
The ordinary formula uses exponent `a+b-j`; the dual formula uses
exponent `-j`, obtained by inverting `ω^j`. Class-valued factors
reduce to the factors of these actual representatives.

The provenance is internal: these are deductions between existing
Library definitions, equivalences, and explicitly supplied proposition
values. No external mathematical assertion is introduced as a proved
input. Worker 584 implemented the comparisons; Worker 1695 supplied
the local consumer interface and dual-product formulation.
