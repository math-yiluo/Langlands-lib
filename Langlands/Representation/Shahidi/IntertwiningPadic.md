# Shahidi's intertwining operator over a p-adic field

This module is the p-adic case of the operator in
`Langlands.Representation.Shahidi.IntertwiningInduced`. The source is
F. Shahidi, *Fourier transforms of intertwining operators and Plancherel
measures for GL(n)*, American Journal of Mathematics 106 (1984), 67–111,
printed page 72:

\[
A(s,\pi,w_{m,n})f(g)=\int_{U'} f(w_{m,n}u'g)\,du'.
\]

The registered original is `shahidi-1984-fourier`, SHA256
`a10d5c605d94d4e85d0e5f453d6a8c233d91e3cb60d538f430d8ad900cbb6b29`.
The author is Worker 11.

The general module builds the operator from four hypotheses: a source
covariance law, a target covariance law, a Jacobian law for the measure `du'`,
and compact open cofinality of the Levi `GL_m(F) × GL_n(F)`. This module proves
all four for the p-adic induced representations of
`Langlands.Representation.Shahidi.Induction`, and so defines the operator from
the p-adic `I(s, π₁ ⊗ π₂)` to the p-adic `I(-s, π₂ ⊗ π₁)`. Values are carried
from `V₁ ⊗ V₂` to `V₂ ⊗ V₁` by the tensor flip, as in `IntertwiningInduced`,
whose Markdown explains why this reading is needed.

The unit builds on these published modules:

- `IntertwiningInduced`: `IsSourceCovariance`, `IsTargetCovariance`,
  `IsModulusScaling`, `convergenceDomain`, `smoothInduced_mem_convergenceDomain`,
  `swappedOperator` and its laws `hasIntegral_swappedOperator`,
  `swappedOperator_eval`, `swappedOperator_smoothInduced`, and `pairFlip`,
  `pairRepresentation`, `isSmooth_pairRepresentation`;
- `IntertwiningCovariance`: `map_rectangularConj_padic`, the scaling of an
  additive Haar measure under `a ↦ h₂⁻¹ a h₁`;
- `Induction`: the p-adic `ShahidiSourceSpace`, `shahidiSource`,
  `shahidiSourceEval`, `ShahidiTargetSpace`, `shahidiTarget`,
  `shahidiTargetEval`, `shahidiTwistedPair`, `shahidiAbsoluteValue`,
  `determinantComplexPower_apply`, `determinantAbs_eq_determinantNorm`,
  `leviModulus_twoBlocks` (general and p-adic), `leviModulus_swappedTwoBlocks`,
  `leviProjection_swappedParabolicEquiv`, `blockTensor_pairFamily_twist` and
  `sqrt_mul_cpow_mul_cpow`;
- the Library's `T.leviCompactOpen`, `T.leviTopology` and
  `T.leviTopologicalGroup` for block Levis.

All declarations lie in `Langlands.PadicField.TopologicalData`, for
`F : PadicField p` and a supplied realization `T : F.TopologicalData`. The
absolute value is `T.shahidiAbsoluteValue`, the Library's residue-normalized
`T.normalizedAbs` with `|ϖ| = q⁻¹`.

## Topology and cofinality

- `shahidiTopologicalRing` (private) gives `IsTopologicalRing F.Carrier` for
  `T.topology`. The general layer needs this instance. The proof is instance
  search from the local-field structure in `T`.
- `leviCompactOpenCofinal B`: for every block shape `B`, every open subgroup
  of the Levi `B.Levi F.Carrier` contains a compact open subgroup. The proof
  applies the Library's `T.leviCompactOpen B` to the open subgroup, which is a
  neighborhood of `1`. For `B = twoBlocks m n hm hn` this is the cofinality
  hypothesis of the general operator.

## The covariance laws

Let `0 < m`, `0 < n`, `s : ℂ`, and let `π₁`, `π₂` be complex representations
of `GL_m(F)` and `GL_n(F)`.

- `shahidiSourceInducing hm hn s π₁ π₂` is the inducing representation of the
  p-adic `I(s, π₁ ⊗ π₂)`. It is reducible notation for the published twist of
  the block tensor of `T.shahidiTwistedPair s π₁ π₂` by
  `T.parabolicHalfModulus`, as in `ShahidiSourceSpace`.
  `shahidiTargetInducing hm hn s π₁ π₂` is the same for `I(-s, π₂ ⊗ π₁)` on
  the parabolic of `swappedTwoBlocks m n hm hn`.
- `isSourceCovariance_shahidiSource`: `shahidiSourceInducing` satisfies
  `IsSourceCovariance` for `T.shahidiAbsoluteValue`, that is, it acts by
  `|det p₁|^((s+n)/2) |det p₂|^(-(s+m)/2) (π₁ ⊗ π₂)(p₁, p₂)`. The proof
  follows the published `shahidiSource_covariant`: it splits off the twists by
  `blockTensor_pairFamily_twist`, rewrites the half modulus by
  `T.leviModulus_twoBlocks` and the twists by `determinantComplexPower_apply`,
  and combines the scalars by `sqrt_mul_cpow_mul_cpow`.
- `isTargetCovariance_shahidiTarget`: `shahidiTargetInducing` satisfies
  `IsTargetCovariance`, with exponents `(m-s)/2` and `(s-n)/2`. The proof is
  the same computation after `leviProjection_swappedParabolicEquiv`, with
  `T.leviModulus_swappedTwoBlocks`.

## The Jacobian law

Let `F.Carrier` carry a measurable structure with `MeasurableAdd₂` and
`MeasurableMul`.

- `isModulusScaling_padic hm hn`: for `T.topology`, every additive Haar
  measure `μ` on the `n` by `m` matrices over `F`, Borel for the product
  topology, satisfies `IsModulusScaling hm hn T.shahidiAbsoluteValue μ`. So
  `a ↦ h₂⁻¹ a h₁` multiplies `μ` by `|det h₂|^m |det h₁|^(-n)` for
  `h₂ ∈ GL_n(F)` and `h₁ ∈ GL_m(F)`. The proof starts from the published
  `map_rectangularConj_padic`. It rewrites the general `leviModulus` by
  `leviModulus_twoBlocks` and `determinantAbs_eq_determinantNorm`, then
  moves the unit coercion through quotients and powers.

## The operator

Fix a measure `μ` on the `n` by `m` matrices over `F`.

- `shahidiSourceDomain hm hn s π₁ π₂ μ` is the convergence domain of (0.1)
  inside the p-adic `I(s, π₁ ⊗ π₂)`. It consists of the `f` for which
  `∫_{U'} f(w_{m,n} u' g) du'` exists at every `g`, as a weak integral tested
  by the smooth dual of `π₁ ⊗ π₂`. It is reducible notation for the general
  `convergenceDomain` with `shahidiSourceInducing`.
- `shahidiSource_mem_shahidiSourceDomain`: the domain is stable under the
  action `shahidiSource`, so it is a subrepresentation.

Now let `μ` be invariant under left translation, with
`hμ : IsModulusScaling hm hn T.shahidiAbsoluteValue μ`. For an additive Haar
measure, `isModulusScaling_padic` supplies `hμ`.

- `shahidiIntertwining hm hn s π₁ π₂ hμ hπ₁ hπ₂` is Shahidi's
  `A(s, π, w_{m,n})` over the p-adic field, for smooth `π₁` and `π₂`. It is a
  complex-linear map from `shahidiSourceDomain` to `ShahidiTargetSpace`, the
  space of the p-adic `I(-s, π₂ ⊗ π₁)`. It is the general `swappedOperator`
  with the cofinality, the two covariance laws above and `hμ`.
- `shahidiTargetEval_shahidiIntertwining` (by `rfl`): the value of `A f` at
  `g` is the flip of the published `intertwiningOperator` of `f` at `g`.
- `hasIntegral_shahidiIntertwining`: `flip⁻¹ (A f(g))` is the weak integral of
  `a ↦ f(w_{m,n} u'(a) g)` against `μ`. Here `w_{m,n}` is the published
  `blockWeyl m n` and `u'(a)` is `intertwiningUnipotent m n a`.
- `shahidiIntertwining_eval`: for every smooth functional `ℓ` of `π₁ ⊗ π₂`,
  `ℓ(flip⁻¹ (A f(g))) = ∫ ℓ(f(w_{m,n} u'(a) g)) dμ(a)`.
- `shahidiIntertwining_shahidiSource`:
  `A (I(s)(g) f) = I(-s)(g) (A f)`. So `A(s, π, w_{m,n})` intertwines the
  subrepresentation `shahidiSourceDomain` of the p-adic `I(s, π₁ ⊗ π₂)` with
  the p-adic `I(-s, π₂ ⊗ π₁)`.

The last four results are the general `swappedOperator` laws for these
inputs.

**Field scope.** This layer covers exactly the Library's `PadicField p`, a
field with a specified finite-dimensional algebra structure over Mathlib's
`Padic p`, with a supplied `TopologicalData`. Positive-characteristic local
fields are covered only by the general layer of `IntertwiningInduced`.

## What is not claimed

This unit does not claim the following:

- that the integral converges for `f ∈ I(s,π)` when `Re s` is large. The
  domain `shahidiSourceDomain` is defined by convergence, and this unit does
  not show that it is all of `I(s,π)` for any `s`;
- that `A(s,π,w_{m,n})` has a rational continuation in `q^(-s)`;
- any Haar normalization of `du'`. Every additive Haar measure is allowed;
- the comparison of Shahidi's `GL_r(O)`-finite functions with the Library's
  smooth induction, which `Induction` also leaves open;
- a comparison of `shahidiIntertwining` with the general
  `intertwiningInduced` for `T.shahidiAbsoluteValue`. The two use different
  but equal inducing data, as explained in `Induction`; this unit proves the
  hypotheses of `swappedOperator` directly for the p-adic data.

These remain obligations for later units of the parent task.
