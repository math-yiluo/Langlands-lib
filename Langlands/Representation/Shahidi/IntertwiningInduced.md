# Shahidi's intertwining operator `I(s, π₁ ⊗ π₂) → I(-s, π₂ ⊗ π₁)`

This module specializes the function-level integral (0.1) to the induced
representations of `Langlands.Representation.Shahidi.Induction`. The source is
F. Shahidi, *Fourier transforms of intertwining operators and Plancherel
measures for GL(n)*, American Journal of Mathematics 106 (1984), 67–111,
printed page 72:

\[
A(s,\pi,w_{m,n})f(g)=\int_{U'} f(w_{m,n}u'g)\,du'.
\]

The registered original is `shahidi-1984-fourier`, SHA256
`a10d5c605d94d4e85d0e5f453d6a8c233d91e3cb60d538f430d8ad900cbb6b29`.
The author is Worker 11.

On page 72 the source calls (0.1) an intertwining operator on `I(s,π)`, where
`π = π₁ ⊗ π₂`. Its display (0.3) applies the Whittaker functional of
`I(-s,π')`, with `π' = π₂ ⊗ π₁`, to `A f`. The source does not spell out how
the values of `A f`, which lie in the space `V₁ ⊗ V₂` of `π`, become values in
the space `V₂ ⊗ V₁` of `π'`. This unit uses the tensor flip
`v₁ ⊗ v₂ ↦ v₂ ⊗ v₁`, which is the reading under which `A f` lies in
`I(-s,π')`. The proofs below show that with the flip `A f` has exactly the
covariance of `I(-s,π')`.

The unit builds on three published modules:

- `IntertwiningIntegral`: the weak integral `intertwiningOperator m n ρ μ
  hcofinal hρ` on its domain `intertwiningDomain m n ρ μ`, for an arbitrary
  function with values in a representation `ρ`, and its right-translation law;
- `IntertwiningCovariance`: `intertwiningOperator_parabolic` (left
  transformation under the `(n,m)` parabolic, carried by `swapRank`),
  `intertwiningOperator_mul_right`, `twoBlockLeviSwap` and `rectangularConj`;
- `Induction`: `SourceSpace`, `source`, `TargetSpace`, `target`,
  `sourceEval`, `targetEval`, the shape `swappedTwoBlocks`,
  `swappedParabolicEquiv`, the general `leviModulus` and the scalar identity
  `sqrt_mul_cpow_mul_cpow`.

All declarations lie in `Langlands.Shahidi`.

## The tensor flip

These results are internal to the formalization.

- For a family `V : Fin 2 → Type` of modules over a commutative ring,
  `pairSplit V` is the linear equivalence from `PiTensorProduct R V` to the
  binary tensor `V 0 ⊗ V 1`. It is the published
  `FiniteTensor.headTailLinearEquiv` followed by Mathlib's
  `PiTensorProduct.subsingletonEquiv` on the one-factor tail.
  `pairSplit_tprod` gives its value `v 0 ⊗ v 1` on pure tensors.
- `pairSwap a b`, for linear equivalences `a : V 0 ≃ W 1` and
  `b : V 1 ≃ W 0`, sends `x ⊗ y` to `b y ⊗ a x`. It is `pairSplit V`, then the
  binary commutativity equivalence and `TensorProduct.congr b a`, then
  `(pairSplit W)⁻¹`. The lemmas are `pairSplit_pairSwap` and `pairSwap_tprod`.
- `pairSplit_external`: under `pairSplit`, the published external tensor
  action `FiniteTensor.external ρ h` becomes `TensorProduct.map (ρ 0 (h 0))
  (ρ 1 (h 1))`.
- `pairSwap_external`: if `a` intertwines `ρ 0 (h 0)` with `ρ' 1 (h' 1)` and
  `b` intertwines `ρ 1 (h 1)` with `ρ' 0 (h' 0)`, then `pairSwap a b`
  intertwines the external actions of `h` and `h'`.
- `pairFlip` is `pairSwap` with both maps the identity. It is the flip
  `PiTensorProduct ℂ (pairCarrier V₁ V₂) ≃ PiTensorProduct ℂ (pairCarrier V₂ V₁)`
  of the published two-factor carriers. `pairFlip_pairTensor` gives
  `pairTensor v₁ v₂ ↦ pairTensor v₂ v₁`.
- `pairRepresentation hm hn π₁ π₂` is the published block tensor
  `(twoBlocks m n hm hn).blockTensor (pairFamily π₁ π₂)`, the representation
  `π₁ ⊗ π₂` of the Levi `GL_m(F) × GL_n(F)`. It is reducible notation.
- `pairFlip_pairRepresentation`: for a Levi element `l = (h₂, h₁)` of
  `twoBlocks n m`, the flip carries `(π₁ ⊗ π₂)(h₁, h₂)` to
  `(π₂ ⊗ π₁)(h₂, h₁)`. Here `(h₁, h₂)` is `twoBlockLeviSwap hm hn F l`.

## Exponents

Let `F` be a field, `abv : AbsoluteValue F ℝ`, `0 < m`, `0 < n` and `s : ℂ`.
`|x|` below is the complex number `abv x`, and complex powers are Mathlib's
`cpow`.

- `sourceScalar abv hm hn s (h₁, h₂)` is
  `|det h₁|^((s+n)/2) · |det h₂|^(-(s+m)/2)` on the Levi of `twoBlocks m n`.
  These are the normalized exponents of `I(s, π₁ ⊗ π₂)` in `Induction`.
- `targetScalar abv hm hn s (h₂, h₁)` is
  `|det h₂|^((m-s)/2) · |det h₁|^((s-n)/2)` on the Levi of `twoBlocks n m`.
  These are the exponents of `I(-s, π₂ ⊗ π₁)` in `Induction`.
- `sourceScalar_swap_mul_leviModulus`: for every Levi element `l = (h₂, h₁)`
  of `twoBlocks n m`,

  \[
  \mathrm{sourceScalar}(h_1,h_2)\cdot |\det h_2|^m\,|\det h_1|^{-n}
    = \mathrm{targetScalar}(h_2,h_1).
  \]

  The middle factor is the published general `leviModulus abv (twoBlocks n m
  hn hm) l`, rewritten by `leviModulus_twoBlocks`. The proof splits
  `(m-s)/2 = -(s+m)/2 + m` and `(s-n)/2 = (s+n)/2 - n` and uses
  `Complex.cpow_add`, `Complex.cpow_sub` and `Complex.cpow_natCast` at the
  positive reals `|det h₂|` and `|det h₁|`.

## The covariance laws and the Jacobian law

These three predicates name the hypotheses of the operator. They are
internal to the formalization.

- `IsSourceCovariance hm hn π₁ π₂ abv s σ`, for a representation `σ` of the
  `(m,n)` parabolic on `V₁ ⊗ V₂`, says
  `σ(p) v = sourceScalar(l_p) · (π₁ ⊗ π₂)(l_p) v` for every `p` and `v`. Here
  `l_p` is the published Levi projection of `p`.
- `IsTargetCovariance hm hn π₁ π₂ abv s σ'`, for a representation `σ'` of the
  parabolic of `swappedTwoBlocks m n hm hn` on `V₂ ⊗ V₁`, says
  `σ'(swappedParabolicEquiv p) v = targetScalar(l_p) · (π₂ ⊗ π₁)(l_p) v` for
  every `p` in the parabolic of `twoBlocks n m` and every `v`. Since
  `swappedParabolicEquiv` is a group isomorphism, this determines `σ'`.
- `IsModulusScaling hm hn abv μ`, for a measure `μ` on the `n` by `m`
  matrices, says `μ.map (rectangularConj h₂ h₁) = leviModulus abv (twoBlocks n m
  hn hm) (h₂, h₁) • μ` for every Levi element. So the change of variables
  `a ↦ h₂⁻¹ a h₁` multiplies `μ` by `|det h₂|^m |det h₁|^(-n)`. It needs
  `MeasurableAdd₂ F` and `MeasurableMul F`.

Over a p-adic field with an additive Haar measure, the published
`map_rectangularConj_padic` gives this scaling with the Library's
`T.determinantNorm`. Converting it to `IsModulusScaling` for an absolute value
that agrees with `T.normalizedAbs` is left to the p-adic unit. This unit does
not state it.

## The operator between covariant function spaces

Let `F` also carry a topology making it a topological ring, and a measurable
structure. Let `σ` be a representation of the `(m,n)` parabolic on `V₁ ⊗ V₂`.

- `inducedFunction P σ` is the linear map from the published
  `Induction.SmoothFunctions P σ` to the underlying functions.
- `convergenceDomain hm hn π₁ π₂ μ σ` is the preimage of the published
  `intertwiningDomain m n (π₁ ⊗ π₂) μ`. It consists of the smooth covariant
  `f` for which `∫ f(w u' g) du'` exists at every `g`, as a weak integral
  tested by the smooth dual of `π₁ ⊗ π₂` (`mem_convergenceDomain`).
- `smoothInduced_mem_convergenceDomain`: the domain is stable under the
  published right-translation action `Induction.smoothInduced`. This is the
  published `rightTranslate_mem_intertwiningDomain`.
- `isSmooth_pairRepresentation`: if `π₁` and `π₂` are smooth, so is
  `π₁ ⊗ π₂`. This is the published `FiniteTensor.isSmooth_external`.

Now assume `hcofinal : CompactOpenCofinal` for the Levi of `twoBlocks m n`,
with `π₁` and `π₂` smooth. These are the uniqueness hypotheses of the published
`intertwiningOperator`.

- `swappedIntegral` sends `f` in the convergence domain to the function
  `g ↦ flip (intertwiningOperator … f g)`, with values in `V₂ ⊗ V₁`
  (`swappedIntegral_apply`, by `rfl`).

Next assume `MeasurableAdd₂ F`, `MeasurableMul F`, that `μ` is invariant under
left translation, `IsSourceCovariance … σ` and `IsModulusScaling … μ`.

- `swappedIntegral_swapRank_mul`: for `p` in the parabolic of `twoBlocks n m`
  with Levi projection `l`,
  `swappedIntegral f (swapRank p x) = targetScalar(l) · (π₂ ⊗ π₁)(l)
  (swappedIntegral f x)`. The proof applies the published
  `intertwiningOperator_parabolic` with `χ = sourceScalar`, `τ = id` and
  `c = leviModulus`. It then moves the flip across the action by
  `pairFlip_pairRepresentation` and combines the scalars by
  `sourceScalar_swap_mul_leviModulus`.
- `swappedIntegral_mem_coindV`: with `IsTargetCovariance … σ'` as well, the
  function satisfies the published left covariance `Representation.coindV`
  for `σ'`. Each element of the swapped parabolic is written as
  `swappedParabolicEquiv` of its preimage.
- `swappedIntegral_mul_right`: if `f(x k) = f(x)` for all `x`, then the same
  holds for `swappedIntegral f`. This is the published
  `intertwiningOperator_mul_right`.
- `swappedOperator hm hn hcofinal hπ₁ hπ₂ hσ hσ' hμ` is the resulting linear
  map from the convergence domain to `Induction.SmoothFunctions` for `σ'`.
  Smoothness holds because the operator keeps the right invariance of `f`
  under the open subgroup that fixes `f`. `swappedOperator_apply` records its
  values by `rfl`.
- `hasIntegral_swappedOperator`: `flip⁻¹ (A f(g))` is the weak integral of
  `a ↦ f(w_{m,n} u'(a) g)` against `μ`.
- `swappedOperator_eval`: for every smooth functional `ℓ` of `π₁ ⊗ π₂`,
  `ℓ(flip⁻¹ (A f(g))) = ∫ ℓ(f(w_{m,n} u'(a) g)) dμ(a)`.
- `swappedOperator_smoothInduced`: the operator commutes with right
  translation by every `g`. This is the published
  `intertwiningOperator_rightTranslate`.

## The operator on the induced spaces

Let `abv` satisfy the published `IsOpenNormOne abv` (`hopen`), the smoothness
hypothesis of the general induction layer.

- `isSourceCovariance_source`: the inducing representation of the published
  `source abv hopen hm hn s π₁ π₂`, which is `I(s, π₁ ⊗ π₂)`, satisfies
  `IsSourceCovariance`. The proof unfolds the published normalized induction.
  Its inducing scalar is the published `leviHalfCharacter` times the twists
  `|det h₁|^(s/2)` and `|det h₂|^(-s/2)`. The proof combines them by
  `blockTensor_pairFamily_twist`, `leviModulus_twoBlocks` and
  `sqrt_mul_cpow_mul_cpow`.
- `isTargetCovariance_target`: the inducing representation of the published
  `target abv hopen hm hn s π₁ π₂`, which is `I(-s, π₂ ⊗ π₁)`, satisfies
  `IsTargetCovariance`. The proof is the same computation, through
  `leviProjection_swappedParabolicEquiv` and `leviModulus_swappedTwoBlocks`.
- `sourceDomain abv hopen hm hn s π₁ π₂ μ` is the convergence domain inside
  `SourceSpace`, the space of `I(s, π₁ ⊗ π₂)`. `source_mem_sourceDomain`: it
  is stable under the action `source`, so it is a subrepresentation.
- `intertwiningInduced abv hopen hm hn s hcofinal hπ₁ hπ₂ hμ` is Shahidi's
  `A(s, π, w_{m,n})`. It is a complex-linear map from `sourceDomain` to
  `TargetSpace`, the space of `I(-s, π₂ ⊗ π₁)`. Its hypotheses are those of
  `swappedOperator` other than the two covariance laws, which are now proved.
  The measure `μ` must be invariant under left translation and satisfy
  `IsModulusScaling`.
- `targetEval_intertwiningInduced` (by `rfl`): its value at `g` is
  `flip (intertwiningOperator … f g)`.
- `hasIntegral_intertwiningInduced` and `intertwiningInduced_eval`: the weak
  integral and the scalar formula
  `ℓ(flip⁻¹ (A f(g))) = ∫ ℓ(f(w_{m,n} u'(a) g)) dμ(a)`.
- `intertwiningInduced_source`: `A (I(s)(g) f) = I(-s)(g) (A f)`. So
  `A(s, π, w_{m,n})` intertwines the subrepresentation `sourceDomain` of
  `I(s, π₁ ⊗ π₂)` with `I(-s, π₂ ⊗ π₁)`.

**Field scope.** The general layer needs a field with a topology making it a
topological ring, a measurable structure with `MeasurableAdd₂` and
`MeasurableMul`, an absolute value `abv` with `IsOpenNormOne abv`, the
cofinality `hcofinal` of the Levi, and a left-invariant measure `μ` with
`IsModulusScaling`. It makes no use of a uniformizer or of local compactness
beyond these hypotheses.

## What is not claimed

This unit does not claim the following:

- that the integral converges for `f ∈ I(s,π)` when `Re s` is large. The
  domain `sourceDomain` is defined by convergence, and this unit does not
  show that it is all of `I(s,π)` for any `s`;
- that `A(s,π,w_{m,n})` has a rational continuation in `q^(-s)`;
- the p-adic specialization: the cofinality `hcofinal` for the Levi, and
  `IsModulusScaling` for an additive Haar measure;
- any Haar normalization of `du'`;
- the comparison of Shahidi's `GL_r(O)`-finite functions with the Library's
  smooth induction, which `Induction` also leaves open.

These remain obligations for later units of the parent task.
