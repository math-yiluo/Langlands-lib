# Split-kernel value integrals over a fixed intersection subgroup

This pair defines the linear map
`Langlands.Induction.splitKernelValueIntegral`, which integrates the values
of a compactly induced function, pushed through a coefficient map `T`, over
the left quotient of the kernel of a split retraction. It proves the laws of
this map: kernel invariance, the section law, surjectivity, a kernel
criterion, and compatibility with linear maps of values. The pair was written
for task `d6be9c3b-ff6f-425c-9bb5-84c973b9568f` (surviving graded transitions
of the corrected Aubert complex). The module
`Langlands.Representation.Aubert.General.CorrectedOrbitJacquet` specializes it
to the orbit Jacquet maps of that complex.

Author: Worker 1255.

## Provenance

This is an internal derived construction, not a statement transcribed from
the literature. It is the coefficient-valued form of the split-kernel
relative integral `Langlands.Induction.splitKernelCompactIntegral`
(SplitKernelIntegral). Its laws are reduced to the published results on that
integral:

- `splitKernelSection`, `isCompact_quotientSupport_splitKernel_restrict`,
  `splitKernelCompactRestrict` and `splitKernelCompactEquiv`
  (SplitKernelCompact);
- `splitKernelCompactIntegral`, `splitKernelCompactCoinvariantDesc` and
  `splitKernelCompactCoinvariantDesc_bijective`, the bijectivity of the
  descended integral on kernel coinvariants (SplitKernelIntegral);
- `splitKernelConjugation`, `splitKernelConjugation_mem`,
  `splitKernelCoefficientAction` and `splitKernelCompactIntegral_section`
  (SplitKernelCovariance);
- `eval_covariant` (CompactQuotientProof) and `quotientCoinvariantSimple`
  (CompactCoinvariantIntegral);
- the algebraic integral of finite simple functions,
  `HarmonicAnalysis.AlgebraicIntegral.integral` and its laws `integral_add`,
  `integral_smul`, `integral_comp_measurePreserving` and `integral_linearMap`
  (HarmonicAnalysis/AlgebraicIntegral), and `compactlySupportedSimpleFunc`
  (HarmonicAnalysis/AlgebraicIntegrand);
- the quotient operations `descend`, `quotientMap` and `rightTranslate` of
  `LeftQuotient` (Group/LeftQuotient), and
  `QuotientIntegration.subgroupAutomorphism`
  (Analysis/Local/QuotientAutomorphismStatement);
- Mathlib's automorphism Haar character `MeasureTheory.mulEquivHaarChar`.

## Setting

`G` is a topological group, `L` a group and `r : G →* L` a group homomorphism.
`H` is a subgroup of `G`, `σ : Representation ℂ H V` is a representation and
`T : V →ₗ[ℂ] W` is a linear map with

```text
hT : ∀ h : H, (h : G) ∈ r.ker → ∀ v, T (σ h v) = T v,
```

so `T` kills the action of `H ∩ ker r`. The integration subgroup is a
subgroup `I` of `r.ker` given together with

```text
hI : ∀ n : r.ker, n ∈ I ↔ (n : G) ∈ H.
```

So `I` has the same points as `H.comap r.ker.subtype`, but it is a separate
parameter. Two subgroups `H` and `H'` with the same kernel intersection can
therefore be integrated over the same quotient `LeftQuotient I` with the same
measure, and the comparison lemmas below need no transport between quotients.
The proofs of the deeper laws replace `I` by `H.comap r.ker.subtype` with
`obtain rfl : I = H.comap r.ker.subtype := Subgroup.ext hI`.

For the integral, `L` is a topological group with a homomorphism
`s : L →* G`, `hrs : ∀ l, r (s l) = l`, `r` and `s` are continuous, and
`hsH : ∀ l, s l ∈ H`.

## The value function and the integral

- `splitKernelValue_left_mul`: for `f` in `CompactFunctions H σ`, `i ∈ I` and
  `n ∈ ker r`, `T (f (i n)) = T (f n)`. This is the covariance
  `f (h g) = σ h (f g)` (`eval_covariant`) followed by `hT`.
- `splitKernelValueFunction` is the function `I n ↦ T (f n)` on
  `LeftQuotient I`, descended through `QuotientIntegration.descend`;
  `splitKernelValueFunction_mk` is its value on a coset (by `rfl`).
- `splitKernelValueFunction_isLocallyConstant`: it is locally constant,
  because `f` is locally constant and the quotient map is a quotient map.
- `splitKernelValueFunction_translate`: translating `f` by `n ∈ ker r` is the
  quotient right translation `rightTranslate I n` of the value function.
- `splitKernelValueFunction_hasCompactSupport`: it has compact support. The
  proof replaces `I` by the intersection subgroup and uses the published
  compactness `isCompact_quotientSupport_splitKernel_restrict` of the support
  of the kernel restriction of `f`. The support of the value function is a
  closed subset of the closure of that support, since `f n = 0` gives
  `T (f n) = 0`.
- `splitKernelValueSimple` is the value function as a finite simple function
  (`compactlySupportedSimpleFunc`). `splitKernelValueSimple_add` and
  `splitKernelValueSimple_smul` are its linearity in `f`, and
  `splitKernelValueSimple_finMeasSupp` gives finite-measure support for every
  measure `ν` that is finite on compact sets.
- `splitKernelValueIntegral ν : CompactFunctions H σ →ₗ[ℂ] W` sends `f` to the
  algebraic integral of the simple function over `ν`. Informally,

  ```text
  f ↦ ∫_{I \ ker r} T (f n) dν(I n).
  ```

  `splitKernelValueIntegral_apply` unfolds it.

## Laws over one quotient

- `splitKernelValueIntegral_translate`: if right translation by every element
  of `ker r` preserves `ν`, then translating `f` by `n ∈ ker r` does not change
  the integral. The simple function of the translate is the composite with
  `rightTranslate I n` (`splitKernelValueFunction_translate`), and
  `integral_comp_measurePreserving` applies.
- `splitKernelValueIntegral_map_of_eval`: take a second datum `H'`, `σ'`,
  `T' : V' →ₗ[ℂ] W'` with the same integration subgroup `I` (proof `hI'`), and
  a linear map `A : W →ₗ[ℂ] W'`. If
  `T' (f' n) = A (T (f n))` for all `n ∈ ker r`, then the integral of `f'` is
  `A` applied to the integral of `f`. The simple function of `f'` is the
  `A`-image of that of `f`, and `integral_linearMap` applies.
- `splitKernelValueIntegral_eq_of_eval` is the case `A = LinearMap.id`: equal
  values give equal integrals.

## Descent to kernel coinvariants

- `splitKernelValueDescent` is the map `T` descended to the coinvariants of
  `σ` restricted to `H ∩ ker r`, through `Representation.Coinvariants.lift`
  and `hT`. `splitKernelValueDescent_mk` is its value on a class (by `rfl`),
  and `splitKernelValueDescent_surjective` says it is surjective if `T` is.
- `splitKernelValueDescent_coefficientAction`: if `T` carries the action of
  the section values to a representation `τ` of `L`, that is
  `T (σ (splitKernelSection s H hsH l) v) = τ l (T v)`, then the descended map
  carries the published coefficient action `splitKernelCoefficientAction` to
  `τ`.
- `splitKernelValueIntegral_eq_descent`: for `I = H.comap r.ker.subtype`, `H`
  closed, `G` locally compact and `σ` smooth, the value integral is the
  descended map applied to the published integral `splitKernelCompactIntegral`.
  Both sides are integrals of simple functions; the simple function of the
  value integral is the image of `quotientCoinvariantSimple` under the
  descended map, and `integral_linearMap` applies.

## Section law, surjectivity and kernel

Here `G` is also Hausdorff, `ker r` is locally compact, and `ker r`, `I` and
`LeftQuotient I` carry Borel measurable structures.

- `splitKernelValue_conjugation_mem`: the inverse conjugation
  `splitKernelConjugation r s l` preserves `I`, by `hI` and the published
  `splitKernelConjugation_mem`.
- `splitKernelValueRatio l` is the positive real

  ```text
  mulEquivHaarChar (αI_l) / mulEquivHaarChar (α_l),
  ```

  where `α_l = splitKernelConjugation r s l` acts on `ker r` and `αI_l` is its
  restriction to `I` (`QuotientIntegration.subgroupAutomorphism`). For
  `I = H.comap r.ker.subtype` this is the published Haar ratio.
- `splitKernelValueIntegral_section`: let `μN` and `μI` be regular Haar
  measures on `ker r` and `I`, with `μI` right invariant, and let `ν` be
  compatible with them (`IsCompatible I μN μI ν`). If `T` intertwines the
  section values with `τ` as above, then

  ```text
  Θ (s l · f) = splitKernelValueRatio l • τ l (Θ f).
  ```

  The proof replaces `I` by the intersection subgroup, rewrites both integrals
  with `splitKernelValueIntegral_eq_descent`, applies the published section law
  `splitKernelCompactIntegral_section`, and moves the action through the
  descended map with `splitKernelValueDescent_coefficientAction`.
- `splitKernelValueIntegral_surjective`: assume moreover that compact open
  subgroups form a neighborhood basis of `1` in `ker r` (`hBasis`), that `μN`
  is right invariant, and that `T` is surjective. Then the value integral is
  surjective. A value `T v` is the descended map applied to the class of `v`.
  The published bijectivity `splitKernelCompactCoinvariantDesc_bijective` gives
  a function `f` whose integral is that class, and
  `splitKernelValueIntegral_eq_descent` transfers this to the value integral.
- `splitKernelValueIntegral_mem_ker`: under the same assumptions, if the
  descended map is injective and the value integral of `f` is zero, then `f`
  lies in `Representation.Coinvariants.ker` of the restriction of
  `compactInduced H σ` to `ker r`, the span of the elements `n · f - f`. The
  integral of `f` in the published coinvariant integral is zero by
  injectivity, and the injectivity half of
  `splitKernelCompactCoinvariantDesc_bijective` shows that the class of `f` in
  the kernel coinvariants is zero.
