# Equivariant relative compact-induction integral for a split kernel

This pair packages the split-kernel quotient integral as an equivalence of
`L`-representations, `Langlands.Induction.splitKernelCompactEquivariantEquiv`.
The twisting character is the actual Haar ratio of the section conjugations,
bundled as `Langlands.Induction.splitKernelHaarRatio : L →* ℝ≥0ˣ`. The entry
declaration is the definition `splitKernelCompactEquivariantEquiv`. Its main
property is `Langlands.Induction.splitKernelCompactEquivariantEquiv_natural`,
naturality in the coefficient representation. The pair was written for the
focused prerequisite task `c26863ba-ef18-4ea7-b655-6d3e64474c87` of Worker 76's
parabolic-orbit Jacquet comparison.

Authors: Worker 76 wrote the Lean file and the first version of this text.
Worker 787 added the lemma `splitKernelCompactEquivariantEquiv_toLinearEquiv`,
checked both files against the published Library and expanded this text.

## Provenance

This is an internal derived construction, not a statement transcribed from
the literature. Every declaration combines published Library results with
Mathlib's automorphism Haar character `MeasureTheory.mulEquivHaarChar`:

- `splitKernelConjugation`, `splitKernelConjugation_apply`,
  `splitKernelConjugation_mem`, `splitKernelCoefficientAction` and
  `splitKernelCompactCoinvariantDesc_section` (SplitKernelCovariance);
- `splitKernelCompactCoinvariantEquiv`, `splitKernelCompactCoinvariantEquiv_natural`
  and `isClosed_splitKernelIntersection` (SplitKernelIntegral);
- `QuotientIntegration.subgroupAutomorphism` (restriction of a continuous
  automorphism to a preserved subgroup);
- `Jacquet.complexCharacter` (PositiveCharacter) and `Langlands.twist`
  (Representation/Twist/Definitions);
- Mathlib's `mulEquivHaarChar_refl`, `mulEquivHaarChar_trans` and
  `mulEquivHaarChar_pos`.

No multiplicativity of the scalars, comparison of measures or equivariance law
is assumed. Multiplicativity is proved below from the composition laws.

## Setting

`G` is a topological group, `L` a group, and `r : G →* L`, `s : L →* G` are
group homomorphisms. `H` is a subgroup of `G` with `hsH : ∀ l, s l ∈ H`. Write

```text
N = r.ker,   I = H.comap N.subtype,   α_l = splitKernelConjugation r s l,
```

so that `(α_l n : G) = s(l)⁻¹ * n * s(l)`. The intersection `I` carries its
subgroup topology inside `N`. The universes of `G`, `L`, the coefficient
module `V`, and in naturality the second coefficient module `W`, are
independent.

## The composition laws

- `splitKernelConjugation_one` (simp): `α_1` is `ContinuousMulEquiv.refl N`.
- `splitKernelConjugation_mul`: `α_(l * k) = (α_l).trans (α_k)`, that is,
  `α_(l * k) n = α_k (α_l n)`. Indeed
  `s(l k)⁻¹ * n * s(l k) = s(k)⁻¹ * (s(l)⁻¹ * n * s(l)) * s(k)`, so inverse
  conjugation reverses the order of the factors.
- `splitKernelIntersectionConjugation r s H hsH l : I ≃ₜ* I` is the actual
  restriction `subgroupAutomorphism I α_l hα_l` of `α_l` to `I`, where `hα_l` is
  the published preservation law `splitKernelConjugation_mem`.
- `splitKernelIntersectionConjugation_one` (simp) and
  `splitKernelIntersectionConjugation_mul` are the same two laws for the
  restrictions. Each is proved by evaluating on an element of `I`, passing to
  the underlying element of `N` and applying the kernel law.

These laws need no topology on `L` and no splitting identity.

## The Haar-ratio character

For the character, also assume that `H` is closed in `G`, that `N` is locally
compact, and that `N` and `I` carry Borel measurable structures. Local
compactness of `I` is derived inside each declaration from the closedness of
`I` in `N` (`isClosed_splitKernelIntersection`). `r ∘ s = id` is not needed.

`splitKernelHaarRatio r s H hsH hH : L →* ℝ≥0ˣ` sends `l` to the unit

```text
c_l = mulEquivHaarChar (αI_l) / mulEquivHaarChar (α_l),
αI_l = splitKernelIntersectionConjugation r s H hsH l,
```

the subgroup modulus divided by the kernel modulus. The value is nonzero
because both Haar characters are positive (`mulEquivHaarChar_pos`).

- The identity law uses `splitKernelIntersectionConjugation_one`,
  `splitKernelConjugation_one` and `mulEquivHaarChar_refl`, so `c_1 = 1 / 1`.
- The multiplication law rewrites with the two `_mul` laws and
  `mulEquivHaarChar_trans`. It then closes by `div_mul_div_comm`:
  `(a * b) / (c * d) = (a / c) * (b / d)`.

`splitKernelHaarRatio_apply` (simp, `rfl`) states the value as

```text
(splitKernelHaarRatio r s H hsH hH l : ℝ≥0)
  = mulEquivHaarChar (subgroupAutomorphism I α_l hα_l) / mulEquivHaarChar α_l.
```

The value uses the same orientation as the covariance theorem: the scalar
that appears when a function on `N` is precomposed with `α_l` in the forward
direction. After the embedding `ℝ≥0 → ℝ → ℂ`, it is exactly the scalar `c_l`
of `splitKernelCompactCoinvariantDesc_section`.

## The equivariant equivalence

The equivalence uses exactly the hypotheses of
`splitKernelCompactCoinvariantEquiv`:

- `G` locally compact and Hausdorff, `L` with a topology (not necessarily a
  topological group), `r` and `s` continuous, `hrs : ∀ l, r (s l) = l`, and
  `H` closed;
- a smooth representation `σ : Representation ℂ H V` on an arbitrary complex
  module `V`, with no topology or dimension assumption;
- `N` locally compact, with a basis at the identity of compact open subgroups
  (`hBasis`);
- Borel measurable structures on `N`, `I` and `LeftQuotient I = I \ N`;
- regular left Haar measures `μN` on `N` and `μI` on `I`, both also right
  invariant;
- a measure `ν` on `I \ N`, finite on compact sets, with
  `QuotientIntegration.IsCompatible I μN μI ν` (`hCompatible`).

Write `σI = σ.comp (N.subtype.subgroupComap H)` and
`χ = Jacquet.complexCharacter (splitKernelHaarRatio r s H hsH hH) : L →* ℂˣ`.
Then

```text
splitKernelCompactEquivariantEquiv r s H hsH hrs hr hs hH σ hσ ν hBasis μN μI hCompatible :
  Representation.Equiv (((compactInduced H σ).toCoinvariants N).comp s)
    (twist χ (splitKernelCoefficientAction r s H hsH σ)).
```

The source is Mathlib's representation of `G` on the coinvariants of the
normal subgroup `N` in `compactInduced H σ`, restricted along `s`. The target
is the published section action on `Representation.Coinvariants σI`, with each
operator multiplied by the complex number `χ(l) = c_l`.

- The underlying linear equivalence is `splitKernelCompactCoinvariantEquiv` with
  the same arguments. `splitKernelCompactEquivariantEquiv_toLinearEquiv` records
  this by `rfl`; no new integral or inverse is chosen.
- `splitKernelCompactEquivariantEquiv_mk` (simp, `rfl`) gives the representative
  formula

  ```text
  splitKernelCompactEquivariantEquiv … [f]
    = AlgebraicIntegral.integral ν (quotientCoinvariantSimple I σI (E f)),
  ```

  for `f : CompactFunctions H σ`, where
  `E = splitKernelCompactEquiv r s hrs hr hs H hH hsH σ hσ` is the actual
  restriction of compact functions to the kernel. The right side is the
  finite-fiber algebraic integral over `I \ N` of the quotient simple function
  `[n] ↦ [(E f)(n)]`.

The intertwining law at `l : L` is checked on an element `z` of the kernel
coinvariants. After the goal is unfolded to the descended integral,
`Jacquet.complexCharacter_apply` and `splitKernelHaarRatio_apply` turn `χ(l)` into
`c_l`. The goal is then exactly `splitKernelCompactCoinvariantDesc_section`:

```text
Desc ((compactInduced H σ).toCoinvariants N (s l) z) = c_l • D(l) (Desc z),
```

with `Desc` the descended integral and `D = splitKernelCoefficientAction r s H
hsH σ`.

## Naturality

`splitKernelCompactEquivariantEquiv_natural` holds for every smooth
representation `τ : Representation ℂ H W` (`hτ : IsSmooth τ`) on a complex
module `W` in an independent universe, every intertwiner
`T : σ.IntertwiningMap τ`, and every `z` in the kernel coinvariants of
`compactInduced H σ`:

```text
Φ_τ (Coinvariants.map _ _ (Jacquet.restrictMap (compactInducedMap H T) N) z)
  = Coinvariants.map σI τI (splitKernelInducingMap r H T) (Φ_σ z).
```

Here `Φ_σ` and `Φ_τ` are the equivariant equivalences for `σ` and `τ`, and
`τI = τ.comp (N.subtype.subgroupComap H)`. On the source, the map is
`Coinvariants.map` of the restriction to `N` of the actual compact-induction
functor map `compactInducedMap H T`. On the target, it is `Coinvariants.map`
of the inducing coefficient map `splitKernelInducingMap r H T`, which is `T` on
vectors. Both equivalences apply their underlying linear equivalences, so the
proof is the published `splitKernelCompactCoinvariantEquiv_natural`.

## Scope

This pair proves equivariance and naturality only. It does not prove
smoothness of the twisted coefficient action, compact induction in stages, an
outer normal-coinvariant comparison, an identification of `c_l` with other
moduli, or `PadicParabolicOrbitJacquetComparison`. It imports
`Langlands.Representation.Induction.SplitKernelCovariance` by its published
module name. The axioms are `propext`, `Classical.choice` and `Quot.sound`.
