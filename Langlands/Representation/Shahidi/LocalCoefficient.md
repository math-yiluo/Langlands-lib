# The local-coefficient relation on functions, and its uniqueness

This module states equation (0.3) of F. Shahidi, *Fourier transforms of
intertwining operators and Plancherel measures for GL(n)*, American Journal
of Mathematics 106 (1984), 67–111, printed pages 72–73:

\[
\lambda^{-s}_{\pi'}\bigl(A(s,\pi,w_{m,n})f\bigr)=C_\chi(s,\pi)^{-1}\,\lambda^s_\pi(f).
\]

The registered original is `shahidi-1984-fourier`, SHA256
`a10d5c605d94d4e85d0e5f453d6a8c233d91e3cb60d538f430d8ad900cbb6b29`.
The author is Worker 11. The module combines two Library units:

- the intertwining integral (0.1), `HasIntertwiningIntegral` of
  `Langlands.Representation.Shahidi.IntertwiningIntegral`;
- the Jacquet integrals of `Langlands.Representation.Shahidi.JacquetIntegral`.
  `HasJacquetIntegral` is the stabilized integral (0.2), and
  `HasSwappedJacquetIntegral` is the stabilized integral defining
  `λ^{-s}_{π'}` below (0.3).

The rational-function layer uses `spectralPoint q s = q^(-s)` and
`rationalFunction_eq_of_infinite_eval_eq` from
`Langlands.Representation.RankinSelberg.RationalContinuation`.

## Setting

In the source, `π₁` and `π₂` are non-degenerate representations of `GL_m(F)`
and `GL_n(F)`, and `π = π₁ ⊗ π₂`. Two `χ`-Whittaker functionals `λ₁` and
`λ₂` are fixed. The function `f` lies in the induced space `I(s,π)`, and
`A(s,π,w_(m,n)) f` lies in `I(-s,π')` with `π' = π₂ ⊗ π₁`. The source
deduces from its reference [19] that there exists a complex number
`C_χ(s,π)` satisfying (0.3) for all `f ∈ I(s,π)`. On page 73 it remarks that
`C_χ(s,π)` depends on the measures defining `A(s,π,w_(m,n))`, `λ^s_π` and
`λ^{-s}_{π'}`.

This unit does not construct `I(s,π)`. Like its two imported units, it works
with actual functions `f : GL_(m+1+n+1)(F) → V`. Here `V` is an arbitrary
complex vector space carrying an arbitrary representation `ρ` of an
arbitrary topological group `H`. The two block ranks are written `m+1` and
`n+1` so that both are positive, as in `JacquetIntegral`. The data are:

- `ψ`, the unitary additive character defining the Whittaker character
  `χ` of the Jacquet integrals;
- `ℓ`, a complex linear functional on `V` used in (0.2), the stand-in for
  `λ₁ ⊗ λ₂`;
- `ℓ'`, a complex linear functional on `V` used in the swapped integral, the
  stand-in for `λ₂ ⊗ λ₁`;
- `μ`, a measure on `(n+1)` by `(m+1)` matrices, the measure `du'` of (0.1);
- `μJ`, a measure on the same matrices, the measure `du'` of (0.2);
- `μJ'`, a measure on `(m+1)` by `(n+1)` matrices, the measure `du` of the
  swapped integral.

The three measures are separate arguments, as the page-73 remark requires.
No Haar property and no normalization is assumed. As in `JacquetIntegral`,
the field `F` carries a topology making it a topological ring and a
measurable structure.

`ℓ'` is a separate argument because `A f` takes values in the same space `V`
as `f` at this level. In the intended specialization to induced spaces, `A f` is read
in `V₂ ⊗ V₁` through the tensor swap. Then `ℓ'` is `λ₂ ⊗ λ₁` composed with
that swap. On pure tensors this is `v₁ ⊗ v₂ ↦ λ₂(v₂) λ₁(v₁)`, so it agrees
with `ℓ = λ₁ ⊗ λ₂`. The unit allows any `ℓ'`.

## The relations

`SatisfiesLocalCoefficientEquation m n ψ ρ ℓ ℓ' μ μJ μJ' f c` means that
`c ≠ 0` and that there are a function `A` and complex numbers `z` and `z'`
such that

- `A` is the intertwining integral of `f` against `μ`
  (`HasIntertwiningIntegral (m+1) (n+1) ρ μ f A`);
- the Jacquet integral of `f` against `μJ` with functional `ℓ` stabilizes to
  `z` (`HasJacquetIntegral m n ψ ℓ μJ f z`);
- the swapped Jacquet integral of `A` against `μJ'` with functional `ℓ'`
  stabilizes to `z'` (`HasSwappedJacquetIntegral m n ψ ℓ' μJ' A z'`);
- `z' = c⁻¹ z`.

This is (0.3) for one function `f` and one number `c`, with Shahidi's inverse
convention: `c` is `C_χ(s,π)`, and its inverse multiplies `λ^s_π(f)`.

The condition `c ≠ 0` makes `c⁻¹` a genuine reciprocal. Lean's inverse is
total, with `0⁻¹ = 0`. Without the condition, `c = 0` would satisfy the
equation whenever `z' = 0`, even if `z ≠ 0`. The source equation has no
finite coefficient in that situation. With the condition, `z ≠ 0` forces
`z' ≠ 0`.

`satisfiesLocalCoefficientEquation_iff_mul` restates the relation without
inverses: `c ≠ 0`, and the same data satisfy `c z' = z`. The equivalence is
`eq_inv_mul_iff_mul_eq₀`. `SatisfiesLocalCoefficientEquation.ne_zero`
extracts `c ≠ 0`.

`IsLocalCoefficientAt m n ψ ρ ℓ ℓ' μ μJ μJ' S c` means that every function in
the set `S` satisfies the equation with the same `c`. With `S` the functions
of `I(s,π)`, this is the source's "for all `f ∈ I(s,π)`".

`IsLocalCoefficient m n ψ ρ ℓ ℓ' μ μJ μJ' q S C` takes a natural number `q`, a
family `S : ℂ → Set (GL_(m+1+n+1)(F) → V)` and a rational function
`C : RatFunc ℂ`. It means that there is a real number `a` such that for every
`s` with `a < Re s`:

1. the denominator of `C` does not vanish at `q^(-s)`;
2. some `f ∈ S s` has a Jacquet integral `z` with `z ≠ 0`;
3. `IsLocalCoefficientAt … (S s) c` holds with `c` the value of `C` at
   `q^(-s)`. In particular this value is nonzero.

So `C` is the local coefficient of the family, as a rational function of
`q^(-s)`, on a right half-plane. The functionals and measures do not depend
on `s`, as in the source, where `λ₁ ⊗ λ₂` and the measures are fixed once.

Condition 1 makes the value of `C` an actual value, not Lean's value `0` at a
pole. It does not restrict `C`. The denominator has finitely many roots. A
nonzero root `x` corresponds to the vertical line
`Re s = -log |x| / log q` (for `q > 1`), and `q^(-s)` is never `0`. So every
rational function has nonvanishing denominator at `q^(-s)` on some right
half-plane.

Condition 2 places nonvanishing of the Jacquet functional inside the
relation. Without it, if every Jacquet integral on `S s` were `0`, every
nonzero `C` would satisfy (0.3) with `z = z' = 0`. The Library's JPSS gamma
relations also keep their nonzero witnesses inside the relation. Condition 2
also makes `S s` nonempty, so condition 3 does force `C(q^(-s)) ≠ 0`.

Conditions 1 and 2 alone would not give the source reciprocal. The zero
rational function has denominator `1`, so it passes condition 1. Condition 2
concerns `λ^s_π`, not `λ^{-s}_{π'}`. The nonvanishing of the value comes from
condition 3, through `c ≠ 0`. Two consequences are proved:

- `IsLocalCoefficient.reciprocal`: on a right half-plane, the numerator of
  `C` does not vanish at `q^(-s)`, the denominator of the rational function
  `C⁻¹` does not vanish there, and the value of `C⁻¹` at `q^(-s)` is the
  inverse of the value of `C`. So `C` has neither zeros nor poles on the
  half-plane, and (0.3) there reads `λ'(A f) = C⁻¹(q^(-s)) λ(f)`, with `C⁻¹`
  the reciprocal rational function. The proof: the value of `C` is nonzero,
  so `C ≠ 0` and its numerator does not vanish. The denominator of `C⁻¹`
  divides the numerator of `C` (`RatFunc.denom_inv_dvd`), so it does not
  vanish either. Then `RatFunc.eval_mul` applied to `C * C⁻¹ = 1` gives the
  values.
- `IsLocalCoefficient.ne_zero`: `C` is not the zero rational function, since
  the numerator of `0` is `0`.

These two results need no hypothesis on `H` or `ρ`.

## Uniqueness

Uniqueness assumes that `H` is a topological group, `ρ` is smooth, and every
open subgroup of `H` contains a compact open subgroup (`hcofinal`). These are
the hypotheses of the published `HasIntertwiningIntegral.unique`.

- `SatisfiesLocalCoefficientEquation.unique`: if the Jacquet integral of `f`
  is a nonzero `z`, then two numbers `c` and `c'` satisfying the equation for
  `f` are equal. The proof uses uniqueness of the intertwining integral and of
  the two stabilized integrals. This gives `c⁻¹ z = c'⁻¹ z`. Cancelling `z`
  and inverting gives `c = c'`. The proof does not use `c ≠ 0`.
- `IsLocalCoefficientAt.unique`: if some `f ∈ S` has a nonzero Jacquet
  integral, then `S` has at most one local coefficient. This is the previous
  result for that `f`.
- `IsLocalCoefficient.unique`: if `q > 1`, then the rational function is
  unique. Take the larger of the two half-plane bounds. On real `s` beyond it,
  condition 2 and the previous result give equal values of the two rational
  functions at `q^(-s)`. The points `q^(-s)` for real `s` in an interval
  `(b, ∞)` are pairwise distinct (`spectralPoint_ofReal_injective`), so they
  form an infinite set. Both denominators are nonzero there by condition 1.
  `rationalFunction_eq_of_infinite_eval_eq` then gives equality of the
  rational functions.

## Rescaling the functionals

Each `χ`-Whittaker functional of an irreducible generic representation is
unique up to a scalar. Replacing `λ₁` by `a λ₁` multiplies both `λ₁ ⊗ λ₂`
and `λ₂ ⊗ λ₁` by `a`, and similarly for `λ₂`. The following results show that
this does not change the local coefficient:

- `SatisfiesLocalCoefficientEquation.smul`: if the equation holds for `ℓ`
  and `ℓ'`, then it holds for `a • ℓ` and `a • ℓ'` with the same `c`, for
  every `a ∈ ℂ`. The stabilized integrals become `a z` and `a z'`, and
  `c ≠ 0` is unchanged.
- `satisfiesLocalCoefficientEquation_smul_iff`: for `a ≠ 0` the converse
  also holds.
- `IsLocalCoefficient.smul`: if `C` is the local coefficient for `ℓ` and
  `ℓ'`, then it is the local coefficient for `b • ℓ` and `b • ℓ'`, for
  `b ≠ 0`. The nonzero witness `z` becomes `b z`.

These results need no hypothesis on `H` or `ρ`.

## What is not claimed

This unit does not claim the following:

- that a local coefficient exists, for any data;
- that the intertwining or Jacquet integrals converge or stabilize on
  `I(s,π)`;
- that the Jacquet functional is nonzero on `I(s,π)`;
- that `C_χ(s,π)` is rational in `q^(-s)`;
- any normalization of the measures `μ`, `μJ` and `μJ'`;
- Theorem 5.1.

The specialization to `I(s,π)`, with `ℓ` and `ℓ'` built from actual Whittaker
functionals `λ₁` and `λ₂`, and the existence statement of the local
coefficient, are later units of this formalization.
