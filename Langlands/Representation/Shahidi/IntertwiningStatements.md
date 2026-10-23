# Convergence and rational continuation of Shahidi's intertwining operator

This module states, as proposition definitions, the two analytic assertions
that F. Shahidi, *Fourier transforms of intertwining operators and Plancherel
measures for GL(n)*, American Journal of Mathematics 106 (1984), 67–111,
makes on printed page 72 about the operator

\[
A(s,\pi,w_{m,n})f(g)=\int_{U'} f(w_{m,n}u'g)\,du' \qquad (0.1)
\]

for irreducible admissible `π₁` of `GL_m(F)` and `π₂` of `GL_n(F)`:

1. the integral converges for `Re(s) ≫ 0` (the source cites its references
   [15, 19, 22] and gives no proof);
2. "as a function of `s`, it has a meromorphic continuation to a rational
   function of `q^{-s}` on `ℂ`".

Neither assertion is proved or assumed here. The two `Prop` definitions are
targets for later proof units; nothing in the Library uses them as hypotheses.

The registered original is `shahidi-1984-fourier`, SHA256
`a10d5c605d94d4e85d0e5f453d6a8c233d91e3cb60d538f430d8ad900cbb6b29`.
The author is Worker 11.

The unit builds on these published modules:

- `IntertwiningPadic`: the p-adic operator `shahidiIntertwining`, its
  convergence domain `shahidiSourceDomain`, and `shahidiIntertwining_eval`;
- `IntertwiningInduced`: `pairRepresentation` (the representation `π₁ ⊗ π₂`
  of `GL_m(F) × GL_n(F)` on the source values), `pairFlip` and
  `IsModulusScaling`;
- `Induction`: the p-adic `ShahidiSourceSpace` and `shahidiSourceEval`
  (the space `I(s, π₁ ⊗ π₂)` and evaluation of its elements), and
  `T.shahidiAbsoluteValue`;
- `Geometry`: `blockWeyl m n` (Shahidi's `w_{m,n}`) and
  `intertwiningUnipotent m n a`, the element `u'(a)` of `U'` for an `n` by
  `m` matrix `a`. It is the exchanged upper radical matrix
  `[[I_n, a], [0, I_m]]`, with `a` in the upper-right `n` by `m` block,
  transported to total rank `m+n`. This agrees with the source (p.71–72):
  `U` is the upper `(m,n)` radical, `V` its long-Weyl conjugate and `U'` the
  transpose of `V`. The Library's separate lower matrix
  `[[I_m, 0], [a, I_n]]` is `w_{m,n} u'(a) w_{m,n}^{-1}` (`Geometry.lower`)
  and is not used here;
- the Library's `GeneralLinearGroup.integralSubgroup`, `rectangularMeasure`,
  `AdditiveHaarMeasure`, `IsAdmissible`, `SmoothDual`, and
  `HasRationalContinuation` with `T.residueCardinality`.

All declarations lie in `Langlands.PadicField.TopologicalData`, for
`F : PadicField p` and a supplied realization `T : F.TopologicalData`, with
`0 < m` and `0 < n`.

## Definitions

- `shahidiMaximalCompact r` is `K_r = GL_r(O_F)`: the matrices in `GL_r(F)`
  whose entries and whose inverse's entries lie in `T.Integers`, the
  valuation ring of the specified valuation. It is the published
  `GeneralLinearGroup.integralSubgroup (Fin r) T.Integers`.
- `IsShahidiFlatFamily hm hn π₁ π₂ f`: a family `s ↦ f_s ∈ I(s, π₁ ⊗ π₂)`,
  given for every complex `s`, is *flat* when the restriction of `f_s` to
  `K_{m+n}` does not depend on `s`. Since `G = P K` with `P` the `(m,n)`
  parabolic, such a family is the same as one function on `K_{m+n}`,
  extended to each `I(s, π₁ ⊗ π₂)` by the left transformation law. This is
  the standard "compact picture" meaning of a function of `s` in the
  induced spaces; the source does not say which families it varies, and this
  is the reading used here (internal interpretation).
- `shahidiIntertwiningCoefficient hm hn π₁ π₂ μ f g ℓ s` is the complex number
  `∫ ℓ(f_s(w_{m,n} u'(a) g)) dμ(a)`, for a measure `μ` on the `n` by `m`
  matrices over `F`, a point `g ∈ GL_{m+n}(F)` and a smooth functional `ℓ` of
  `π₁ ⊗ π₂`. It is an ordinary Bochner integral, so it is defined for every
  `s`, and it is the quantity whose dependence on `s` the rationality
  statement describes.
- `shahidiIntertwiningCoefficient_eq` (theorem): when `μ` is invariant under
  left translation and satisfies `IsModulusScaling`, and `f_s` lies in the
  convergence domain `shahidiSourceDomain`, the coefficient equals
  `ℓ(flip⁻¹ (A(s, π, w_{m,n}) f_s(g)))`. Here `flip : V₁ ⊗ V₂ ≃ V₂ ⊗ V₁` is
  the published `pairFlip`, which `IntertwiningInduced` uses to read the
  values of `A f` in the target `I(-s, π₂ ⊗ π₁)`. The proof is the published
  `shahidiIntertwining_eval`.

## The convergence statement

`ShahidiIntertwiningConvergenceStatement hm hn` says: for every additive Haar
measure `ν` on `F` (Borel for the topology of `T`), and all complex
representations `π₁` of `GL_m(F)` and `π₂` of `GL_n(F)` that are admissible
and irreducible, there is a real `a` such that for every `s` with
`Re s > a`, the convergence domain of (0.1) for the measure
`rectangularMeasure ν n m` is all of `I(s, π₁ ⊗ π₂)`.

- *Irreducible admissible.* Admissible is the Library's `IsAdmissible`, which
  includes smoothness. Irreducible is `IsSimpleModule` over the group algebra
  `MonoidAlgebra ℂ (GL_k(F))`, that is, algebraic irreducibility, as for the
  representations in the source.
- *Convergence.* The domain `shahidiSourceDomain` consists of the `f` for
  which, at every `g`, the integral of `a ↦ f(w_{m,n} u'(a) g)` exists as a
  weak integral tested by the smooth dual of `π₁ ⊗ π₂`: every smooth `ℓ`
  gives a Lebesgue-integrable function `a ↦ ℓ(f(w_{m,n} u'(a) g))`, and some
  vector `v` has `ℓ(v)` equal to its integral for all `ℓ`. So the statement
  asks for absolute convergence of each scalar integral and for a vector
  value.
- *Measure.* `du'` is the product measure `rectangularMeasure ν n m` on the
  coordinates of `u'`, for an arbitrary additive Haar measure `ν`. The source
  fixes no normalization at this point. A positive rescaling of `ν` does not
  change the convergence domain.
- *Smooth versus `K_r`-finite.* The source defines `I(s, π)` with
  `K_r`-finite functions. The Library's `ShahidiSourceSpace` uses smooth
  functions, the standard reading of the source's space over a p-adic field
  (smooth functions are `K_r`-finite). This identification is not proved in
  the Library, and this unit does not use it.

## The rationality statement

`ShahidiIntertwiningRationalityStatement hm hn` says: for every `ν`, `π₁`,
`π₂` as above and every flat family `f`,

- there is a real `a` such that `f_s` lies in the convergence domain for
  `Re s > a`; and
- for every `k ∈ K_{m+n}` and every smooth functional `ℓ` of `π₁ ⊗ π₂`, there
  is a rational function `R ∈ ℂ(X)` with
  `HasRationalContinuation q (s ↦ shahidiIntertwiningCoefficient … f k ℓ s) R`,
  where `q = T.residueCardinality` is the cardinality of the residue field.

The published `HasRationalContinuation q φ R` means: for some real `b` and all
`s` with `Re s > b`, the denominator of `R` does not vanish at `q^{-s}` and
`φ(s) = R(q^{-s})`. With the first conjunct and
`shahidiIntertwiningCoefficient_eq`, this says that
`s ↦ ℓ(flip⁻¹ (A(s, π, w_{m,n}) f_s(k)))` agrees with `R(q^{-s})` on a right
half-plane where the integral converges. Since `R(q^{-s})` is meromorphic in
`s` on `ℂ`, this is the source's "meromorphic continuation to a rational
function of `q^{-s}`", read pointwise and weakly. By the published
`HasRationalContinuation.unique`, `R` is determined by `f`, `k` and `ℓ`.

Two choices narrow the source's sentence; both are internal interpretations.

- *Points of `K_{m+n}`.* Rationality is stated at `k ∈ K_{m+n}` only. The
  target `I(-s, π₂ ⊗ π₁)` is induced from the swapped `(n,m)` parabolic. Write
  its elements as `p = diag(h₂, h₁) u`, where `h₂ ∈ GL_n(F)` is the first,
  `n` by `n` block (acting through `π₂`) and `h₁ ∈ GL_m(F)` is the second,
  `m` by `m` block (acting through `π₁`); so `h₁` and `h₂` keep the labels of
  the original factors. In the normalized induction the target carries
  `|det h₂|^{(m-s)/2}` on the first block and `|det h₁|^{(s-n)/2}` on the
  second (the published target covariance of `IntertwiningPadic`). For
  `g = p k`, `A f_s(g)` is `A f_s(k)` times a factor that contains
  `(|det h₁| / |det h₂|)^{s/2}`. When the valuation of
  `det h₁ / det h₂` is odd, this is an odd power of `q^{-s/2}`, so `A f_s(g)`
  is in general not a rational function of `q^{-s}`. At `k ∈ K_{m+n}`, the
  determinant of `w_{m,n} u' k` is a unit, so only integral powers of
  `q^{-s}` occur. By the Iwasawa decomposition and the target transformation
  law, the values on `K_{m+n}` determine `A f_s`; this is a remark, not a
  result of this unit.
- *Weakly, for each `k` and `ℓ`.* The rational function may depend on `k`
  and `ℓ`. No common denominator is claimed.

## What is not claimed

This unit does not claim the following:

- that either statement holds; both are open proof obligations;
- holomorphy or nonvanishing of the continued operator, or of any normalized
  operator;
- a common denominator for the rational functions over `k` and `ℓ`, or
  rationality as a vector-valued function;
- any Haar normalization of `du'`;
- the comparison of Shahidi's `K_r`-finite functions with the Library's
  smooth functions;
- the local coefficient relation (0.3), which later units of the parent task
  treat.
