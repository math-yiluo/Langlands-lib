# Analytic coefficients and local bounds for the actual Cartan covector form

This internal construction extends the published Cartan covector form of
`ArchimedeanCartanSymbol` from actual units to all ambient matrices and
makes its positivity quantitative near each unit. It holds for every
number field `K` in an arbitrary universe and every natural rank `n`,
including zero. Worker 94 developed the construction and its proofs.
Worker 815 added the global analyticity form, the corollary for the
published form and the two norm checks, and prepared the pair for
submission.

## Carriers and norms

Everything lives on the published `ArchimedeanMatrix K n`, which consists of
matrices over the actual mixed real/complex space. That type keeps its
published `L∞` operator norm, the maximum row sum of entry norms, from
`Matrix.Norms.Operator`. Covectors are continuous real linear maps
`ArchimedeanMatrix K n →L[ℝ] ℝ`, with the induced continuous-linear-map
operator norm. Two closing `example`s check this. The first is
`ContinuousLinearMap.norm_def` for the covector norm. The second is
`Matrix.linfty_opNorm_def` for the matrix norm. No new norm, topology or
instance is introduced.

## Definitions and elementary properties

`ambientCartanCovectorForm K n y ℓ` is defined for every ambient matrix `y`
(units and nonunits alike) and every continuous covector `ℓ`. It is the
finite sum, over the whole `CartanBasisIndex K n`, of
`(ℓ (y * realLieAlgebraToMatrix K n (cartanAdaptedBasis K n i)))²`.
The basis is the published normalized complete Cartan basis.

- `ambientCartanCovectorForm_unit`: at an actual unit `g`, the expression
  equals `cartanCovectorForm K n g ℓ.toLinearMap`. This is the published
  algebraic-dual form, evaluated on the underlying linear map of `ℓ`.
  Both sides are the same sum of squares by `cartanCovectorForm_apply`.
- `ambientCartanCovectorForm_nonneg`: nonnegativity, term by term.
- `ambientCartanCovectorForm_zero`: the zero covector gives zero.
- `ambientCartanCovectorForm_smul`: real degree-two homogeneity in the
  covector, `Q(y, c • ℓ) = c² * Q(y, ℓ)`.
- `continuous_ambientCartanCovectorForm`: joint continuity in `(y, ℓ)` for
  the product of the matrix-norm and dual-operator-norm topologies. Each
  summand comes from continuous right multiplication by a fixed matrix,
  jointly continuous evaluation `Continuous.clm_apply` and squaring. A
  finite sum of such terms is continuous.
- `analyticAt_ambientCartanCovectorForm` and
  `analyticOnNhd_ambientCartanCovectorForm`: for each fixed continuous
  covector, the map `z ↦ Q(z, ℓ)` is real analytic at every matrix. The
  proof derives this. Each inner map `z ↦ ℓ (z * Xᵢ)` is the continuous
  linear map `ℓ ∘ (right multiplication by Xᵢ)`, built from Mathlib's
  bounded multiplication `ContinuousLinearMap.mul`, so it is analytic.
  Squares and finite sums of analytic functions are analytic. No
  analyticity certificate or extra regularity hypothesis is supplied.
- `ambientCartanCovectorForm_unit_pos`: at a unit, the value on a nonzero
  continuous covector is strictly positive. If the underlying linear map
  were zero, the covector would be zero. The published
  `cartanCovectorForm_pos` then applies.

## Local coercive bound

`ambientCartanCovectorForm_local_bound` takes an actual unit `g`. It gives
a real `c > 0` and an open set `U` of ambient matrices that contains `g`
and is contained in the range of the coercion from the actual units
`ArchimedeanGL K n`. These satisfy `c * ‖ℓ‖² ≤ Q(y, ℓ)` for every `y ∈ U`
and every continuous covector `ℓ`. Both `c` and `U` are chosen before
`ℓ`.

The implemented argument runs as follows.

1. The continuous dual is finite dimensional over `ℝ`, so it is a proper
   space. Its unit sphere `S` is therefore compact (`isCompact_sphere`).
2. At `g`, `ℓ ↦ Q(g, ℓ)` is continuous and positive on `S`.
   `IsCompact.exists_forall_le'` gives `b > 0` with `b ≤ Q(g, ℓ)` on `S`.
   When `S` is empty, the same lemma just returns some `b > 0`, so no
   nonempty sphere or positive rank is assumed.
3. Every `ℓ ∈ S` satisfies `b / 2 < Q(g, ℓ)`. Joint continuity makes this
   inequality hold on a neighborhood of `(g, ℓ)`.
   `IsCompact.eventually_forall_of_forall_eventually` then gives one
   neighborhood of `g` on which `b / 2 < Q(y, ℓ)` for all `ℓ ∈ S` at once.
4. That neighborhood is intersected with the range of the unit
   coercion, which is open because `Units.val` is an open embedding. An
   open subset `U` of the intersection containing `g` is extracted, and
   `c = b / 2` is set.
5. For `y ∈ U`, the zero covector is immediate because both sides vanish.
   A nonzero `ℓ` equals `‖ℓ‖ • normalize ℓ`, where `normalize ℓ` lies in
   `S`. Homogeneity gives `Q(y, ℓ) = ‖ℓ‖² * Q(y, normalize ℓ)`, and
   `Q(y, normalize ℓ) ≥ b / 2`.

`cartanCovectorForm_local_bound` restates the same `c` and `U` for the
published form. For every actual unit `h` with `↑h ∈ U` and every
continuous covector `ℓ`, it gives
`c * ‖ℓ‖² ≤ cartanCovectorForm K n h ℓ.toLinearMap`. The proof is the
restriction identity.

No power bounds are included. In particular, the pair compares no
powers of this scalar form with principal symbols of powers or
compositions of differential operators.

## Provenance and scope

This is an internal, derived finite-dimensional analysis consequence of
the published complete Cartan frame form. It uses Mathlib's compactness,
analyticity of continuous linear maps and finite polynomial operations,
and has no external theorem attribution. It constructs analytic scalar
coefficient expressions and local norm bounds only. It does not assert
any of the following:

- a composition theorem for polynomial differential operators;
- analytic elliptic regularity or analyticity of smooth solutions;
- density, compact admissibility, reproducing-kernel or reproduction
  statements;
- final automorphic derivative growth.

These remain separate obligations.
