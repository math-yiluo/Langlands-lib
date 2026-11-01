# Unipotent slices of matrix test functions are Schwartz–Bruhat

Module `Langlands.Representation.GodementJacquet.WhittakerSliceSchwartz`,
namespace `Langlands.GodementJacquet.WhittakerSlice`.

Let `F` be a p-adic field (a `PadicField`), with its canonical topology,
valuative relation and local-field structure as local instances. Let `ψ` be a
nontrivial unitary additive character, `N` the upper unipotent subgroup of
`GL_{n+1}(F)` with any Borel measurable structure and its normalized Haar
measure `unipotentHaar F.Carrier n`, and `ψ_N = standardCharacter ψ n` the
standard character of `N`. For a function `f` on all square matrices
`M_{n+1}(F)` the module defines the slice integral

`J_f(x) = ∫_N f(u · diag(x)) ψ_N(u) du`,  for `x ∈ F^{n+1}`,

and proves that `J_f` is Schwartz–Bruhat (locally constant with compact
support) whenever `f` is. The main use is `f = Φ(· k)` for a matrix test
function `Φ` and `k ∈ GL_{n+1}(F)`.

## Source and provenance

The statement is internal and derived. It serves the reduction of the
rationality statement `ModelWhittakerRationalityStatement` (convergence and
rationality of every full-matrix Whittaker integral on the coefficient model).
That statement is the input of JPSS, *Rankin–Selberg convolutions*, Amer. J.
Math. 105 (1983), Section (5.2), citing Jacquet, Piatetski-Shapiro and Shalika,
*Automorphic forms on GL(3)*, Ann. of Math. 109 (1979). In the Iwasawa
decomposition `g = u · diag(a) · k` of a full-matrix Whittaker integral, the
integral over `N` produces exactly `J_{Φ(·k)}(a)`. The reduction needs this to
be a Schwartz–Bruhat function of the diagonal entries, including entries equal
to `0`. The proof below is not taken from the sources: it is a direct
elementary argument using right translation by elementary unipotent matrices.

## Declarations

### Generic topology

- `exists_nhds_add_invariant`: in a topological additive group, a compactly
  supported locally constant `f` admits one neighbourhood `U` of `0` with
  `f (x + h) = f x` for all `x` and all `h ∈ U`. Proof: the set of pairs
  `(h, x)` with `f (x + h) = f x` is open and contains `{0} × tsupport f`, so
  the generalized tube lemma gives `U` working on the support. Intersect with
  `-U`. If `x + h` lies in the support, apply the claim to `x + h` and `-h`.
  If neither `x` nor `x + h` lies in the support, both values are `0`.
- `pi_eventually_small`: smallness predicates in `𝓝[>] 0` on each coordinate
  of a finite product give one on the product.

### The normalized absolute value

`nabs F` abbreviates `F.canonicalTopologicalData.normalizedAbs`. The lemmas
`nabs_nonneg`, `nabs_mul`, `nabs_add_le_max` (ultrametric inequality),
`nabs_neg`, `nabs_zero`, `nabs_one`, `nabs_pos` and `continuous_nabs` restate
Library facts. `eventually_small_scalar` says that for small enough `r > 0`,
every `z` with `nabs z < r` lies in a given neighbourhood of `0`. This uses
the ball basis `normalizedAbs_balls_basis`. `exists_small_matrix` is the
matrix version: every neighbourhood of `0` in `M_ι(F)`, `ι` finite, contains
all matrices whose entries have `nabs < r` for some `r > 0`.

### Uniform estimates for a test function

- `exists_uniform_constancy`: a compactly supported locally constant `f` on
  square matrices has `r > 0` with `f (M + δ) = f M` whenever every entry of
  `δ` has `nabs < r`.
- `eq_of_small_diff`: under that property, `f A' = f A` as soon as all entries
  of `A' - A` have `nabs < r` in the case where `f A ≠ 0` or `f A' ≠ 0`.
- `exists_support_bound`: there is `R` with `nabs (M a b) ≤ R` for every entry
  of every `M` with `f M ≠ 0`. This is the bound of the continuous function
  `M ↦ ∑ nabs (M a b)` on the compact support.

### Unipotent matrices

- `column_bound`: for `u ∈ N`, a column index `b`, `t > 0` and `y` with
  `b = 0` or `t ≤ nabs y`, if `nabs (u a b · y) ≤ R` for all `a`, then
  `nabs (u a b) ≤ max 1 (R / t)` for all `a`. Entries below the diagonal are
  `0` and diagonal entries are `1`. Above the diagonal, `b ≠ 0`, and the
  bound follows by dividing by `nabs y ≥ t`.
- `adjacentTransvection i c` is the element `1 + c E_{i,i+1}` of `N`, built
  from the Library's `transvectionUnit`. Right multiplication by it adds `c`
  times column `i` to column `i+1` (`mul_adjacentTransvection_val`). The
  standard character takes the value `ψ(c)` on it
  (`standardCharacter_adjacentTransvection`).

### Vanishing

- `threshold r R a` is the sequence `θ 0 = 1`,
  `θ (k+1) = r / (a · max 1 (R / θ k))`; it is positive when `r, a > 0`
  (`threshold_pos`).
- `sliceIntegral F ψ f x` is `J_f(x)` above.
- `sliceIntegral_eq_zero_of_invariant`: if
  `f ((u · (1 + c E_{i,i+1})) · diag(x)) = f (u · diag(x))` for all `u` and
  `ψ(c) ≠ 1`, then `J_f(x) = 0`. Proof: right invariance of the Haar measure
  of `N` (`integral_mul_right_eq_self`) gives `J_f(x) = J_f(x) · ψ(c)`.
- `sliceIntegral_eq_zero_step`: fix `r`, `R` as in the uniform estimates and
  `c ≠ 0` with `ψ(c) ≠ 1`. If `i = 0` or `t ≤ nabs (x_i)`, and
  `nabs (x_{i+1}) < r / (nabs c · max 1 (R / t))`, then `J_f(x) = 0`. Proof:
  the translate by `1 + c E_{i,i+1}` changes only column `i+1` of
  `u · diag(x)`, by `c · u_{a,i} · x_{i+1}`. When either value of `f` is
  nonzero, column `i` of `u · diag(x)` is bounded by `R`, so `column_bound`
  bounds `u_{a,i}`. The change is then below `r`, so `eq_of_small_diff` gives
  invariance, and the previous lemma applies.
- `sliceIntegral_eq_zero_of_lt_threshold`: for `b ≠ 0`, if
  `nabs (x_b) < θ b` (thresholds with `a = nabs c`) then `J_f(x) = 0`. Proof
  by induction on `b`: if `nabs (x_{b-1}) < θ (b-1)` with `b - 1 ≠ 0`, use the
  induction hypothesis. Otherwise apply the step with `t = θ (b-1)`, or with
  `i = 0` and `t = 1` when `b = 1`.

### Schwartz–Bruhat property

- `exists_character_ne_one`: `ψ` takes a value `≠ 1` at some `c ≠ 0`
  (from nontriviality of `ψ`).
- `sliceIntegral_isLocallyConstant`: `J_f` is locally constant for compactly
  supported locally constant `f`. Fix `x`. If some `b ≠ 0` has
  `nabs (x_b) < θ b`, this persists on a neighbourhood (continuity of `nabs`)
  and `J_f` vanishes there. Otherwise every `b` has `b = 0` or
  `θ b ≤ nabs (x_b)`. Take `x'` with `nabs (x'_b - x_b) < ρ b` for all `b`,
  where `ρ b = min (θ b) (r / max 1 (R / θ b))`. By the ultrametric
  inequality `x'` satisfies the same lower bounds. The entries of
  `u · diag(x') - u · diag(x)` are `u_{a,b} (x'_b - x_b)`. Whenever one of
  `f (u · diag(x))`, `f (u · diag(x'))` is nonzero, `column_bound` with
  `t = θ b` bounds `nabs (u_{a,b})` by `max 1 (R / θ b)`, so these entries
  have `nabs < r`. Then the integrands agree pointwise by `eq_of_small_diff`,
  so `J_f(x') = J_f(x)`.
- `sliceIntegral_hasCompactSupport`: since `(u · diag(x))_{jj} = x_j` for
  `u ∈ N`, `J_f(x) = 0` unless each `x_j` lies in the compact image of
  `tsupport f` under `M ↦ M_{jj}`. The product of these images is compact.
  This uses that `F` is Hausdorff (`localField_t2`).
- `sliceIntegral_mem`: for `f` in `schwartzBruhatSubmodule` of
  `M_{n+1}(F)`, `J_f` lies in `schwartzBruhatSubmodule (Fin (n+1) → F)`.
- `rightMulHomeomorph k`: `M ↦ M · k` as a homeomorphism of `M_{n+1}(F)` for
  `k ∈ GL_{n+1}(F)`, with inverse `M ↦ M · k⁻¹`.
- `sliceIntegral_rightTranslate_mem`: for a matrix test function `Φ` and
  `k ∈ GL_{n+1}(F)`, the function `x ↦ ∫_N Φ(u · diag(x) · k) ψ_N(u) du` is
  Schwartz–Bruhat on `F^{n+1}`. The translate is locally constant by
  composition with a continuous map, and compactly supported by
  `HasCompactSupport.comp_homeomorph`.

No measurability or integrability hypotheses are needed: if the integrand is
not integrable, the Bochner integral is `0` and the vanishing and congruence
arguments still apply, because they only rewrite the integrand pointwise or
use right invariance of the measure.
