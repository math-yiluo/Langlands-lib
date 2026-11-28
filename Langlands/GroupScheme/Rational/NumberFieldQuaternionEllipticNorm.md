# Prescribed reduced norms and ellipticity at real places

Let `F` be a number field, `D` a central quaternion division algebra over `F` with an
orthogonal involution `σ` (`finrank F D = 4`, three-dimensional symmetric subspace), and `τ` the
canonical conjugation `σ.quaternionConjugation`, so that `d τ(d) = Nrd(d)`.

## Main results

- `Langlands.GroupScheme.Quaternionic.FirstKindInvolution.exists_mul_conjugation_eq_of_real`:
  suppose `a ∈ F` is a square at every real place where `F_v ⊗ D` is a division ring. More
  precisely, at a real place where `a` is not a square, a nonzero nonunit of `F_v ⊗ D` is
  required. Then `a = d τ(d)` for some `d ∈ D`.
- `exists_elliptic_mul_conjugation`: under the same hypothesis and `a ≠ 0`, there are
  `d ∈ D` and `s, c ∈ F` with `s ≠ 0`, `d τ(d) = a s²` and `(d - τ d)² = c`. At every real
  place where `a` is a square, `c` has negative real image. In that case `F_v(d)` is
  isomorphic to `ℂ`, so `d` is elliptic there.

## Proofs

**The norm.** The conjugate-product form `x ↦ ℓ(x τ x)` is the reduced norm, where `ℓ` is a
linear retraction of the scalars. Its scalar extension is the reduced norm of the extended
algebra (`conjugateProductQuadratic_baseChange`). It is anisotropic, hence nondegenerate, in
dimension four, so `numberFieldQuadraticRepresentation_of_archimedean` needs only archimedean
conditions.

- At a complex place, and at a real place where `a = s²`, the vector `s ⊗ 1` represents `a`.
- At a real place where `a` is not a square, a nonzero nonunit `y` has norm zero. Otherwise
  `y · τ(y) Nrd(y)⁻¹ = 1`, and `F_v ⊗ D` is Artinian, hence Dedekind-finite, so `y` would be a
  unit.
- The extended polar form is left-separating (`bilinForm_baseChange_separatingLeft`, by a dual
  basis). A form with such an isotropic vector represents every scalar
  (`quadraticForm_exists_eq_of_isotropic`).

**Ellipticity.** Replace `d₀` with `d₀ τ(d₀) = a` by `d = d₀ y²`. Then
`d τ(d) = a Nrd(y)²`, and the defect `c = Trd(d)² - 4 Nrd(d)` (`sub_conjugation_mul_self`)
equals `Trd(d₀ y²)² - 4 a Nrd(y)²`. Both `Trd(d₀ y²)` and `Nrd(y)` are quadratic forms in the
coordinates of `y` in a basis (`bilin_eq_sum_repr`), so the defect is a homogeneous polynomial
of degree four in these coordinates (for instance `-4t⁴` for `d₀ = i` in Hamilton's
quaternions and scalar `y = t`). The argument only uses that it is a polynomial, hence
continuous on each real completion.

At each real place `v` where `a` is a square, some pure `u ∈ {x, j, jx}` has positive norm
there (`exists_alternating_pos_norm_of_isReal`). Its norm is one of `-c₀`, `-δ₀`, `c₀ δ₀`, and
these cannot all be negative. On the real line `y = 1 + s u` the trace of `d₀ y²` is
`A + B s - k A s²`, with `A = Trd(d₀)` and `k = Nrd(u) > 0`, and `Nrd(y) = 1 + k s²`. A real
root `s` makes the trace vanish, so the defect becomes `-4 a (1 + k s²)² < 0`.

The defect is a continuous function of the real coordinates. Weak approximation at the real
places (`realCompletionVectorWeakApproximation`) gives a global `y` on which it is negative
at all these places. The same negativity shows `Nrd(y) ≠ 0` when such a place exists; when
none exists, `d = d₀` works.

The completion lemmas `realCompletion_isSquare_of_nonneg`,
`realCompletion_isSquare_or_isSquare_neg`, `realCompletion_eq_zero_of_mul_self_add_mul_self`
and `complexCompletion_isSquare` use the identifications of the real and complex completions
with `ℝ` and `ℂ`.

The norm step is the description of reduced norms in V. Platonov and A. Rapinchuk, *Algebraic
Groups and Number Theory* (1994), §6.7, equation (6.39), printed p. 357. At a real place where
the algebra is Hamilton's quaternions, the reduced norms of units are the positive scalars.
At every other place, every nonzero scalar is the reduced norm of a unit. The global proof here
uses the four-dimensional quadratic representation theorem to obtain the conclusion of
Eichler's norm theorem in this case. The approximation is
weak approximation in affine space at the real places, discussed in the paragraph after
Proposition 7.1 of the same book, printed p. 400.
