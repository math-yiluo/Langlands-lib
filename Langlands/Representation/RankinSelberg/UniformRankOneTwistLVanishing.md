# Godement–Jacquet L-vanishing from a ramified principal-level eigenvector

Module `Langlands.Representation.RankinSelberg.UniformRankOneTwistLVanishing`.

Authors: Worker 1836 (with Worker 1807, who proposed the same averaging argument
independently).

This module is internal support for the proof of
[UniformRankOneTwistStatement](UniformRankOneTwistStatement.md), the
level-uniform form of Jacquet–Shalika 1985, Proposition (2.2). It is a derived
argument, not a literal translation of a printed proof. It reuses the
compact-support Laurent computation of Godement–Jacquet, *Zeta Functions of Simple
Algebras* (1972), Section 5, printed pages 69–70, which the Library already
implements in [CompactMatrixLaurent](../GodementJacquet/CompactMatrixLaurent.md).
The point of the module is that the bound it needs depends only on the
principal level, so it yields level-uniform L-vanishing. All statements use the
canonical p-adic structures of a supplied `PadicField`.

## Main results

* `eq_one_of_normalizedMatrixFunctionalEquationData`. Let `ρ` be an
  irreducible smooth representation of `GL_(n+1)(F)` on an arbitrary carrier.
  Suppose some nonzero vector `w` satisfies `ρ k w = η(det k) • w` for every `k`
  in the principal congruence subgroup `K_m = 1 + ϖ^m M_(n+1)(O)`, `m > 0`, and
  `η : Fˣ →* ℂˣ` satisfies `η u ≠ 1` for some `u` in the principal units of
  level `m`. Then both polynomials `P` and `PDual` of any normalized matrix
  functional-equation data
  `GodementJacquet.Padic.NormalizedMatrixFunctionalEquationData F ψ ν ρ P PDual c a`
  equal `1`. No continuity of `η` is assumed.
* `isPadicSymmetricLPolynomial_one_of_eigenvector`. If moreover `ρ` (here
  called `τ`) has full Whittaker type for `ψ₀`, then
  `IsPadicSymmetricLPolynomial F ψ₀ ν₀ τ (rankOneCharacter 1) 1` holds for
  every self-dual Haar measure `ν₀`, that is, `L(s, τ × 1) = 1`.

## The averaging argument

The proof does not use Fubini. It replaces the integral over `K_m` by a finite
sum over cosets.

* `cosetSum H φ` sums a function over chosen representatives of the left
  cosets of a finite-index subgroup `H`. For a right `H`-invariant `φ`, the
  sum is invariant under left translation (`cosetSum_mul_left`); the proof
  reindexes by the permutation `MulAction.toPerm g₀` of the coset space.
* `averagedTest F K H η Φ` is the matrix test
  `X ↦ ∑_c η(det k_c) Φ(X k_c)`, a finite combination of the published right
  translates `rectangularTranslate`. `averagedTest_apply` evaluates it as a
  coset sum. `averagedTest_mul` proves
  `Φ♮(X) = η(det k₀) Φ♮(X k₀)` for `k₀ ∈ K`, provided `η ∘ det` is trivial on
  `H` and `Φ` is right `H`-invariant.
* `exists_principalLevel_fix_of_det_eq_zero`. Let `X` be singular, `m > 0`,
  and `u` a principal unit of level `m`. Take a kernel vector `z` of `X`, and
  normalize it to `x₀ = z_i⁻¹ z` at a coordinate `i` of maximal valuation, so
  that `x₀` is integral with `x₀ i = 1`. The rank-one perturbation
  `1 + (u - 1) x₀ e_iᵀ` lies in `K_m`. It is built with the published
  `exists_mem_principalLevelSubgroup`. Its determinant is `u`, by the matrix
  determinant lemma, and it fixes `X`.
* Together these give `averagedTest_eq_zero_of_fix` and
  `averagedTest_mem_regularMatrixTests`: the average vanishes at every
  singular matrix. By the published
  `hasCompactSupport_restrict_of_mem_regularMatrixTests`, its restriction to
  `GL_(n+1)(F)` has compact support.
* `matrixIntegral_averagedTest`. If `f (g k) = η(det k) f g` for `k ∈ K`, and
  all translates `rectangularTranslate k Φ`, `k ∈ K`, converge at `s`, then the
  integral against `Φ♮` is `[K : H]` times the integral against `Φ`. The
  proof uses the published norm-one translation lemma
  `matrixIntegral_translate_of_norm_one`. That lemma rests on right invariance
  of `generalLinearHaar` and on `|det k| = 1` for the compact group `K`.
* `exists_laurent_matrixIntegral_of_equivariant`. For continuous such `f`, `H`
  is taken to be a principal level `K_a ≤ K_m`. It is chosen inside the
  neighbourhood on which `Φ` is right invariant (`eventually_matrixTranslate_eq`)
  and inside an open subgroup on which `η ∘ det` is trivial. The quotient is
  finite (`Subgroup.quotient_finite_of_isOpen` on the compact group `K_m`). The
  published `exists_laurent_matrixIntegral_of_hasCompactSupport` applied to
  `Φ♮` then gives one Laurent polynomial. Dividing by the index gives the
  integral of `Φ` on every parameter where the translates converge.

## Passage to all coefficients

* `matrixIntegral_comp_mul_right` moves a right translation of the coefficient
  to the test, with the determinant weight `|det h⁻¹|^s`. Via
  `determinantWeight_shift_spectral` this weight is a Laurent monomial in
  `q^(-s)` (`LaurentOnRight.comp_mul_right`).
* `LaurentOnRight F a f` says that every test has a shifted integral equal to a
  single Laurent polynomial on `a < Re s`. `laurentOnRight_span` extends it
  from a set to its span, using convergence of every element of the span on
  that half-plane.
* `exists_openSubgroup_twist_trivial`. Since `w` is smooth, an open subgroup
  fixes it, and on that subgroup intersected with `K_m` the eigenvalue
  `η(det k)` must be `1`.
* `laurentOnRight_biSmooth_of_eigenvector`. The common half-plane is the first
  component of the matrix analytic assertions in the data. A bi-smooth
  coefficient `g ↦ λ(ρ g v)` is rewritten using
  `span_range_orbit_eq_top`: by irreducibility, `v` lies in the span of the
  translates `ρ h w`. So the coefficient lies in the span of the right
  translates of the `η`-equivariant coefficient `g ↦ λ(ρ g w)`, which is
  continuous by `continuous_of_mem_biSmoothMatrixCoefficients`.
* `laurentOnRight_iota_biSmooth_of_eigenvector` is the same argument for the
  inverse-transpose functions `coefficientIota f`. Here `ι(g ↦ λ(ρ g w))` is
  `η⁻¹`-equivariant, because `K_m` is stable under inverse transpose
  (`inverseTranspose_mem_principalLevelSubgroup`) and
  `det(k^{-T}) = (det k)⁻¹` (`det_inverseTranspose`). The translates of `w`
  become right translates by `h^{-T}`.
* `laurent_of_hasShiftedRationalValue` identifies each rational value with the
  Laurent polynomial, by uniqueness of rational continuation. The published
  `normalizedGenerator_eq_one_of_laurent` then forces both normalized
  generators to be `1`.

## From matrix data to the pair L-factor

`isPadicSymmetricLPolynomial_one_of_eigenvector` chooses a nonzero standard
Whittaker functional `ℓ` from the full-Whittaker-type equivalence and passes to
the coefficient model through `Whittaker.modelEquiv`. Irreducibility and full
Whittaker type transfer along that equivalence. The published
`genericMatrixFunctionalEquation`, at the model carrier's universe, supplies
matrix data. The eigenvector is transported by `Whittaker.modelMap`, and the main
theorem gives `P = 1`. The published `exists_modelMatrixNormalizedGenerator`
gives a polynomial that is both the pair L-polynomial against
`rankOneCharacter 1` and the matrix normalized generator of every nonzero model.
Uniqueness of normalized generators identifies it with `P = 1`.
