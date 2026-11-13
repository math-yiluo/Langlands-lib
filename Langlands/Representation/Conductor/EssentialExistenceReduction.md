# Existence of the essential vector from the JPSS inputs

This internal unit proves the existence half of Jacquet 2012, Theorem 1 (printed page
517), conditional on three analytic inputs. Jacquet takes these from Jacquet,
Piatetski-Shapiro and Shalika 1983 in sections 1-2 of the correction (printed pages
518-522). They are explicit hypotheses of the final theorem; this unit claims no
instance of them. Everything else in Jacquet's existence argument is proved here or in
published modules, over an arbitrary nonarchimedean local field. Uniqueness is a
separate matter (`Conductor/EssentialUniquenessReduction`).

The final theorem is `exists_isEssentialVector_of_jpss`. Its conclusion is the published
`IsEssentialVector h π ℓ w` for some vector `w` of the Whittaker model
`coefficientModel π ℓ`.

## Setting

Fix Jacquet's normalizations `h : IsJacquetNormalization q ψ abv ϖ μ` (residue
cardinality `q`, normalized absolute value, `ψ` of conductor `O`, compatible quotient
measure `μ` on `N_(n+1) \ GL_(n+1)`). Let `π` be a smooth representation of
`GL_(n+2)(F)`, `ℓ` a `ψ`-Whittaker functional, and `P` a polynomial with the published
`IsCharacterLPolynomial q ψ abv (rankOneQuotientHaar F) 1 π P` (so `L(s, π) = P(q^(-s))⁻¹`).
For a tuple of units `x` write `W(x)` for `inverseSphericalWhittaker h.conductor.1
h.uniformizer q x` (Jacquet's `W(g; x; ψ̄)`), `Ψ(s, w, W(x))` for the published
`corankOneIntegral ψ abv μ w.val W(x) s`, `Q_x = ∏_i P(x_i X)` (the polynomial
`∏ i, P.comp (C (x i) * X)`) and `X = q^(-s)` (`spectralPoint q s`).

## The three inputs

1. `hconv`: for every model vector `w` and every `x` there is `a` such that
   `CorankOneConverges ψ abv μ w.val W(x) s` for all `s` with `Re s > a`. Jacquet
   (printed page 519): the integral "converges absolutely if Re(s) ≫ 0".
2. `hpoly`: for every `w` and every `x` there are `a`, `N ∈ ℤ` and a polynomial `Q` with
   `Ψ(s, w, W(x)) · Q_x(q^(-s)) = q^(-Ns) Q(q^(-s))` for `Re s > a`. That is, the product
   of the integral with `∏ P(x_i q^(-s))` is a Laurent polynomial in `q^(-s)`. On pages
   520-521 Jacquet multiplies the formal series by `∏ P(X X_i)` and concludes that the
   product is a polynomial, using the JPSS 1983 functional equation. This input is the
   pointwise statement that this step needs. The uniformity in `x` is then proved here,
   by the Baire argument of `Conductor/SphericalUniformBound`, not by the functional
   equation.
3. `hgen`: for every `x` there are finitely many model vectors `W_j` and integers `e_j`
   (indexed by `Fin k`) and `a` such that
   `(∑_j q^(-e_j s) Ψ(s, W_j, W(x))) · Q_x(q^(-s)) = 1` for `Re s > a`. This is Jacquet's
   Lemma 4 (printed page 519), `∑_j q^(-n_j s) Ψ(s, W_j, W(x)) = ∏ P(q^(-s) x_i)⁻¹`,
   multiplied through by `Q_x`. Jacquet derives it from JPSS 1983 (his Lemma 3) and his
   Lemmas 1-2.

## Proof outline

The Lean proof follows Jacquet's sections 2-3 with the published spherical
infrastructure (`SphericalSeries`, `SphericalProduct`, `SphericalEvaluation`,
`SphericalNumeratorIdeal`). There `corankOneModelDenominatorProduct h π hπ ℓ w P` is the
product `Ψ(X; W) ∏ P(X X_i)` of Jacquet's page 520 as a Laurent series over symmetric
Laurent polynomials, and `corankOneModelNumerator` is Jacquet's `Ξ(W)`, the sum of its
coefficients when its support is finite.

1. **Laurent sums** (section `Laurent`). `hasSum_polynomial_eval_mul`: if
   `∑_d y^d c_d` converges to `f`, then the convolution of `c` with the coefficients of a
   polynomial `Q` sums to `Q(y) f`. `hasSum_coeff_shift`: shifting coefficients by `k`
   multiplies the sum by `y^k`. `hasSum_monomial_mul_polynomial`: `y^N Q(y)` as a finite
   Laurent sum. `coeff_eq_zero_above_of_hasSum_eq`: a Laurent series with lower-bounded
   support whose sums on `(0, r)` equal `y^N Q(y)` vanishes above degree `N + deg Q`.
   It uses the published identity theorem `eq_zero_of_hasSum_int_eq_zero`.
   `exists_spectralPoint_eq`: each `y ∈ (0, q^(-a))` is `q^(-s)` for a real `s > a`.
2. **Residue classes** (section `Residue`). `residueClassLift` lifts each residue class
   of the valuation ring to `F` by `Function.surjInv`. The lifts of distinct classes
   differ by an element of valuation one (`residueClassLift_eq_of_lt_one`), and every
   integral element is congruent to a lift (`exists_residueClassLift_lt_one`).
   `exists_adjacentUnit_ne_one`: since `ψ` has conductor `O` and `ϖ⁻¹ ∉ O`, some
   `x ∈ ϖ⁻¹ O` has `ψ(x) ≠ 1`, so the inverse standard character is nontrivial on every
   adjacent root subgroup at a point of `ϖ⁻¹ O`. These are the finite-sum inputs of the
   published `exists_corankOneModelNumerator_eq_one_of_no_common_zero`.
   `exists_corankOneModelNumerator_eq_one` applies it with these inputs. If at every
   tuple of units some model vector with finite numerator has a nonzero numerator value,
   some model vector has numerator `1`. This is Jacquet's Lemma 5 together with the weak
   Nullstellensatz.
3. **Finiteness** (section `Model`). `hasSum_specializedDenominatorProduct`: on the
   half-plane of convergence, `Q_x(q^(-s)) Ψ(s, w, W(x))` is the Laurent sum of the
   specialized product, by the published `hasSum_corankOneIntegral`.
   `specializedDenominatorProduct_exists_upper_bound` combines this with `hpoly` and step
   1 to bound each specialization above.
   `corankOneModelDenominatorProduct_support_finite_of_jpss` then gives finite support
   over the symmetric Laurent algebra, by `Conductor/SphericalUniformBound`.
4. **No common zero.** `sum_numerator_evaluation_eq_one`: under `hgen` at `x` (with
   finite supports and convergence for the `W_j`), the values at `x` of the numerators
   of the `W_j` add up to `1`. By steps 1 and 3 the coefficients of the specialized
   products satisfy `∑_j T_j(t - e_j) = δ_(t,0)` for every `t`. Summing over `t` gives
   the claim, since the shifts do not change the sums. So some `W_j` has nonzero
   numerator value at `x`. This is Jacquet's observation (page 523) that the
   `q^(-n_j s)` factors disappear at `X = 1`.
5. **Numerator one gives the identity.**
   `specializedDenominatorProduct_coeff_of_numerator_eq_one`: if `Ξ(w) = 1` then every
   specialization of the product of `w` is the constant series `1`. The coefficients are
   homogeneous, so `∑_d T_d(x) c^d = Ξ(w)(c x) = 1` for every `c ≠ 0`. The identity
   theorem then gives `T_d(x) = δ_(d,0)`. `hasRationalContinuation_essentialFactor_of_coeff`:
   then `Q_x(q^(-s)) Ψ(s, w, W(x)) = 1` wherever the integral converges. Hence
   `Q_x(q^(-s)) ≠ 0` there, and `Ψ` agrees with the published `essentialFactor P x` on a
   right half-plane (`HasRationalContinuation`), as required by
   `SatisfiesEssentialIdentity`.
6. **Averaging** (section `Averaging`). The published `IsEssentialVector` also requires
   that the restriction of `w` to `diag(GL_(n+1), 1)` is right `GL_(n+1)(O)`-invariant.
   Jacquet's Theorem 1 does not include this clause; it is part of the uniqueness
   statement. `restrictedModelRepresentation` is `g ↦ π(diag(g, 1))` on the model, smooth
   by the published `model_isSmooth`. `degreeCorankOneModelCoefficient_integral_translate`:
   translating by `diag(k, 1)` with `k ∈ GL_(n+1)(O)` does not change the Laurent degree
   coefficients. `W(x)`, `|det|` and the degree are right `GL_(n+1)(O)`-invariant, and
   `μ` is right invariant. `exists_integralInvariant_degreeCoefficients_eq`: the published
   compact average `Compact.averageMap` over the compact open subgroup
   `levelOpenSubgroup F n 0 = GL_(n+1)(O)` gives a vector that satisfies
   `IsIntegralInvariantOnRestriction` and has the same degree coefficients
   (`linearMap_orbitMean_eq`: an invariant linear map is constant on finite orbit means).
   By `corankOneModelDenominatorProduct_eq_of_degreeCoefficients_eq` it also has the
   same denominator product.
7. **Assembly.** `exists_isEssentialVector_of_jpss`: by step 3 every model vector has
   finite support. By step 4 the hypothesis of step 2 holds, so some `w₀` has
   `Ξ(w₀) = 1`. Average `w₀` (step 6) to `w₁`. Then step 5 applies to `w₁`, with
   convergence from `hconv`, and `w₁` is essential with the given `P`.
