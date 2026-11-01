# Proof: the Laurent coefficient normal form of the actual relative unit annulus

Authors: Worker 1177 wrote this Lean proof and its Markdown. The route follows
the proof plan that Worker 105 sketched in the context of the proof task
(diagonal sums of coefficients, an axis section and quotient norm estimates).

The theorem
`Langlands.Analytic.PresentedAffinoidAlgebra.RelativeUnitAnnulus.normal_form`
proves the published proposition
`Langlands.Analytic.PresentedAffinoidAlgebra.RelativeUnitAnnulus.NormalFormStatement.{u}`
from module
`Langlands.Geometry.Analytic.GeneralizedAffinoid.RelativeUnitAnnulusNormalFormStatement`.
The type of the unapplied theorem is exactly that proposition, for the single
universe parameter `u`. It has no parameters or extra hypotheses: `K`, its
`NormedField`, `IsUltrametricDist` and `CompleteSpace` instances and the
presented base `A` are quantified inside the statement and introduced by the
proof. The module imports the statement module and the published
`Langlands.Geometry.Analytic.GeneralizedTateAlgebra.PolynomialApproximation`.
It changes no imported file and adds no helper module. Every auxiliary
declaration lives in the namespace
`Langlands.Analytic.PresentedAffinoidAlgebra.RelativeUnitAnnulus.NormalForm`.

## The objects used

Write `T = GeneralizedTateAlgebra (PositivePolyradius.unit (Fin 2)) A` for the
relative two-variable unit-radius series (local notation `𝕋` in the Lean
file). The annulus is the published carrier

```lean
RelativeUnitAnnulus.Algebra K A
  = RelativeRelations.QuotientAlgebra K A (PositivePolyradius.unit (Fin 2)) (equations K A)
```

that is, Mathlib's ring quotient of `T` by the closed ideal
`(Ideal.span (equations K A)).closure`, where `equations K A` is the singleton
`{X₀ * X₁ - 1}`. Its norm is Mathlib's quotient norm (the infimum of the norms
of representatives). The proof never replaces this carrier or norm. It uses
only the published quotient API from `GeneralizedAffinoid.RelativeUnitAnnulus`:

- `quotientMap K A`, the quotient projection, with `quotientMap_surjective`
  and `quotientMap_eq_zero_iff` (an element maps to zero exactly when it lies
  in the closure of the generated ideal);
- `norm_quotientMap_le` (the projection is contractive);
- `exists_representative_norm_lt` (every class has a representative whose
  norm exceeds the class norm by less than any given `ε > 0`); this is the
  defining property of the quotient norm;
- `baseMap`, `annulusX`, `annulusY`, `annulusX_mul_annulusY`, `positive`,
  `negative`, `positive_apply` and `negative_apply`.

The target is Mathlib's `C₀(ℤ, A)` with its own module structure and
supremum norm. Small lemmas in the section `CZero` record that evaluation at
`n` is bounded by the norm (`norm_apply_le`), that a function bounded pointwise
by `C ≥ 0` has norm at most `C` (`norm_le_of_forall`, both through Mathlib's
bounded continuous functions), that evaluation is continuous, and that an
element tends to zero along the cofinite filter (`cocompact_eq_cofinite` on the
discrete integers). The function `single m a`, equal to `a` at `m` and to `0`
elsewhere, is an element of `C₀(ℤ, A)`.

## Step 1: coefficients of unit-radius series

For unit-radius series the weight of every exponent is one, so the published
`weighted_norm_coeff_le` gives `‖coeff d f‖ ≤ ‖f‖` (`norm_coeff_le_unit`), and
the defining decay condition says that the coefficients tend to zero along the
cofinite filter (`tendsto_coeff_unit`). Each coefficient is therefore a
continuous additive map (`continuous_coeff`).

The density tool is `eq_of_monomial`. Two continuous additive maps from a
generalized Tate algebra to a Hausdorff additive group that agree on every
monomial `monomial r B d b` agree everywhere. The proof maps the published
unconditional expansion `hasSum_monomials` (each series is the sum of its
coefficient monomials) through both maps and uses uniqueness of limits. The
laws below are reduced to monomials by this lemma.

## Step 2: the diagonal coefficient functionals

The integer degree of an exponent `d : Fin 2 →₀ ℕ` is
`degree d = (d 0 : ℤ) - (d 1 : ℤ)`. For `n : ℤ` and `f : T` the diagonal
functional is

```lean
diagonal K A n f = ∑' d, if degree d = n then MvPowerSeries.coeff d (series _ A f) else 0
```

The family is summable (`summable_diagonal`): its terms tend to zero along the
cofinite filter, and in the complete ultrametric group `A` (complete because
`K` is) such families are summable by Mathlib's
`NonarchimedeanAddGroup.summable_of_tendsto_cofinite_zero`. The ultrametric
estimate `IsUltrametricDist.norm_tsum_le_of_forall_le_of_nonneg` gives
`‖diagonal K A n f‖ ≤ ‖f‖` (`norm_diagonal_le`). The functional is additive
(`diagonal_add`, by `Summable.tsum_add`), hence continuous
(`continuous_diagonal`). On a monomial it returns the coefficient when the
degree is `n` and `0` otherwise (`diagonal_monomial`, by `tsum_eq_single`).

`diagonal_mul_equation` shows that `diagonal K A n (h * (X₀ * X₁ - 1)) = 0`
for every `h : T`. Both sides are continuous additive functions of `h`, so by
`eq_of_monomial` it suffices to take `h` a monomial with exponent `d`. Then
`h * X₀ * X₁` is the monomial with exponent `d + e₀ + e₁`, which has the same
degree as `d`, so the two diagonal values cancel. The zero set of the
continuous functional is closed and contains the generated ideal, so it
contains its closure (`diagonal_closure`). Every diagonal functional
therefore vanishes on the ideal used to form the annulus.

## Step 3: the axis section

For `m : ℤ` put `exponent m = single 0 m.toNat + single 1 (-m).toNat`, the
exponent of `X^m` when `m ≥ 0` and of `Y^(-m)` when `m < 0`. It has degree `m`
(`degree_exponent`) and is injective. For `φ : C₀(ℤ, A)` the series
`sectionSeries K A φ : T` has coefficient `φ m` at `exponent m` and `0` at
every exponent not of this form (`sectionCoeff`, defined by
`Function.extend`). Its coefficients tend to zero cofinitely because those of
`φ` do (`tendsto_sectionCoeff`), so it is a unit-radius series. The section is
additive, `K`-linear, sends `single m a` to the monomial with exponent
`exponent m` and coefficient `a` (`sectionSeries_single`), and satisfies
`‖sectionSeries K A φ‖ ≤ ‖φ‖` (`norm_sectionSeries_le`, from the published
`norm_le_iff` for the Gauss norm). Since exactly one exponent of each degree
carries a coefficient, `diagonal K A n (sectionSeries K A φ) = φ n`
(`diagonal_sectionSeries`, by `Function.Injective.tsum_eq`).

## Step 4: the isometric equivalence

The `K`-linear map `toAnnulus K A : C₀(ℤ, A) →ₗ[K] Algebra K A` sends `φ` to
`quotientMap K A (sectionSeries K A φ)`. It preserves the original quotient
norm (`norm_toAnnulus`):

- Upper bound: the projection is contractive and the section is contractive,
  so `‖toAnnulus K A φ‖ ≤ ‖φ‖`.
- Lower bound: given `ε > 0`, `exists_representative_norm_lt` provides a
  representative `g : T` of `toAnnulus K A φ` with
  `‖g‖ < ‖toAnnulus K A φ‖ + ε`. Then `g - sectionSeries K A φ` maps to zero,
  so it lies in the closure of the generated ideal (`quotientMap_eq_zero_iff`),
  and Step 2 gives `diagonal K A n g = φ n` for every `n`. Hence
  `‖φ n‖ ≤ ‖g‖` for all `n`, so `‖φ‖ ≤ ‖g‖ < ‖toAnnulus K A φ‖ + ε`. As `ε` is
  arbitrary, `‖φ‖ ≤ ‖toAnnulus K A φ‖`.

So `toAnnulus` is a linear isometry (`toAnnulusIsometry`), and in particular
injective. Its range is closed, because an isometry from the complete space
`C₀(ℤ, A)` is a closed embedding.

Surjectivity (`toAnnulus_surjective`) uses only the existing quotient. Two
lemmas reduce monomials. The published `relative_monomial_eq` (through
`quotientMap_monomial`) shows that the class of the monomial with exponent `d`
and coefficient `a` is `baseMap K A a * annulusX K A ^ d 0 * annulusY K A ^ d 1`.
Then `baseMap_mul_pow_pow` uses `annulusX K A * annulusY K A = 1` to cancel
`min i j` factors of `x * y`. It rewrites `b(a) * x^i * y^j` as the class of
the monomial with exponent `exponent (i - j)`, which is
`toAnnulus K A (single (i - j) a)`. So every class of a monomial lies in the
range (`quotientMap_monomial_mem_range`). Any annulus element is
`quotientMap K A f` for some `f`. The finite truncations of `f` converge to
`f` (published `tendsto_truncation`), their classes are finite sums of
classes of monomials and lie in the range, and the projection is continuous,
so `quotientMap K A f` lies in the closed range.

The equivalence is `equiv K A`, the inverse of
`LinearIsometryEquiv.ofSurjective (toAnnulusIsometry K A) (toAnnulus_surjective K A)`.
It has type `Algebra K A ≃ₗᵢ[K] C₀(ℤ, A)` and satisfies
`equiv K A (toAnnulus K A φ) = φ`.

Thus the proof treats the closure quotient directly. It never asserts that
the ordinary ideal generated by `XY - 1` is closed, and it identifies no other
kernel. The kernel information it needs is the inclusion of Step 2: every
diagonal functional kills the closure, and this is used only for the lower
norm bound. Injectivity of `equiv` comes from the isometry, and surjectivity
from the closed range together with the density of monomials.

## Step 5: the six laws

The final theorem introduces `K`, its three instances and `A`, and uses the
existential witness `equiv K A`.

1. `equiv_monomial`: `b(a) * x^i * y^j` equals `toAnnulus K A (single (i - j) a)`
   by `baseMap_mul_pow_pow`, `quotientMap_monomial` and `toAnnulus_single`.
   Hence `equiv K A (b(a) * x^i * y^j) = single ((i : ℤ) - (j : ℤ)) a`, and its
   value at `n` is the statement's `if n = (i : ℤ) - (j : ℤ) then a else 0`.
2. For multiplication by `x`, write `z = quotientMap K A g`. Both
   `g ↦ equiv K A (x * quotientMap K A g) n` and
   `g ↦ equiv K A (quotientMap K A g) (n - 1)` are additive and continuous in
   `g` (the projection is a bounded algebra map and `equiv K A` is
   continuous). On a monomial, `x * (b(a) x^{d₀} y^{d₁}) = b(a) x^{d₀+1} y^{d₁}`,
   and law 1 reduces both sides to `if` expressions whose conditions agree by
   `omega`. So `eq_of_monomial` applies.
3. Multiplication by `y` is the same argument with `y^{d₁+1}` and `n + 1`.
4. For `b(c) * z` the two maps are `g ↦ equiv K A (b(c) * quotientMap K A g) n`
   and `g ↦ c * equiv K A (quotientMap K A g) n`. On monomials,
   `b(c) * b(a) = b(c * a)` because `baseMap` is multiplicative, and law 1
   gives `if n = i - j then c * a else 0 = c * (if n = i - j then a else 0)`.
   Here the multiplication `c * _` takes place in `A`, applied to one value of
   `equiv K A z`; the multiplication of `C₀(ℤ, A)` is never used.
5. For `positive K A h`, with
   `h : GeneralizedTateAlgebra (PositivePolyradius.unit (Fin 1)) A`, the two
   maps are `h ↦ equiv K A (positive K A h) n` and the statement's expression
   `if 0 ≤ n then MvPowerSeries.coeff (Finsupp.single 0 n.toNat) (series _ A h) else 0`.
   The first is continuous because `positive K A` is a bounded algebra map.
   The second is a constant or a continuous coefficient (`continuous_coeff`).
   Every one-variable exponent is `Finsupp.single 0 k` (`exists_single_eq`).
   On the monomial with exponent `single 0 k` and coefficient `a`, the
   published `positive_apply` and `evaluateCoefficients_monomial` give
   `positive K A (monomial) = b(a) * x^k = b(a) * x^k * y^0`
   (`positive_monomial`). Law 1 then gives `if n = k then a else 0`, which
   matches the coefficient side in both cases `0 ≤ n` and `n < 0`, using
   injectivity of `Finsupp.single` and `omega`.
6. `negative K A h` is the same argument with `negative_monomial`
   (`b(a) * x^0 * y^k`), degree `-k`, the condition `n ≤ 0` and the exponent
   `(-n).toNat`.

These laws use exactly the statement's `MvPowerSeries` coefficient
extraction, integer inequalities and `toNat` conversions. In laws 5 and 6 the
degree-zero coefficient appears on both sides.

## Scope of the hypotheses

The proof uses only the given instances on `K`. Completeness of `K` is used for
the published completeness of `A` (summability of diagonal sums) and of
`C₀(ℤ, A)` (closed range), and for the published `positive`/`negative` maps.
No step uses Noetherianity, a nontrivial valuation, strictness of the base, a
nonzero or reduced base, properness of an ideal, closedness of the ordinary
ideal `(XY - 1)`, exactness or gluing. If `A = 0` every space involved is zero
and the same argument applies. A trivially valued `K` is allowed.

## Checks

`lean_check` in environment `3b864ddf-f0af-4c18-8903-c6f813a0ce0f` builds this
module with Lake with no errors or warnings. Inspecting
`Langlands.Analytic.PresentedAffinoidAlgebra.RelativeUnitAnnulus.normal_form`
shows a theorem with one universe parameter `u` and the axioms `propext`,
`Classical.choice` and `Quot.sound` only. These are development checks.
Acceptance needs the formal exact-target validation and independent review.

## Provenance and scope

The source context is Piotr Achinger, *Introduction to non-Archimedean
Geometry*, lecture notes, November 22, 2020, registered as
`achinger-2020-non-archimedean-geometry-nov22`. In the proof of Proposition
7.1.1 (printed p.64) the source writes `A⟨X,X⁻¹⟩ = A⟨X,Y⟩/(XY-1)` with the
ordinary generated ideal, over a complete nontrivially valued field (printed
p.6), and describes its elements as Laurent series. This proof is internal
derived mathematics. It works with the Library's quotient by the closure of
the generated ideal, over an arbitrary presented base, with the original
quotient norm, and with possibly trivially valued `K`. The isometry onto
`C₀(ℤ, A)`, the diagonal functionals, the axis section and the six laws are
not attributed to the source. The source gives context only, not the route of
the Lean proof.

This module proves only the normal-form proposition. It proves no
injectivity of multiplication by `x - b(f)`, no principal-relation
comparison, no overlap presentation, no Laurent exact sequence and no scalar
gluing. Those have separate tasks.
