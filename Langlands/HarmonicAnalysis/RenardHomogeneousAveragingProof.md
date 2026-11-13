# Renard II.3.9: the subgroup averaging map and the invariant functional

Helper module for the proof of
`Langlands.HarmonicAnalysis.HomogeneousFunctions.Renard.Statements`
(Worker 67, Task 5524). It proves the first two conjuncts:
`invariantFunctional : InvariantFunctionalStatement` and
`averagingStatement : AveragingStatement`, at the full universe parameter
`uG`.

Source: David Renard, *Représentations des groupes réductifs p-adiques*,
French version of 9 July 2026, registered as
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
The Theorem of II.3.9 and its proof are on printed pp.49–50 / PDF pp.55–56.
The Lean proof follows Renard's strategy: the averaging map `p` is
surjective, and every right-invariant distribution on `G` vanishes on its
kernel. It replaces two of his steps by finite algebraic arguments, as
explained below. It uses no Fubini theorem, no quotient measure and no
countability hypothesis on `G` or `H`.

Notation: `δ` is Renard's modular character `Distribution.renardModular`
(the reciprocal of Mathlib's), `T = Distribution.ofMeasure μG.inv` is the
right Haar distribution, and `V = renardSpace H hH`.

## The averaging map

`modularWeight g = ((δ(g) : ℝ)⁻¹ : ℂ)` is multiplicative, nonnegative and
locally constant (`Distribution.RenardModular.regularity`).
`modularWeight_eq_inv_cast` identifies it with the target's weight
`((δ(g) : ℝ) : ℂ)⁻¹`. For a test function `f` and `y ∈ G`, `slice hH f y` is
the test function `h ↦ f(h y) δ(h)⁻¹` on `H`. Its support is compact because
`h ↦ h y` is a closed embedding of `H`, and it is integrable by
`Distribution.test_integrable` (`integrable_slice`).

`average hH μH f y = ∫_H f(h y) δ(h)⁻¹ dμH(h)` is `ofMeasure μH` applied to the
slice. Its properties are:

- right translation of `f` translates the average (`average_rightTests`);
- a compact open right stabilizer of `f` (from
  `commonCompactOpenBiInvariance`) is one for the average, so the average is
  locally constant;
- `average_mul_left`: `average f (h₀ y) = (δ_G(h₀)/δ_H(h₀)) · average f y`.
  This comes from the right-translation formula
  `Distribution.RenardModular.translation` for `μH` on `H`, which is locally
  compact as a closed subgroup;
- if the average at `y` is nonzero then `f(h y) ≠ 0` for some `h ∈ H`, so the
  support of the average lies in `H · supp f`.

Together these give `averageVec : V`. `averaging` is the corresponding linear
map, with value formula `averaging_apply` and right equivariance
`averaging_rightTests`.

## Coset tests and the kernel

For a compact open subgroup `K`, `cosetTest K hKc a` is the characteristic
function of `a K`, and `dcoset K H a` is the double coset `H a K`. The basic
facts used are:

- `cosetTest (h a) = leftTests h (cosetTest a)` and
  `cosetTest (a k) = cosetTest a`;
- `average_leftTests`: averaging is scaled by `δ(h)⁻¹` under left translation
  by `h ∈ H`, by left invariance of `μH`;
- `inverse_leftTests`: `T(leftTests h φ) = δ(h)⁻¹ T(φ)`, by the same
  translation formula on `G`;
- the average of `cosetTest a` vanishes off `H a K`
  (`average_cosetTest_eq_zero`) and is strictly positive at `a`
  (`average_cosetTest_self_pos`). Positivity comes from
  `Distribution.RenardHaar.ofMeasure_positive`.

`inverse_eq_zero_of_averaging_eq_zero` proves that `p f = 0` implies
`T f = 0`. Take a compact open right stabilizer `K` of `f` and write
`f = Σ_j c_j · cosetTest (g_j)` with the Library expansion
`Hecke.RenardTestDecomposition.rightInvariantExpansion`. Evaluating `p f = 0`
at each `g_i` gives `Σ_j c_j P_{ij} = 0`, where `P_{ij}` is the average of
`cosetTest (g_j)` at `g_i`. The abstract finite lemma `sum_eq_zero_of_classes`
groups indices by their double coset `H g_j K`. Across classes `P_{ij} = 0`.
Within a class `g_j = h g_i k`, so the coset-test identities give
`T(cosetTest g_j) · P_{ii} = T(cosetTest g_i) · P_{ij}` (both sides acquire
the factor `δ(h)⁻¹`). Since `P_{ii} ≠ 0`, the lemma yields
`Σ_j c_j T(cosetTest g_j) = 0`, which is `T f`.

This replaces Renard's identification of the `K`-fixed tests supported in
`H g K` with finitely supported functions on the discrete set `H g K / K`.
Both arguments compare two linear forms with the same `H`-transformation law.

## Surjectivity with nonnegative preimages

`exists_averaging_eq` shows that every `F ∈ V` is `p f` for some test `f`,
and that `f` can be chosen pointwise nonnegative when `F` is. Take a uniform
compact open stabilizer `K` of `F` (`exists_uniform_stabilizer`). Cover the
compact set `C` with `supp F ⊆ H C` by finitely many cosets `x K`, `x ∈ S`.
`exists_averaging_eq_of_cover` inducts on the finset `S`. At a new point `x`
set `c = F(x) / P` with `P = average (cosetTest x) x > 0`, so `c ≥ 0` if
`F ≥ 0`. Then `F' = F − c · p(cosetTest x)` is still `K`-invariant. It vanishes
on `H x K` by covariance and `K`-invariance, and agrees with `F` off `H x K`.
So `F'` is covered by `S` without `x`, and it is nonnegative if `F` is. The
preimage is `f' + c · cosetTest x`. This is Renard's reduction to
one-dimensional pieces, organised as an induction.

## The functional

`exists_functional` takes a linear right inverse `s` of the surjective map
`p` (`LinearMap.exists_rightInverse_of_surjective`) and sets `ν = T ∘ s`.
The kernel lemma gives `ν ∘ p = T`. Right invariance of `ν` follows from
surjectivity, `averaging_rightTests` and right invariance of `T`
(`inverse_rightTests`, from left invariance of `μG`). `ofMeasure_inv_eq`
identifies `T` with the published inversion of `ofMeasure μG`. Hence `T` is
positive by `Distribution.RenardHaar.isPositive_inversion`
(`inverse_positive`).

## The two statements

`averagingStatement` puts the borel structure on `H` exactly as in the
target. It supplies `averaging`, its integrability and value formula
(rewritten with `modularWeight_eq_inv_cast`), surjectivity, equivariance
and `exists_functional`.

`invariantFunctional` chooses the Borel structures and the Haar measures
`Measure.haar` on `G` and `H`, then takes `ν` from `exists_functional`.

- Positivity: a nonzero nonnegative `F` has a nonzero nonnegative preimage
  `f`, and `ν F = T f > 0`.
- Uniqueness in the full algebraic dual: if `S` is right invariant then
  `S ∘ p` is a right-invariant distribution. Its inversion is left invariant
  (`isLeftInvariant_inversion`). The Haar uniqueness part of
  `Distribution.RenardHaar.measureHaarBridge` gives `S ∘ p = c • T`, so
  `S = c • ν` because `p` is surjective (`LinearMap.cancel_right`). The
  scalar is unique because `ν ≠ 0` (`T` is positive, hence nonzero).
- Positive uniqueness: if `S` is also positive, then `S ∘ p` is positive by
  `averaging_ne_zero` and `averaging_nonneg`.
  `Distribution.RenardHaar.positive_real_multiple` gives a unique positive
  real `r` with `S ∘ p = r • T`, which transfers to `S = r • ν` by
  cancellation.
