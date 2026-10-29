# Proof of equal-rank determinant-slice lower support

`Langlands.RankinSelberg.equalRankSliceSupport` proves the unchanged Library
proposition
`Langlands.RankinSelberg.EqualRankSliceSupportStatement.{uF,uV,uW} F T n`
from `Langlands.Representation.RankinSelberg.EqualRankSliceSupportStatement`.
It holds for every `p : ℕ` with `[Fact p.Prime]`, every `F : PadicField.{uF} p`,
all supplied `T : F.TopologicalData` and every `n : ℕ`. The field universe and
the two carrier universes stay independent. The statement pair and every pair
it imports are imported without modification.

Worker 887 wrote the Lean proof and this note. The route is the internal one
that Worker 484 proposed in the statement's paired Markdown and in the proof
task. It is derived from published Library results. It does not use a gauge
estimate or a torus expansion, and it claims nothing further about the
original JPSS arguments discussed below.

## What is proved

After the telescope's local instances, the proof introduces every unitary
character `ψ`, the right-invariance instance, every compatible quotient
measure `μ`, both carriers, both representations `π` and `σ` with their
Whittaker-type hypotheses, every `ℓ`, `ℓ'`, every coefficient `f`, `f'`
(zero included) and every row test `Φ`. It then proves

```text
BilateralLaurentSeries.HasLowerBoundedSupport
  (equalRankSliceCoefficient T μ ψ f.val f'.val Φ).
```

It applies the published equivalence
`BilateralLaurentSeries.hasLowerBoundedSupport_iff` to the coefficient
function, with an explicit argument. It then exhibits an integer `M = -N`
such that the coefficient vanishes for every `m < M`. The integer `N` is
chosen after all of the data. In particular it depends on `f` and `Φ`. No
uniformity over coefficients or tests is claimed.

No integrability, convergence, irreducibility, unitary central character,
gauge bound or support hypothesis is added. The only fact used about `π` is
its smoothness, the first component `hπ.1.1` of admissibility inside
`IsOfWhittakerType`. The second coefficient `f'`, the representation `σ`
and the measure `μ` are never constrained. The argument proves pointwise
vanishing of the integrand, so the value of `f'` plays no role.

## Helper lemmas

The module adds three public lemmas in `Langlands.RankinSelberg`. Each takes
the topological data `T` as an explicit argument.

1. `normalizedAbs_finsetSum_le`: if `T.normalizedAbs (x i) ≤ C` for every
   `i` in a finset `s`, and `0 ≤ C`, then
   `T.normalizedAbs (∑ i ∈ s, x i) ≤ C`. The proof is finset induction, using
   `T.normalizedAbs_zero` for the empty sum and the ultrametric inequality
   `T.normalizedAbs_add_le_max` for the insertion step.

2. `exists_schwartzBruhat_row_bound`: under `T.topology`, every
   `Φ : SchwartzBruhat (Fin (n + 1) → F.Carrier)` has a constant `C ≥ 0` such
   that `Φ x ≠ 0` implies `T.normalizedAbs (x j) ≤ C` for every coordinate `j`.
   The function `x ↦ ∑ j, T.normalizedAbs (x j)` is continuous by
   `T.continuous_normalizedAbs` and `continuous_finsetSum`. It is bounded on
   the compact set `tsupport Φ`, which is compact by
   `SchwartzBruhat.hasCompactSupport`, via
   `IsCompact.exists_bound_of_continuousOn`. A point where `Φ` is nonzero lies
   in `tsupport Φ`. Each nonnegative summand is at most the sum, and the sum is
   at most the bound. The returned constant is `max C 0`.

3. `normalizedAbs_determinant_le_of_simpleRoot`: let
   `W : WhittakerFunctions ψ n`, `R > 0` and `C ≥ 0`. Suppose the
   simple-root conclusion holds for `W`: for every diagonal unit tuple `a`
   and every `κ` in `Conductor.integralSubgroup` of the valuation integers,
   `W.val (Iwasawa.diagonalUnits a * κ) ≠ 0` implies
   `T.normalizedAbs (a i.castSucc / a i.succ) ≤ R` for every `i : Fin n`.
   Then every `g` with `W.val g ≠ 0` and `T.normalizedAbs (lastRow g j) ≤ C`
   for all `j` satisfies

   ```text
   T.normalizedAbs (det g) ≤ ∏ i : Fin (n + 1), R ^ (n - i) * C.
   ```

   Smoothness is not a hypothesis of this lemma. It enters only through the
   assumed simple-root conclusion.

## Proof of the determinant bound

This is the geometric core, implemented with actual matrices.

*Iwasawa decomposition.* The published
`GeneralLinear.Iwasawa.exists_upperTriangular_mul`, applied to
`ValuativeRel.valuation F.Carrier`, writes `g = b * k`. Here `b` is invertible
and upper triangular, and `k` lies in the integral subgroup. Each diagonal
entry `b i i` is nonzero, because otherwise
`Matrix.det_of_isUpperTriangular` would make the determinant of `b` zero.
Set `a i = Units.mk0 (b i i)`, `D = Iwasawa.diagonalUnits a` and
`u = b * D⁻¹`. The underlying matrix of `u` is `b * diagonal (b i i)⁻¹`. This
is upper triangular (`Matrix.BlockTriangular.mul` with a diagonal matrix) and
has unit diagonal, so `u ∈ upperUnipotent (n + 1) F.Carrier`. Rewriting
gives `g = u * (D * k)`.

*Simple roots at `D k`.* The defining left equivariance of `W`,
`W(u h) = θ(u) W(h)`, shows that `W.val (u * (D * k)) ≠ 0` forces
`W.val (D * k) ≠ 0`. The hypothesis then bounds every adjacent ratio
`|a_i / a_{i+1}|` by `R`.

*Last diagonal entry.* The published `lastRow_unipotent_mul` gives
`lastRow (u * (D * k)) = lastRow (D * k)`, so the last row of `D * k` lies in
the box. Evaluating `(D * k) * k⁻¹ = D` at the entry `(last, last)` gives

```text
a_last = ∑ j, lastRow (D * k) j * (k⁻¹) j last.
```

The inverse `k⁻¹` has integral entries (`Conductor.mem_integralSubgroup`), so
`T.normalizedAbs_le_one_iff_mem_integers` bounds each entry by `1`.
Multiplicativity `T.normalizedAbs_mul` and the ultrametric sum lemma then
give `|a_last| ≤ C`.

*All diagonal entries.* Reverse induction on `Fin (n + 1)`
(`Fin.reverseInduction`) proves `|a_i| ≤ R^(n - i) * C`. The base case is the
last-entry bound. For the step, write
`a_{i.castSucc} = (a_{i.castSucc} / a_{i.succ}) * a_{i.succ}` and use the
ratio bound together with `R > 0`. When `n = 0` there are no ratios and only
the base case occurs, so the bound is `|a_0| ≤ C`.

*Determinant.* `determinant_unipotent_mul` removes `u`, and then
`Matrix.det_mul` together with `Matrix.det_diagonal` gives
`det g = (∏ i, a_i) * det k`. The published
`Conductor.valuation_det_of_mem_integralSubgroup` gives valuation `1` for
`det k`, so `T.normalizedAbs (det k) ≤ 1`. The normalized absolute value
turns the product into a product of absolute values (`map_prod` for the
underlying absolute value). Then `Finset.prod_le_prod₀` and the diagonal
bounds give the stated estimate.

## Proof of the main theorem

1. Apply `Langlands.Whittaker.smoothSimpleRootSupport.{uF,uV}`, for the actual
   carrier `V` and representation `π`, to `ψ`, the smoothness `hπ.1.1`, `ℓ` and
   `f`. This gives `R > 0` with the simple-root conclusion for `f.val`.
2. Apply `exists_schwartzBruhat_row_bound` to `Φ` to get `C ≥ 0`.
3. Put `B = ∏ i : Fin (n + 1), R ^ (n - i) * C` and `q = T.residueCardinality`.
   Since `q > 1` (`T.residueCardinality_gt_one`), `pow_unbounded_of_one_lt`
   gives `N : ℕ` with `B < q^N`.
4. Fix `m < -N`. Rewrite the coefficient by the published
   `equalRankSliceCoefficient_def` as the restricted total Bochner integral of
   `equalRankIntegrand … 0` over `determinantSlice T n m`. Then
   `setIntegral_eq_zero_of_forall_eq_zero` reduces the goal to the integrand
   vanishing at every point of the slice. This lemma needs no integrability
   or measurability hypothesis.
5. A point of the quotient is `Quotient.mk _ g`. Membership in the slice is
   `T.ord (det g) = m` (`mk_mem_determinantSlice`). The integrand there is
   `f.val.val g * f'.val.val g * Φ (lastRow g)` (`equalRankIntegrand_zero_mk`).
   If this product were nonzero, then both `f.val.val g ≠ 0` and
   `Φ (lastRow g) ≠ 0` would hold. The determinant lemma would give
   `|det g| ≤ B`. By `T.normalizedAbs_of_ne_zero` and the slice condition,
   `|det g| = q^(-m)`. Since `-m ≥ N` and `q > 1`,
   `zpow_le_zpow_right₀` gives `q^N ≤ q^(-m) ≤ B < q^N`, which is a
   contradiction.

So every coefficient with index below `-N` is the integral of the zero
function on its slice. This uses the sign convention `|det g| = q^(-m)`: an
upper bound on `|det g|` is a lower bound on the slice index. Rank one
(`n = 0`) goes through the same code without a case split. The simple-root
theorem then supplies only a vacuous ratio bound, and the compact test bound
`|a_0| ≤ C` is the whole estimate.

## Relation to the original source

The source is H. Jacquet, I. I. Piatetski-Shapiro and J. A. Shalika,
*Rankin–Selberg Convolutions*, Amer. J. Math. 105 (1983), 367–464, registered
as `jpss-1983-rankin-selberg`
(`/home/taskhub/central-library/Jacquet-Piatetski-Shapiro-Shalika--Rankin-Selberg Convolutions--1983.pdf`,
SHA256 `d9feed6388ca5acf02ecc6a8cce984871a7c28f062ff441e45a71fa2d8962245`).
Printed pp.385–386, 388–391 and 406–407 were read from rendered page images.
The literature index registers no erratum for this article. The registered
Jacquet (2012) correction concerns the 1981 *Conducteur* paper.

- §4.2, p.406, defines the slices `G_r^m = {g : |det g| = q^(-m)}` and the
  slice integrals `Ψ^m(W, W'; Φ) = ∫_{N_r \ G_r^m} W(g) W'(g) Φ(η_r g) dg`.
  The Library's `determinantSlice` and `equalRankSliceCoefficient` formalize
  these, with `r = n + 1` and `η_r g = lastRow g`.
- §4.2, p.407, states that only finitely many negative-index terms are
  nonzero. It derives this from the torus reduction (2.7.3), writing
  `a = diag(a_1 ⋯ a_r, …, a_r)`. The gauge dominating `W_i` confines the
  support to bounded simple-root coordinates `a_i`, `1 ≤ i ≤ r - 1`.
  `Φ_i(a_r) ≠ 0` bounds `|a_r|`. So each torus integral vanishes unless
  `|det a|` is bounded. These are bounds by constants that depend on the gauge
  and on `Φ_i`, not bounds by the number `1`. The printed text writes the
  gauge estimate as `|a_i| ≤ 1`. Lemma 2.6, p.390, states the corresponding
  gauge bound as `|λ_i / λ_{i+1}| ≤ c`, with `c` depending on the gauge. For
  the last coordinate and the determinant, p.407 prints `|a_r| ⪯ 1` and
  `|det a| ⪯ 1`. The sign is a curved `≺` over a bar, as checked on an
  enlarged rendering of the scan. The same sign appears on p.390, where
  `|λ_i| ⪯ 1` and `‖ε_j g‖ ⪯ 1` follow from `|λ_t| ≤ 1` and the bound
  `≤ c`. There it can only mean an upper bound up to a constant, and this
  note reads p.407 the same way. Compact support gives no literal bound by
  `1`. In rank one, let `Φ` be the characteristic function of `ϖ⁻¹𝒪`, where
  `ϖ` is a uniformizer. Then `Φ(ϖ⁻¹) = 1` although `|ϖ⁻¹| = q > 1`, and with
  trivial `GL_1` coefficients the integrand is nonzero on the negative slice
  `m = -1`. The finite negative tail needs only some finite, data-dependent
  bound.
- §2.5, pp.388–389, gives the gauge majorization of `W ∈ 𝒲(π; ψ)` under the
  extra hypothesis that the central character of `π` is unitary. It gives the
  finite-function expansion (2.5.2) for generic `π`. Lemma 2.6 and its proof,
  pp.389–390, derive bounded adjacent ratios `|λ_i / λ_{i+1}| ≤ c` from
  nonvanishing of a gauge. Theorem 2.7, pp.390–391, treats representations of
  Whittaker type, and (2.7.3) is its Iwasawa and K-finiteness reduction to
  the torus.
- §2.1, pp.385–386, defines Whittaker type (admissible, of finite type, with
  a one-dimensional space of Whittaker functionals) and Whittaker functions
  `W(g) = λ(π(g)v)`.

The implemented proof follows the same geometric idea as p.407: bounded
simple-root coordinates and a bounded last coordinate together bound the
determinant, and only the finiteness of that bound matters. The route
differs from the source's. It does not use the source's gauge majorization,
the central character restriction of §2.5, or the K-finite torus reduction
(2.7.3). The ratio bound comes from the published `smoothSimpleRootSupport`,
which holds for arbitrary smooth coefficient images. It bounds the adjacent
ratios of the Iwasawa diagonal directly by a constant `R`, uniformly over the
integral factor. The last diagonal entry is bounded by the constant `C`
chosen for `Φ`, through the last row of the actual matrix rather than through
a torus test function `Φ_i`. The result is the explicit, data-dependent bound
`|det g| ≤ ∏ R^(n-i) C`. So the full-type, zero-inclusive scope here is
internal provenance through the Library's smooth route. It is not a claim
that the source's single-gauge estimate holds without the central-character
restriction.

## Boundary

The theorem proves only the lower-support endpoint. It proves no slice
integrability, convergence of the zeta integral, Laurent expansion (4.2.2),
rational continuation, gamma, epsilon or L-factor statement, functional
equation or multiplicativity.
