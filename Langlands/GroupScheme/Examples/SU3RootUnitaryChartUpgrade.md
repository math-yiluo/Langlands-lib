# Upgrade of unitary charts (proof)

Module `Langlands.GroupScheme.Examples.SU3RootUnitaryChartUpgrade`.

Main theorem: `Langlands.GroupScheme.RelativeRoot.unitaryChartUpgrade :
UnitaryChartUpgradeStatement.{u}`. It proves the statement
`Langlands.GroupScheme.RelativeRoot.UnitaryChartUpgradeStatement` in
`Langlands.GroupScheme.Rational.RootHeisenbergUnitaryChart`: a rational homomorphism
`φ : U_{L/E}(E) → U(K)` with chart form `φ(u, v) = incl(B v + H(u, u)) * sec(A u)` is the map on
rational points of a homomorphism `ψ : W = R_{E/K} U_{L/E} ⟶ U`, and `ψ ≫ j` represents the
root subgroup `U_a`. The proof builds `ψ` as an isomorphism `W ≅ U`. The auxiliary
declarations live in the namespace `Langlands.GroupScheme.RelativeRoot.UnitaryChartUpgrade`.

## Polynomial identities

- `eq_zero_of_natural` (**polynomial identity principle**). Let `K` be an infinite field and
  `F_R : (I → R) → (J → R)` a family of maps indexed by `K`-algebras `R`, natural along
  `K`-algebra maps. If `F_K = 0`, then `F_R = 0` for every `R`. Proof: by naturality along the
  evaluations `MvPolynomial I K → K`, every evaluation of the universal value
  `F (MvPolynomial I K) X` is zero. By `MvPolynomial.funext` (`K` infinite) that value is zero.
  Then use naturality along `aeval x : MvPolynomial I K → R`.
- `matVec R M v` is a `K`-matrix acting on vectors over a `K`-algebra `R`. `quad R c v` is the
  quadratic map `l ↦ ∑ₛ ∑ₜ vₛ vₜ c(s, t, l)` with coefficients `c` in `K`. The lemmas cover
  naturality (`matVec_map`, `quad_map`, `matVec_add_quad_map`), additivity, composition
  (`matVec_matVec`, `matVec_one`), injectivity and right inverses from inverse matrices.
  `bilin_sum_smul` expands a `K`-bilinear map on linear combinations as a `quad`.

## Linear algebra of the chart form

Let `b` be a `K`-basis of `E`, and let `e`, `f`, `t` be the chart basis, center and trace-one
element of the canonical chart `chartData E L`.

- `towerBasis E L b`: the `K`-basis `(i, j) ↦ bⱼ • eᵢ` of `L` (`Module.Basis.smulTower'`).
- `centerMap E L b ζ = (∑ⱼ ζⱼ bⱼ) • f`, a `K`-linear map `K^n → L` onto the trace-zero line.
- `chartForm E L B H x y = B(t x σ(y)) + H(x, y)`, a `K`-bilinear map. `chartCoeff` gives its
  values on pairs of tower basis vectors.
- `vecMatrix E L b A` and `scalarMatrix E L b B` are the matrices of `A ∘ (tower coordinates)⁻¹`
  and of `B ∘ centerMap`.
- `chartForm_rationalComponents`: for a field parameter `p = (u, v)` with basis components
  `(α, ζ)`, `scalarMatrix ζ + quad(chartCoeff) α = B v + H(u, u)`. This holds because
  `v = (∑ ζⱼ bⱼ) f + t u σ(u)` (`second_eq_rationalCoordinates`) and `u = towerBasis`-sum of `α`
  (`towerBasis_rationalComponents`).
- `exists_vecMatrix_inverse` (from bijectivity of `A`) and `exists_scalarMatrix_inverse` give
  two-sided inverse matrices. For the second, `bijective_scalar` shows that `B ∘ centerMap` is
  bijective. Injectivity: the values of `centerMap` have trace zero, `f ≠ 0`, and `B` is
  injective on trace-zero elements. Surjectivity: every trace-zero element is an
  `E`-multiple of `f` (`exists_algebraMap_mul_eq_of_traceZero`).

## The chart map

- `chartMap N e e' E L b A B H T x` is the `T`-point
  `testChartPoint (scalarMatrix ζ + quad(chartCoeff) α) (vecMatrix α)` of `U`, where `(α, ζ)` are
  the basis components `pointComponents L b T x` of the `T`-point `x` of `W`.
- `defect R α α'` is the polynomial expression
  `scalarMatrix(weilForm α α') + Q(α + α') − Q(α) − Q(α') − coordinatePairing(Am α, Am α')`
  with `Q = quad(chartCoeff)` and `Am = vecMatrix`.
- `chartMap_mul_iff`: `chartMap (x y) = chartMap x · chartMap y` if and only if the defect of
  the first components of `x` and `y` vanishes. The proof compares the Heisenberg law of chart
  points (`testChartPoint_mul_sections`, built on `testChartPoint_mul` and
  `chartCocycle_eq_coordinatePairing`) with the group law of `W` in basis components
  (`pointComponents_mul_fst/snd`), using injectivity of chart coordinates.
- `chartMap_rationalPoint`: on `rationalPoint L p` the chart map is
  `chartPoint (A u) (B v + H(u, u))`. This uses `pointComponents_rationalPoint`,
  `chartForm_rationalComponents` and `chartPoint_eq_testChartPoint`.
- `defect_map`: the defect is natural in `R` (`weilForm_map`, `quad_map`, `matVec_map`,
  `coordinatePairing_naturality`).
- `chartMap_mul_baseTest`, `defect_baseTest_eq_zero`, `defect_field_eq_zero`: every rational
  point of `W` is a `rationalPoint` (`exists_rationalPoint_eq`), and `φ` is a homomorphism, so
  the chart map is multiplicative over the identity test scheme. Hence the defect vanishes
  over `Γ(Spec K)`, so over `K` by naturality along `K ≅ Γ(Spec K)`
  (`identitySectionsEquiv`).
- `defect_eq_zero`: the defect vanishes over every `K`-algebra. This is
  `eq_zero_of_natural` with index set `I ⊕ I` for the pair `(α, α')`.
- `chartMap_mul`: the chart map is multiplicative over every test scheme.
- `chartMap_bijective`: from the inverse matrices of `vecMatrix` and `scalarMatrix`.
  Injectivity uses `testChartPoint_injective`. Surjectivity uses `exists_testChartPoint_eq`:
  solve `α = Am⁻¹ x`, then `ζ = Bm⁻¹ (w − Q α)`.
- `chartMap_naturality`: the chart map commutes with pullback along `f : T' ⟶ T`
  (`comp_testChartPoint`, `pointComponents_naturality`, `matVec_add_quad_map`).

## The isomorphism

- `pointsMulEquiv`: the chart maps as multiplicative equivalences
  `(T ⟶ W) ≃* (T ⟶ U)`.
- `chartIso : W ≅ U` comes from `isoOfPoints`, using their naturality.
  `comp_chartIso_hom` says that `x ≫ chartIso.hom = chartMap T x`.
- `unitaryChartUpgrade`: take `b = Module.finBasis K E` and `ψ = chartIso.hom`. On rational
  points, `rationalPoints.map_apply`, `comp_chartIso_hom`, `chartMap_rationalPoint` and the
  chart form `hφ` give `ψ(p) = φ(p)`. For representability, `ψ ≫ j` is a monomorphism, since
  `ψ` is an isomorphism and `j` is a monomorphism. Its range is the range of `j`
  (`SubgroupFunctor.range_iso_comp`), which is `U_a` by `hj`.

The hypotheses that `S` is a split torus, that `a ≠ 0`, that no `n • a` with `n ≥ 3` is a
root, and the smoothness and finiteness assumptions on `G` are not used.
