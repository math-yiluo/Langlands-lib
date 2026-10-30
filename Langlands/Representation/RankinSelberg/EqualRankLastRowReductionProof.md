# Equal-rank integrals with a last-row orbit cutoff: proof

Author: Worker 719.

`Langlands.RankinSelberg.equalRankLastRowReduction` proves
`EqualRankLastRowReductionStatement F T n` for every implicit prime `p`, every
`F : PadicField.{uF} p`, every supplied `T : F.TopologicalData` and every
`n : ℕ`. Its type is exactly that proposition, from
[`EqualRankLastRowReductionStatement`](EqualRankLastRowReductionStatement.md).
No hypothesis is added: the result holds for every compact open subgroup `J`,
every pair of compatible quotient measures `μ, μ'`, and every rank `n`
(including `n = 0`, that is `GL_2` against `GL_1`).

The work is done by a general theorem
`LastRowReduction.lastRowReduction` over an arbitrary topological field `K`.
The `p`-adic theorem only specializes it. All auxiliary declarations live in
the namespace `Langlands.RankinSelberg.LastRowReduction`.

## Notation

Write `GL_(m)` for `Langlands.GeneralLinear m K`, `N_(m)` for its
upper-unipotent subgroup, `ι(h) = rankInclusion 1 h = diag(h, 1)` for
`h ∈ GL_(n+1)`, and `y(v) = col v = [[I, v], [0, 1]] ∈ GL_(n+2)` for a column
`v ∈ K^(n+1)`. `col v` is the published mirabolic radical element
`radicalElement v`.

## The general theorem

`lastRowReduction` assumes a field `K` that is a Hausdorff, second countable,
locally compact topological ring with its Borel σ-algebra; Hausdorff, locally
compact, second countable topologies on `GL_(n+1)` and `GL_(n+2)` with Borel
σ-algebras; Borel σ-algebras on `N_(n+1)`, `N_(n+2)` and on both quotients. Its
data are:

- a multiplicative map `χ : K →*₀ ℝ≥0` and an absolute value `abv` with
  `abv x = χ x` for all `x`;
- an additive Haar measure `vol` on `K^(n+1)` with the determinant rule
  `vol.map (toLin' M) = (χ (det M))⁻¹ • vol` for every invertible `M`;
- regular Haar measures `μG, μN, μG', μN'` on `GL_(n+2)`, `N_(n+2)`,
  `GL_(n+1)`, `N_(n+1)`, the two unipotent ones also right invariant;
- quotient measures `μ` and `μ'` compatible with `(μG, μN)` and `(μG', μN')`;
- an open subgroup `J` of `GL_(n+2)` with compact carrier, such that
  `χ (det j) = 1` for every `j ∈ J`.

Its conclusion is the statement's conclusion with `abv` in place of
`normalizedAbsoluteValue T`: one `c > 0`, chosen before `ψ, W, W', W'', Φ, s`,
such that under the three hypotheses on `W, W', W'', Φ` the two convergence
predicates are equivalent and the equal-rank integral is `c` times the
corank-one integral at `s - 1/2`.

## Algebraic lemmas (sections `Algebra`, `Level`)

These hold over any field.

- `col_add`, `col_zero`, `col_neg`, `col_mem`: `col` is a homomorphism from
  `K^(n+1)` into `N_(n+2)`.
- `rankInclusion_mul_col`: `ι(g) y(v) = y(g v) ι(g)`, from
  `levi_mul_radicalElement`; `col_mul_rankInclusion` is the reverse form.
- `exists_col_mul_rankInclusion`, `col_mul_rankInclusion_inj`: every
  `x ∈ N_(n+2)` is uniquely `y(v) ι(u)` with `u ∈ N_(n+1)`, by the published
  mirabolic decomposition `eq_radicalElement_mul_levi` (`v` is the last column,
  `u` the upper-left block; `projection_mem` shows `u` is upper unipotent).
- `conj_col_mul_rankInclusion'`: `ι(g)⁻¹ y(v) ι(u) ι(h) = y(g⁻¹ v) ι(g⁻¹ u h)`;
  `col_mul_rankInclusion_mul` gives the group law
  `y(v₀) ι(u₀) · y(v) ι(u) = y(v₀ + u₀ v) ι(u₀ u)`.
- `level J` (for a subgroup `J` of `GL_(n+2)`) is the image of `J ∩ P` in
  `GL_(n+1)` under the mirabolic projection. `mem_level`: `a ∈ level J` iff
  `y(w) ι(a) ∈ J` for some `w`. `col_mul_mem_iff`: if `y(w₀) ι(a) ∈ J`, then
  `y(w) ι(a) ∈ J` iff `y(w - w₀) ∈ J`.

## Topology and coordinates (section `Coordinates`)

- `continuous_col`; `isOpen_level` and `isCompact_level`: for open `J` the
  level is open (a neighbourhood `{b : y(w) ι(b) ∈ J}`), and for compact `J`
  it is compact (image of the compact set `J ∩ P` under the continuous
  projection; `P` is closed). `levelOpen J` packages it as an open subgroup;
  this is the group `A` of the statement's route.
- `unipotentCoordinates : K^(n+1) × N_(n+1) ≃ₜ N_(n+2)`,
  `(v, u) ↦ y(v) ι(u)`. Its inverse takes the last column and the projection;
  both directions are continuous by the published continuity of
  `radicalElement`, `rankInclusion`, `lastColumn` and `projection`.

## Haar measure in coordinates (section `HaarFiber`)

`coordinateMeasure vol μN'` is the image of `vol × μN'` under
`unipotentCoordinates`.

- `isMulLeftInvariant_coordinateMeasure`: left translation by `y(v₀) ι(u₀)`
  becomes `(v, u) ↦ (v₀ + u₀ v, u₀ u)` in coordinates. Since `det u₀ = 1`, the
  determinant rule makes `v ↦ u₀ v` preserve `vol`; translation preserves
  `vol` and left translation preserves `μN'`, so the product map preserves
  `vol × μN'`.
- `isFiniteMeasureOnCompacts_coordinateMeasure`: images of finite-on-compacts
  measures under a homeomorphism.
- `exists_coordinateMeasure_eq_smul`: by Mathlib's uniqueness of left Haar
  measure (`isMulLeftInvariant_eq_smul`), `coordinateMeasure vol μN' = κ • μN`
  for some `κ : ℝ≥0`. `N_(n+2)` is locally compact
  (`UpperUnipotent.locallyCompactSpace`) and second countable as a subspace.
- `coordinateMeasure_conj`: for `h ∈ GL_(n+1)`,
  `coordinateMeasure vol μN' {x | ι(h)⁻¹ x ι(h) ∈ J}
   = χ(det h) · vol(Y₀) · μN' {u | h⁻¹ u h ∈ A}` with `Y₀ = col⁻¹ J`.
  In coordinates the condition is `y(h⁻¹ v) ι(h⁻¹ u h) ∈ J`. For fixed `u`
  the `v`-fibre is empty unless `h⁻¹ u h ∈ A`. Otherwise, with a witness
  `y(w₀) ι(h⁻¹ u h) ∈ J`, `col_mul_mem_iff` identifies the fibre with the
  preimage of the translate `Y₀ + w₀` under `v ↦ h⁻¹ v`. Its `vol`-measure is
  `χ(det h⁻¹)⁻¹ vol(Y₀) = χ(det h) vol(Y₀)` by the determinant rule and
  translation invariance. The product formula `Measure.prod_apply_symm` then
  integrates this indicator over `u`.

## Orbit classes (sections `Orbits`, `OrbitIndex`)

- `orbitSetoid J` on `GL_(n+1)`: `h ~ h'` iff `h' = u h a` with
  `u ∈ N_(n+1)`, `a ∈ A`. `exists_eq_of_orbitRel` lifts it to rank `n + 2`:
  if `h ~ h'` then `ι(h') = x ι(h) k` with `x ∈ N_(n+2)` and
  `k = y(w) ι(a) ∈ J`. Conversely `orbitRel_of_eq`: if
  `ι(h') k' = x ι(h) k` with `x ∈ N_(n+2)` and `k, k' ∈ J`, write
  `x = y(v) ι(u)`; then `ι(h')⁻¹ y(v) ι(u) ι(h) = k' k⁻¹ ∈ J`, and
  `conj_col_mul_rankInclusion'` shows `h'⁻¹ u h ∈ A`, so `h ~ h'`. Its classes are open (`isOpen_orbitClass`: each
  contains `h A`), hence countably many (`countable_orbitQuotient`, from
  second countability of `GL_(n+1)` and Mathlib's
  `Pairwise.countable_of_isOpen_disjoint`).
- For a class `i` with representative `r = i.out`, `orbitImage J r` is the
  image of `ι(r) J` in `N_(n+2) \ GL_(n+2)`, and `orbitImage' J r` is the image
  of `r A` in `N_(n+1) \ GL_(n+1)`.
- `exists_orbit_of_lastRow`: if the last row of `g` lies in `lastRow '' J`,
  then by the published `lastRow_mem_image_iff` `g = p j` with `p` mirabolic,
  `j ∈ J`. Write `p = y(v) ι(h)` and let `r` be the representative of the
  class of `h`. Since `r ~ h`, `exists_eq_of_orbitRel` gives
  `ι(h) = x ι(r) k` with `x ∈ N_(n+2)` and `k ∈ J`. Then
  `ι(r) (k j) g⁻¹ = x⁻¹ y(v)⁻¹ ∈ N_(n+2)`, so `g` and `ι(r) (k j)` have the
  same image in the quotient, with `k j ∈ J`.
- `eq_of_orbit_mk_eq`: if `ι(i.out) k` and `ι(i'.out) k'` (`k, k' ∈ J`) have
  the same image in `N_(n+2) \ GL_(n+2)`, then `orbitRel_of_eq` gives
  `i.out ~ i'.out`, so `i = i'`. `eq_of_orbit'_mk_eq` is the analogous
  statement in rank `n + 1`, directly from the definition of `orbitSetoid`.
  Hence distinct classes give disjoint orbit images in both quotients.
- `exists_orbit'`: every point `N_(n+1) h` lies in the orbit image of its
  class: if `r = u h a` is the representative, then `h = u⁻¹ r a⁻¹`, so
  `N_(n+1) h = N_(n+1) r a⁻¹`.

## Orbit masses (sections `OrbitMass`, `Main`)

- `isOpen_orbit`: the image of `g K` in a left quotient is open, because the
  quotient map is open.
- `orbit_measure`: for compatible `μ`, the published
  `compactOpenOrbitMeasure` (from `QuotientCompactOpenOrbitProof`) gives
  `μ(N \ N g K) = μH{h : g⁻¹ h g ∈ K}⁻¹ · μG(K)` with the inner measure in
  `(0, ∞)`; the lemma evaluates the published restricted-measure identity on
  the orbit image itself.
- `orbit_mass_relation`: there is `C > 0` with
  `μ(orbitImage J r) · χ(det r) = C · μ'(orbitImage' J r)` for all `r`, both
  masses finite. Combining `orbit_measure` in both ranks with
  `coordinateMeasure_conj` and `coordinateMeasure = κ • μN` gives
  `κ μN{ι(r)⁻¹ x ι(r) ∈ J} = χ(det r) vol(Y₀) μN'{r⁻¹ u r ∈ A}`. At `r = 1`
  this shows `vol(Y₀) < ∞` and `κ ≠ 0`; `vol(Y₀) > 0` because `Y₀` is open and
  contains `0`; `μG(J)` and `μG'(A)` are positive and finite. The constant is
  `C = κ μG(J) / (vol(Y₀) μG'(A))`.

## Invariance (section `Invariance`)

- `rankInclusion_det`, `det_col_mul`: `det ι(g) = det g`,
  `det(y(w) ι(a)) = det a`.
- `lastRow_mul_mem_iff`, `lastRow_rankInclusion_mul_mem`: membership of the
  last row in `lastRow '' J` is unchanged by right multiplication by `J`, and
  holds for `ι(r) k` with `k ∈ J`.
- `level_det_eq_one`: `χ(det a) = 1` on `A`, from the hypothesis on `J`.
- `whittaker_level_invariant`: for `a ∈ A` with `y(w) ι(a) ∈ J`,
  `ι(h a) = y(h(-w)) · ι(h) · y(w) ι(a)`; the published
  `whittaker_product_invariant` removes the left factor in `N_(n+2)`, and
  right `J`-invariance removes `y(w) ι(a)`. So
  `W(ι(h a)) W'(ι(h a)) = W(ι(h)) W'(ι(h))`.
- `corankOneFunction_level_invariant`, `equalRankFunction_right_invariant`:
  the two integrand functions on the groups are right invariant under `A`
  and `J` respectively (the determinant weights do not change because `χ`
  is `1` on determinants of `A` and `J`).

## Comparison (sections `PiecewiseConstant`, `LocallyConstant`, `Compare`, `Main`)

- `piecewiseConstant_integral`: if `f` is a.e.-strongly measurable, constant
  `a i` on each member `E i` of a countable disjoint family of measurable sets
  of finite measure, and zero off their union, then `f` is integrable iff
  `∑ ‖a i‖ μ(E i)` converges, and then `∫ f = ∑ μ(E i) a i`. The proof
  computes the lower integral of `‖f‖` with `lintegral_iUnion` and the
  integral with `integral_iUnion`.
- `piecewiseConstant_compare`: for two such functions on the same countable
  index set with `μ(E i) a i = C μ'(E' i) a' i` termwise, `C > 0`, the
  integrability statements are equivalent and `∫ f = C ∫ f'` (both sides are
  `0` when not integrable).
- `continuous_of_rightInvariant`, `continuous_descend`: a function right
  invariant under an open subgroup is continuous, and so is its descent to
  the left quotient (the quotient map is an open quotient map). This gives
  a.e.-strong measurability of the two descended integrands.

`lastRowReduction` applies `piecewiseConstant_compare` to the classes of
`orbitSetoid J`, with `E i = orbitImage J i.out`, `E' i = orbitImage' J i.out`
and `C` from `orbit_mass_relation`. On `E i` the equal-rank integrand equals its
value at `ι(r)`, on `E' i` the corank-one integrand equals its value at `r`
(invariance lemmas). The equal-rank integrand vanishes off the union because
`Φ(lastRow g) = 0` unless `lastRow g ∈ lastRow '' J`, and then
`exists_orbit_of_lastRow` places `g` in some `E i`; every point of the rank
`n+1` quotient lies in some `E' i` (`exists_orbit'`). The termwise identity
`hterm` uses `Φ(lastRow ι(r)) = 1`, `det ι(r) = det r`, `W''(r) = W'(ι(r))` and
`|det r|^s = |det r|^((s - 1/2) - 1/2) · |det r|`, together with
`μ(E i) |det r| = C μ'(E' i)`.

## The p-adic specialization

`equalRankLastRowReduction` installs the topology, valuative relation and
local-field structure of `T`, the Hausdorff and second-countability
certificates `T.fieldT2`, `T.secondCountableTopology`, the published
`T.generalLinearT2Space`, `T.generalLinearLocallyCompactSpace` and
`T.generalLinearSecondCountableTopology` in ranks `n + 1` and `n + 2`, and
Borel σ-algebras on `F`, both general linear groups, both unipotent groups
and both quotients, exactly as in the statement. It then applies
`lastRowReduction` with

- `χ = T.normalizedAbsHom` and `abv = normalizedAbsoluteValue T` (they agree
  by definition);
- `vol = Measure.addHaar` on `F^(n+1)`, whose determinant rule is the
  published `HarmonicAnalysis.haarMeasure_map_matrix`, fed with the scalar
  rule `HarmonicAnalysis.padicScalarHaarScaling`;
- `μG = generalLinearHaar F.Carrier (n + 1)`,
  `μN = unipotentHaar F.Carrier (n + 1)`,
  `μG' = generalLinearHaar F.Carrier n`, `μN' = unipotentHaar F.Carrier n`
  (Haar and regular by the instances of `Measures`; right invariance is the
  statement's own instance hypotheses);
- `χ(det j) = 1` on `J`: `eq_one_of_isCompact` shows that the continuous
  character `T.determinantNorm (n + 2)` into `ℝ≥0ˣ`
  (`T.determinantNormContinuous`) is trivial on the compact subgroup `J`,
  because the image of a compact set is bounded and any value `> 1` would have
  unbounded powers in `J` (and similarly for inverses).

## Relation to the literature

The statement is derived from Jacquet, Piatetski-Shapiro and Shalika,
*Rankin–Selberg Convolutions* (1983), printed page 449, displays (1) and (3).
The Lean proof does not use the source's integration formula over
`N_(r-1) \ G_(r-1) × Z_r × K_r`. Instead it decomposes both quotients into
countably many compact open orbits and compares their masses through Haar
uniqueness on `N_(n+2)` in the coordinates `y(v) ι(u)`, as outlined in the
statement's intended route. The constant is
`c = κ μG(J) / (vol(Y₀) μG'(A))`, where `κ` relates the coordinate product
measure to `unipotentHaar F.Carrier (n + 1)`; the theorem asserts only that
`c > 0`.

The compact-character lemma `eq_one_of_isCompact` is imported from
[CompactNormCharacter](../../Topology/CompactNormCharacter.md).
Its declaration and proof retain their original namespace and meaning.
