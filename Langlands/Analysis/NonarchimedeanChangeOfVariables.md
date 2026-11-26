# Local change of variables for an invertible strict derivative

Module `Langlands.Analysis.NonarchimedeanChangeOfVariables`, namespace
`Langlands.Analysis`, universes `u`, `v`, `w`.

Over a nonarchimedean field, a map with an invertible strict derivative `L`
at a point `a` is, on every small closed ball about `a`, a bijection onto a
linear image of a ball. Its pushforward of additive Haar measure restricted
to such a ball equals the pushforward by `L`, restricted to the image ball.
This module states this law as a proposition, proves it, and specializes it
to finite coordinate spaces, where the factor is the inverse of a scalar
Haar scaling character evaluated at the determinant.

## The statement

`NonarchimedeanChangeOfVariablesStatement : Prop` (universe parameters
`u`, `v`, `w`, all free) quantifies over:

- a nontrivially normed field `K : Type u` (`NontriviallyNormedField K`);
- a normed space `X : Type v` over `K` (`NormedAddCommGroup X`,
  `NormedSpace K X`) whose distance is ultrametric (`IsUltrametricDist X`)
  and which is proper (`ProperSpace X`: closed balls are compact);
- a normed space `Y : Type w` over `K` (`NormedAddCommGroup Y`,
  `NormedSpace K Y`), with no further condition;
- Borel measurable structures on `X` and `Y` (`[MeasurableSpace X]
  [BorelSpace X] [MeasurableSpace Y] [BorelSpace Y]`);
- an additive Haar measure `μ` on `X` (`IsAddHaarMeasure μ`);
- a map `f : X → Y`, a point `a : X` and a continuous linear equivalence
  `L : X ≃L[K] Y`.

If `HasStrictFDerivAt f (L : X →L[K] Y) a` (Mathlib's strict derivative:
`f x - f y - L (x - y) = o(x - y)` as `x` and `y` tend to `a`), then there is
`R > 0` such that for every `r` with `0 < r ≤ R` (`r ∈ Ioc 0 R`):

- `BijOn f (closedBall a r) (L '' closedBall (L.symm (f a)) r)`: `f`
  restricted to the closed ball of radius `r` about `a` is a bijection onto
  the image under `L` of the closed ball of the same radius about
  `L.symm (f a)`;
- `(μ.restrict (closedBall a r)).map f = (μ.map L).restrict (f '' closedBall a r)`.

No characteristic, completeness or finite-dimensionality hypothesis is
placed on `K`; completeness of `X` follows from properness. The space `Y`
need not be ultrametric or proper: the balls in the conclusion are balls of
`X`, and the target ball is transported to `Y` by `L`. The theorem `nonarchimedeanChangeOfVariables` has the type
`NonarchimedeanChangeOfVariablesStatement.{u, v, w}` and is proved by
applying `local_map_restrict_eq_of_hasStrictFDerivAt`.

## The general theorem and its proof

`local_map_restrict_eq_of_hasStrictFDerivAt μ L hf` is the same law with the
data as arguments: `K X Y : Type*` with the instances listed above, an
additive Haar measure `μ` on `X`, and `hf : HasStrictFDerivAt f L a`.

The proof uses four private lemmas. The first, second and fourth take a map
`f : X → X`, a set `s`, a constant `c : ℝ≥0` with `c < 1`, and the
approximation hypothesis `ApproximatesLinearOn f (ContinuousLinearMap.id K X) s c`,
that is, `‖f x - f y - (x - y)‖ ≤ c ‖x - y‖` for `x, y ∈ s`. The third
involves no map; it assumes only that the measure is translation invariant.

- `dist_eq_of_approximatesLinearOn_id` (approximation hypothesis on `s`,
  `c < 1`): `f` preserves distances on `s`.
  For `x ≠ y` the error `f x - f y - (x - y)` has norm less than `‖x - y‖`,
  so by the ultrametric equality for summands of different norms
  (`IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm`)
  `‖f x - f y‖ = ‖x - y‖`.
- `surjOn_closedBall_of_approximatesLinearOn_id` (for complete `X`, the
  approximation hypothesis on `s = closedBall a r`, `c < 1` and `0 ≤ r`):
  `f` maps `closedBall a r` onto
  `closedBall (f a) r`. For `z` in the target ball, the map
  `g x = z - (f x - x)` is `c`-Lipschitz on `closedBall a r`. It maps that
  ball into itself by the ultrametric triangle inequality, because
  `dist (g a) a = dist z (f a) ≤ r`. Banach's fixed point theorem on the
  complete closed ball (`ContractingWith.exists_fixedPoint'`) gives `x` with
  `g x = x`, that is `f x = z`.
- `measure_closedBall_eq` (a measure `μ` on `X` with `IsAddLeftInvariant μ`;
  no map and no approximation hypothesis): for all `a b : X` and `r : ℝ`,
  `μ (closedBall a r) = μ (closedBall b r)`, since the translation
  `x ↦ (a - b) + x` has preimage of `closedBall a r` equal to
  `closedBall b r` (`measure_preimage_add`).
- `map_restrict_closedBall_of_approximatesLinearOn_id` (for proper `X`, a
  left-invariant measure `μ` that is finite on compact sets, `0 < R`,
  `c < 1`, and the approximation hypothesis
  `ApproximatesLinearOn f (ContinuousLinearMap.id K X) (closedBall a R) c`):
  `(μ.restrict (closedBall a R)).map f = μ.restrict (closedBall (f a) R)`.
  Both the approximation hypothesis and `c < 1` are needed: they give the
  first two lemmas on `closedBall a R`.
  Write `B = closedBall a R` and `D = closedBall (f a) R`. By the first two
  lemmas, `f` maps `B` isometrically onto `D`. The measure `μ.restrict B`,
  hence also its pushforward, is finite because `B` is compact. In an ultrametric space closed balls of
  positive radius are open (`IsUltrametricDist.isOpen_closedBall`), so they
  form a topological basis and generate the Borel σ-algebra. Two such
  balls are nested or disjoint (`IsUltrametricDist.closedBall_subset_trichotomy`),
  so they form a π-system. By `ext_of_generate_finite` it suffices to
  compare the two measures on these balls and on the whole space. Let a ball
  meet `D` at `f x` with `x ∈ B`; then the ball is `closedBall (f x) r`.
  If `r ≤ R`, its preimage in `B` is `closedBall x r` (distances are
  preserved) and it lies inside `D`, so both sides are the measure of a ball
  of radius `r`. If `r > R`, it contains `D`, its preimage contains `B`, and
  both sides are `μ B = μ D`. A ball disjoint from `D` has empty preimage in
  `B`, so both sides are zero. On the whole space both sides are
  `μ B = μ D`. The third lemma supplies the equal masses.

The theorem itself normalizes the derivative. The map `g = L.symm ∘ f` has
strict derivative the identity at `a` (`HasStrictFDerivAt.comp` with
`L.symm`). By `HasStrictFDerivAt.approximates_deriv_on_nhds` with `c = 1/2`,
it approximates the identity with constant `1/2` on a neighbourhood of `a`,
which contains `closedBall a R` for some `R > 0`. Fix `0 < r ≤ R` and put
`B = closedBall a r`, `D = closedBall (g a) r`, where `g a = L.symm (f a)`.
The first two lemmas show that `g` is a bijection from `B` onto `D`. Since
`f = L ∘ g` and `L` is injective, `f` is a bijection from `B` onto `L '' D`.
For the measure, `g` is replaced by the measurable function equal to `g` on
`B` and to `0` off `B`; it agrees with `g` almost everywhere for
`μ.restrict B`. Then

`(μ.restrict B).map f = ((μ.restrict B).map g).map L = (μ.restrict D).map L
= (μ.map L).restrict (L '' D) = (μ.map L).restrict (f '' B)`,

by `Measure.map_map`, the fourth lemma, `MeasurableEmbedding.restrict_map`
for the homeomorphism `L`, and `f '' B = L '' D`.

## Finite coordinates

`local_map_restrict_eq_inv_det_of_hasStrictFDerivAt` treats the coordinate
space `ι → K`. Its hypotheses are:

- `K : Type*` a nontrivially normed field whose absolute value is
  ultrametric (`IsUltrametricDist K`) and which is proper (`ProperSpace K`),
  with a Borel measurable structure (`[MeasurableSpace K] [BorelSpace K]`);
- a finite index type `ι` (`Fintype ι`, `DecidableEq ι`); the space
  `ι → K` carries Mathlib's sup norm and product measurable structure, so
  `closedBall` below is for the sup distance;
- an additive Haar measure `ν` on `K`, a map `χ : K →*₀ ℝ≥0` of monoids with
  zero, and the scalar law
  `hχ : ∀ z : K, z ≠ 0 → ν.map (fun x => z * x) = (χ z)⁻¹ • ν`;
- an additive Haar measure `μ` on `ι → K`;
- `f : (ι → K) → (ι → K)`, `a : ι → K`, `L : (ι → K) ≃L[K] (ι → K)` and
  `hf : HasStrictFDerivAt f L a`.

The conclusion: there is `R > 0` such that for every `r ∈ Ioc 0 R`,
`f` is a bijection from `closedBall a r` onto
`L '' closedBall (L.symm (f a)) r`, and

`(μ.restrict (closedBall a r)).map f =
(χ (LinearMap.det (L.toLinearEquiv : (ι → K) →ₗ[K] (ι → K))))⁻¹ •
μ.restrict (f '' closedBall a r)`.

Proof. Let `M = LinearMap.toMatrix' L`. Then `M.det = LinearMap.det L`
(`LinearMap.det_toMatrix'`), `Matrix.toLin' M = L`, and `M.det ≠ 0` because
`L` is a linear equivalence. The published theorem
`Langlands.HarmonicAnalysis.haarMeasure_map_matrix` of
`Langlands.HarmonicAnalysis.PadicRectangularHaarScalingProof`, applied to
`ν`, `χ`, `hχ`, `μ` and `M`, gives `μ.map L = (χ (LinearMap.det L))⁻¹ • μ`.
Its second countability hypothesis on `K` holds because `K` is proper. The
general theorem and `Measure.restrict_smul` give the claim.

The premise `hχ` is the scalar law taken by `haarMeasure_map_matrix`.
Over a nonarchimedean local field `F`, the published theorem
`Langlands.HarmonicAnalysis.generalScalarHaarScalingStatement` proves
`μ.map (fun x => (a : F) * x) = ((Shahidi.absUnits abv a : ℝ≥0)⁻¹) • μ`
for every unit `a`, every Borel measurable structure for the field's own
topology and every additive Haar measure `μ`, where `abv` is the
residue-normalized absolute value. Using it as `hχ` requires a nontrivially
normed field structure on `F` inducing that topology; this module does not
carry out that step.

## Provenance and scope

This is a derived helper, the nonarchimedean form of the local
change-of-variables formula for Haar measure. It follows from the
inverse-function-theorem estimate `HasStrictFDerivAt.approximates_deriv_on_nhds`,
Banach's fixed point theorem, the ultrametric inequality, uniqueness of
finite measures agreeing on a generating π-system, and the determinant
scaling theorem `Langlands.HarmonicAnalysis.haarMeasure_map_matrix`. No
external literature transcription is claimed.

The module proves no global change-of-variables formula and no formula for
integrals of functions. It does not identify `μ.map L` with a multiple of
`μ` outside finite coordinate spaces, and it constructs no scalar character
`χ`.
