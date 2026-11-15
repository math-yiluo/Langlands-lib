# The chart form of unitary root coordinates

This module works on rational points. Let `U = U_a` be a multipliable relative root group,
with Heisenberg normal form `N` (module `RootHeisenbergNormalForm`). Let `e` be weight vector
coordinates on the quotient `V = U / U_{2a}` and `e'` weight vector coordinates on
`U₂ = U_{2a}`. Every rational point of `U` is `incl(w) · sec(x)` for unique `K`-valued
coordinates `x` and `w`. Let `φ` be a homomorphism from the rational unitary parameters
`{(u, v) ∈ L² | v + σ(v) = u σ(u)}` of a quadratic extension `L / E` (with `K ⊆ E`) to `U(K)`.
Assume that `φ` is bijective, that it sends exactly the parameters with `u = 0` into `U₂`,
and that for every `c ∈ Kˣ` it intertwines the scaling `(u, v) ↦ (c u, c² v)` with the action
of a torus point whose root value is `c`. The main theorem says that `φ` then has the chart
form

`φ(u, v) = incl(B v + H(u, u)) · sec(A u)`

with `A`, `B` `K`-linear and `H` `K`-bilinear. Moreover `A` is bijective, and `B` is
bijective on the trace-zero elements `v + σ(v) = 0`. This chart form is the hypothesis of
`UnitaryChartUpgradeStatement` (module `RootHeisenbergUnitaryChart`, not imported here), which
upgrades such a `φ` to a homomorphism of group schemes.

Provenance: the module is internal. The unitary law `(u, v)(u', v') = (u + u', v + v' + u σ(u'))`
is that of Kaletha–Prasad, *Bruhat–Tits theory: a new approach* (2.7.2), and the coordinates
model `R_{E/K} U_{L/E} → U_a` of their Construction 2.9.16; these references are context only.
The proof uses the published modules `RootHeisenbergNormalForm` (normal form, cocycle
bilinearity `isBilinearVectorPairing_cocycle`, `exists_eq_mul_sec`, `act_sec`,
`act_inclusion`), `RootDoubleCommutatorPairing` (`commute_comap_double_of_noHigherRoots`),
`SU3RootParametersRational` (`rationalLift`, `traceOne`, `traceOne_add_conjugate`) and
Mathlib's `QuadraticMap.toBilin`.

The definitions `rationalVectorCoordinates` (the `K`-valued coordinates on `V(K)` read through
`Γ(Spec K, 𝒪) ≅ K`) and `HeisenbergNormalForm.chartPoint N e e' x w = incl(w) · sec(x)` are defined in the imported
module `Langlands.GroupScheme.Rational.RootHeisenbergChartPoints`. All declarations live in namespace
`Langlands.GroupScheme.RelativeRoot`.

## Vector coordinates

For natural coordinates `e : (T ⟶ V) ≃* Multiplicative (Fin n → Γ(T, 𝒪_T))` on a group scheme
`V` over `Spec K`:

- `vectorPoint e x` is the rational point with coordinates `x : Fin n → K`.
  `rationalVectorCoordinates_vectorPoint` and `vectorPoint_toAdd` say that it is inverse to
  `rationalVectorCoordinates e`. `vectorPoint_injective`, `vectorPoint_zero`,
  `vectorPoint_add` and `vectorPoint_eq_one_iff` give the additive structure.
  `toAdd_rationalVectorCoordinates` unfolds the coordinates.
- `vectorPoint_smul c x`: `vectorPoint e (c • x)` is read off from the coordinates over
  `Spec K` multiplied by the global section corresponding to `c`.
- `rationalCharacterEval_two_nsmul a t`: the value of `2 • a` at a rational torus point is the
  square of the value of `a`.
- `act_vectorPoint he t x`: if `e` are weight vector coordinates of weight `χ` for an action
  `b`, then `b.act t (vectorPoint e x) = vectorPoint e (χ(t) • x)`.

## The chart

The setting: `i : S ⟶ G`, a character `a`, representatives `j : U ⟶ G` of `subgroup i a` and
`j₂ : U₂ ⟶ G` of `subgroup i (2 • a)`, `C : DoubleRootCommutatorPairing i a hj hj₂`,
`N : HeisenbergNormalForm C`, and coordinates `e` on `C.V` (dimension `d`) and `e'` on `U₂`
(dimension `m`). Statements in namespace `HeisenbergNormalForm`:

- `chartPoint_def`: `N.chartPoint e e' x w = (vectorPoint e' w ≫ incl) * (vectorPoint e x ≫ sec)`.
- The imported `Langlands.Geometry.Building.HeisenbergUnitaryData.inclusion_comp_q`
  proves that `C.q` kills `incl`. The local `sec_comp_quotient` and
  `chartPoint_comp_quotient` show that `C.q` is a retraction of `sec` and sends
  `chartPoint x w` to `vectorPoint e x`.
- `chartPoint_injective`, `chartPoint_inj`: the chart is injective in `(x, w)`.
  `exists_eq_chartPoint`: every rational point of `U` is a chart point.
  `chartPoint_zero_zero`: `chartPoint 0 0 = 1`.
- `commute_inclusion hS ha hhigh w g`: points of `U₂` are central in `U` on every test scheme
  (for `G` affine and smooth, `S` a split torus, `a ≠ 0` and no relative roots `n • a` with
  `n ≥ 3`).
- `cocycleCoordinates e e' x y`: the cocycle `N.cocycle` of the normal form in `K`-valued
  coordinates. `chartPoint_mul`:
  `chartPoint x w * chartPoint x' w' = chartPoint (x + x') (w + w' + cocycleCoordinates x x')`.
- `act_chartPoint he he' t x w`: a torus point `t` with root value `c = a(t)` acts by
  `chartPoint x w ↦ chartPoint (c • x) (c² • w)`.
- `cocycleForm hS ha he he'`: `cocycleCoordinates` as a `K`-bilinear map
  (from `isBilinearVectorPairing_cocycle` on the test `Spec K`); `cocycleForm_apply` unfolds it.
- `chartFirst e e' g` and `chartSecond e e' g`: the chart coordinates `x` and `w` of a rational
  point `g` (chosen through `exists_eq_chartPoint`), with `eq_chartPoint`,
  `chartFirst_chartPoint`, `chartSecond_chartPoint`, `comp_quotient_eq`,
  `chartFirst_eq_zero_iff` (`chartFirst g = 0` iff `g ≫ C.q = 1`), `chartFirst_one`,
  `chartSecond_one`, `chartFirst_mul` (additive), `chartSecond_mul` (additive up to the
  cocycle), `chartFirst_act` (scaled by `a(t)`) and `chartSecond_act` (scaled by `a(t)²`).

## Main theorem

`exists_unitaryChartForm hS ha hhigh he he' φ hinj hsurj hcentral hscale`. Assume `G` affine
and smooth, `S` a split torus, `a ≠ 0`, no relative roots `n • a` with `n ≥ 3`, and weight
vector coordinates `e` (weight `a`, for `C.action`) and `e'` (weight `2 • a`, for the
conjugation action on `U₂`). Let `L / E` be a separable quadratic extension of fields over
`K`, with `L` finite-dimensional over `K`. Let
`φ : SU3Root.rationalParameters E L →* rationalPoints U` be a homomorphism with:

- `hinj`, `hsurj`: `φ` is bijective;
- `hcentral`: `φ p ≫ C.q = 1` if and only if `p.first = 0`;
- `hscale`: for every nonzero `c : K` there is a rational torus point `t` with
  `a(t) = c` and `t · φ(p) = φ(scale c p)` for all `p`, where `scale c (u, v) = (c u, c σ(c) v)`
  (`SU3Root.Parameters.scale` at `algebraMap K L c`).

Then there are `A : L →ₗ[K] (Fin d → K)`, `B : L →ₗ[K] (Fin m → K)` and
`H : L →ₗ[K] L →ₗ[K] (Fin m → K)` such that `A` is bijective, for every `w` there is a unique
`z` with `z + σ(z) = 0` and `B z = w`, and
`φ p = N.chartPoint e e' (A p.first) (B p.second + H p.first p.first)` for all `p`.

**Proof.** Write `X p = chartFirst (φ p)` and `W p = chartSecond (φ p)`, so that
`φ p = chartPoint (X p) (W p)`. Since `φ` is a homomorphism, `X` is additive and
`W(p q) = W p + W q + β(X p, X q)`, where `β = cocycleForm`. By `hcentral`, `X p = 0` exactly
when `p.first = 0`. By `hscale` and `chartFirst_act`/`chartSecond_act`, `X` scales by `c` and
`W` by `c²` under `scale c` (the case `c = 0` uses `scale 0 p = 1`). Hence `X p` depends only
on `p.first` (via `p⁻¹ q`), and `A u = X(rationalLift u)` is `K`-linear with
`A p.first = X p`.

For the second coordinate, put `B z = β(A(κ z), A 1) − β(A 1, A(κ z))`, with `κ = traceOne`
(`κ + σ(κ) = 1`); it is `K`-linear. For a central parameter `p = (0, z)`, the identity
`lift(κ z) · lift(1) = lift(1) · lift(κ z) · p` in the parameter group and the cocycle
rule give `W p = B z`. Writing a general `p` as `lift(p.first) · (lift(p.first)⁻¹ p)`, with
the second factor central, gives `W p = B p.second + Q p.first`, where
`Q u = W(lift u) − B (lift u).second`. Then `Q(c u) = c² Q(u)`, and
`Q(u + v) = Q u + Q v + β(A u, A v) − B(u σ(v))`, whose correction term is `K`-bilinear in
`(u, v)`. So `Q` is a quadratic map over `K`, and `H = Q.toBilin` for the basis
`Module.finBasis K L` satisfies `H u u = Q u` (`QuadraticMap.toQuadraticMap_toBilin`). This
gives the chart form. `A` is injective because `A u = 0` forces `u = 0`, and surjective
because `chartPoint x 0` lies in the image of `φ`. For `B`, the preimage of `chartPoint 0 w`
is a parameter `p` with `p.first = 0`, so `p.second` is trace-zero with `B p.second = w`.
Uniqueness follows from the injectivity of `φ` applied to `(0, z)` and `p`.
