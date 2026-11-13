# The split rank-one rational-orbit height bound

Author: Worker 10.

This module proves the published statement
`Langlands.Global.RepresentationGrowth.SplitRankOneParabolicRationalOrbitHeightBoundStatement`
(`Langlands/Global/AdelicSplitRankOneOrbitHeightBound.lean`) as the theorem

`Langlands.Global.RepresentationGrowth.splitRankOneParabolicRationalOrbitHeightBound :
  SplitRankOneParabolicRationalOrbitHeightBoundStatement.{u}`.

So, in universe `u`, take a number field `F` and a connected reductive `G`
over `F` with a maximal split torus `i : T ⟶ G` that is also a maximal torus.
Take a generic cocharacter `ν` with a single simple relative root `α`, a
finite-coordinate representation `ρ`, and a coordinate `j` whose exact line
stabilizer is `standardParabolic i ν ∅`. Then
`HasUniformNormOneRationalOrbitHeightBound F G ρ (Pi.single j 1)` holds: there
is `C > 0` such that every `g ∈ G(𝔸_F)¹` has a rational right translate
`g q` with `orbitHeight F G ρ e_j (g q) ≤ C`.

The proof uses the five supporting modules, in order:

- `SplitRankOneBinaryForm`
- `SplitRankOneCellPoints`
- `SplitRankOneCellData`
- `SplitRankOneFieldPoints`
- `SplitRankOneLocalBounds`

## Provenance

The statement is published; its Markdown gives the literature context
(Springer, *Reduction theory over global fields*, 1994, §§3.2–3.3). This
module and its helpers are an internal proof. They do not follow Springer's
route, which classifies split rank-one groups as `H × T` with
`H ∈ {GL₂, SL₂, PGL₂}` and treats each case. The route here is this:

1. On the orbit of the highest-weight line `e_j`, the rank-one subgroup acts
   through the binary form `ν(x) = ∑_{l ≤ k} x₀^(k-l) x₁^l w_l`. Here
   `xm(t) e_j = ν(1, t)`.
2. Every local point `g_v` acts on `ν` by a genuine similitude:
   `ρ(g_v) ν(x) = μ_v ν(h_v x)`, with `h_v ∈ GL₂(F_v)` and
   `(|μ_v|² |det h_v|^k)^d = |η(g_v)|²`.
3. The proof does not glue these exact similitudes. In general the identity
   data `h_v = 1`, `μ_v = 1` is not an exact similitude at almost all places.
   For example, take `G = SL₂` over `ℚ` with the standard representation and
   the upper Borel line `e_0`, so `k = 1` and `ν(X, Y) = (X, Y)`. The rational
   point `[[1, 1], [0, 1]]` sends `ν(0, 1) = (0, 1)` to `(1, 1)` at every
   place, so `h_v = 1`, `μ_v = 1` is an exact similitude for it at no place.
   Instead, at each place the proof chooses **local bound data** `(h_v, μ_v)`.
   These satisfy only the determinant-norm relation above and an upper bound
   `‖ρ(g_v) ν(x)‖ ≤ B_v |μ_v| ‖h_v x‖^k`.
   - At the good finite places, `ρ(g_v)` is integral and `|η(g_v)| = 1`.
     There the data are `h_v = 1`, `μ_v = 1`. The upper bound holds because
     an integral matrix does not increase the ultrametric norm. The relation
     holds because `|η(g_v)| = 1`. No action identity is claimed for them.
   - At the finitely many other places (all archimedean places and the bad
     finite places), the data are a genuine similitude from step 2. The upper
     bound then follows from the coefficient bound for `ν`.

   These data equal the identity at almost all places. Gluing gives an
   adelic matrix `h ∈ GL₂(𝔸)`.
4. The product formula on `G(𝔸)¹` gives `∏ |μ_v| · √|det h|^k = 1`.
5. The `GL₂` Hermite bound (`PrimitiveAdelicHeight.exists_rationalHeight_le_sqrt_det`)
   gives a nonzero rational `r` with `H(h r) ≤ C_H √|det h|`.
6. `ν(r)` is a nonzero multiple of a rational orbit point `ρ(q) e_j`. By the
   upper bounds its height is bounded by a constant.

## Definitions

- **`wbound D K`** (the record's declaration). For cell data `D` and a normed
  field `K ⊇ F`, `wbound D K = max(1, max_{l ≤ D.k} ‖w_l‖)`, where
  `w_l = wvec ρ j D.xm K l` are the binary-form coefficients over `K`.
- `finiteAlgHom v` and `infiniteAlgHom w`: the finite and infinite adelic
  projections, as `F`-algebra maps.
- `localPoint φ g`: the local point of an adelic point `g` along an
  `F`-algebra map `φ` out of the adeles.

## Local results

- `one_le_wbound`, `norm_wvec_le_wbound`, and `wbound_eq_one` (when all
  `‖w_l‖ ≤ 1`).
- `CellData.exists_local_similitude`: over a normed field `K ⊇ F` (with `F`
  infinite), every `K`-point `g` gives `h` and `μ ≠ 0` with `det h ≠ 0`,
  `(‖μ‖² ‖det h‖^k)^d = ‖η(g)‖²`, and
  `‖ρ(g) ν(x)‖ = ‖μ‖ ‖ν(h x)‖`. This applies `CellData.exists_similitude`.
  This is a genuine (norm) similitude.
- `CellData.exists_infinite_local`: the similitude data of
  `exists_local_similitude`, now with the upper bound
  `‖ρ(g) ν(x)‖ ≤ (k+1) · wbound · ‖μ‖ · ‖h x‖^k`. The theorem states only the
  relation and this bound.
- `CellData.exists_finite_local`: over an ultrametric `K`, local bound data
  `h`, `μ ≠ 0` with `det h ≠ 0`, the determinant-norm relation, and the upper
  bound `‖ρ(g) ν(x)‖ ≤ wbound · ‖μ‖ · ‖h x‖^k`. The theorem does not state an
  action identity. If all entries of `ρ(g)` have norm at most `1` and
  `‖η(g)‖ = 1`, the data are `h = 1` and `μ = 1`, and the bound comes from
  `norm_mulVec_le_of_norm_le_one` and `norm_nu_le_ultra`. These data are
  generally not a similitude of `ν` (see the `SL₂` example under Provenance).
  Otherwise the data come from `exists_local_similitude`.
- `eventually_norm_finiteProjection_le_one`: for finitely many adeles, almost
  all finite components are integral.
- `map_mulVec_rational`: algebra maps out of the adeles commute with matrix
  action on principal vectors.
- `affineMatrix_localPoint` and `etaUnits_localPoint`: the representation
  matrix and the character value of a local point are the local components of
  the adelic ones.
- `prod_mul_mul_pow_pow` and `prod_mul_mul_pow`: rearranging finite products.

## Gluing

`exists_adelicGL_of_local`: let `h_w ∈ M₂(F_w)` and `h_v ∈ M₂(F_v)` have
nonzero determinants at all places, with `h_v = 1` for almost all finite `v`.
Then there is `A : AdelicGL F 2` whose local components are these matrices.
The entries form a restricted product (`RestrictedProduct.mk`). The
determinant is a unit at every place and integral and a unit at almost all
places, so it is a unit of the adeles
(`RestrictedProduct.isUnit_of_eventually_isUnit`).

## Main theorem

`CellData.uniformBound`: for `G` connected reductive, `ρ` with `Fin n`
coordinates, and `D : CellData ρ j i α`, the conclusion
`HasUniformNormOneRationalOrbitHeightBound F G ρ (Pi.single j 1)` holds with

`C = (∏_w B_w^(mult w)) · (∏ᶠ_v B_v) · C_H^k`.

Here `B_w = (k+1) · wbound D F_w`, `B_v = wbound D F_v`, and `C_H` is the
`GL₂` Hermite constant. The finite product is a finite product, because
`B_v = 1` for almost all `v`. For `g ∈ G(𝔸)¹` the proof runs as follows.

1. Choose local bound data `(h_v, μ_v)` at every place
   (`exists_finite_local`, `exists_infinite_local`) for the local points of
   `g`. These satisfy the determinant-norm relation and the upper bound only;
   the proof uses no exact action identity. Let `x = η(g)` be the idele.
2. Since `g` has norm one, `|x| = 1`
   (`AdelicGroupPoints.mem_normOneSubgroup`, `IdeleAbsoluteValue.coe_full`).
3. For almost all `v`, `ρ(g_v)` is integral and `|x_v| = 1`. There the chosen
   bound data are `h_v = 1` and `μ_v = 1`. Glue the `h_v` into `A ∈ GL₂(𝔸)`.
4. The Hermite bound gives `r ≠ 0` with `H(A r) ≤ C_H √Δ`, where `Δ = |det A|`.
5. Let `S` be a finite set of places outside which every relevant local
   quantity equals `1`. Set `P = ∏_w |μ_w|^(mult w) · ∏_{v ∈ S} |μ_v|`.
   Raising the local relations to the `d`-th power and multiplying gives
   `(P² Δ^k)^d = |x|² = 1`. Since `d > 0` this gives `P² Δ^k = 1`, so
   `P · √Δ^k = 1`.
6. `CellData.exists_rational_orbit` gives a rational `q` and `c ≠ 0` with
   `ν(r) = c ρ(q) e_j`. The orbit height of `g q` is then the height of
   `ρ(g) ν(r)` (`orbitHeight_mul_rational`, `rationalHeight_smul`).
7. Bound the height place by place by `B_v · |μ_v| · ‖(A r)_v‖^k`. The result
   is at most `(∏ B_w^(mult w)) (∏ B_v) · P · H(A r)^k`, which is at most
   `(∏ B_w^(mult w)) (∏ B_v) · C_H^k · (P √Δ^k) = C`.

`splitRankOneParabolicRationalOrbitHeightBound` introduces the hypotheses of
the statement and obtains `D` from `nonempty_cellData` (`F` is infinite since
it has characteristic zero). It then applies `CellData.uniformBound`.
