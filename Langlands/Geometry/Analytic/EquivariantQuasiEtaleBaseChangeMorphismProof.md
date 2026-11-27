# Fixed-field base change of equivariant quasi-étale sites

The module `Langlands.Geometry.Analytic.EquivariantQuasiEtaleBaseChangeMorphismProof`
proves

```lean
theorem equivariantQuasiEtaleBaseChangeMorphism :
    EquivariantQuasiEtaleBaseChangeMorphismStatement.{u, v, z}
```

in the namespace `Langlands.Analytic.SaturatedAtlasPresentation.SpaceWithOperators`,
the statement of `Langlands.Geometry.Analytic.EquivariantQuasiEtaleBaseChangeMorphismStatement`.
Let `K` be a complete ultrametric normed field and `f : Y ⟶ X` a morphism of
spaces with operators over `K`: a continuous homomorphism `f.groupHom` from the
group of `Y` to the group of `X`, and a morphism `f.hom` of the underlying
Hausdorff analytic spaces compatible with the two actions. The functor
`quasiEtalePullbackFunctor f` from `EquivariantQuasiEtaleSite X.space` to
`EquivariantQuasiEtaleSite Y.space` restricts the action of an object `U → X`
along `f.groupHom` and takes its pullback along `f.hom`, with the diagonal
action. The theorem shows that this functor is representably flat and
continuous for `equivariantCompactProbeQuasiEtaleTopology X.space` and
`equivariantCompactProbeQuasiEtaleTopology Y.space`. The universes `u` (field),
`v` (spaces and atlas indices) and `z` (groups) are those of the statement;
the theorem is the fixed-field result `quasiEtalePullbackFunctor_morphismOfSites`
applied to each `K` and `f`.

Write `F` for `quasiEtalePullbackFunctor f`. For an object `U` of the site of
`X`, `quasiEtalePullbackProjection f U` is the first projection from `F U` to
`U` with the restricted action. By `isPullback_quasiEtalePullbackFunctor`, the
square formed by this projection, the structure maps of `F U` and `U`, and
`f.hom` is a pullback of the underlying analytic spaces.

## Naturality squares are pullbacks

`quasiEtalePullbackMap_isPullback` states that for every arrow `g : U ⟶ V` of
the site of `X` the square

```
F U --F g--> F V
 |            |
 v            v
 U  ---g--->  V
```

with the two first projections as vertical maps is a pullback of the
underlying analytic spaces. The square commutes by `pullback.lift_fst`. The
base-change square of `V` is a pullback. The composite of the two squares is
the base-change square of `U`, because the structure map of `F V` composed
with `F g` is the structure map of `F U`, and `g` composed with the structure
map of `V` is that of `U`. The cancellation lemma `IsPullback.of_right` then
shows that the naturality square is a pullback.

## Representable flatness and continuity

`quasiEtalePullbackFunctor_morphismOfSites` applies the general reduction
`GSpace.representablyFlat_and_isContinuous_of_isPullback_forget` with the
precoverages `equivariantCompactProbeQuasiEtalePrecoverage X.space` and
`equivariantCompactProbeQuasiEtalePrecoverage Y.space`, which generate the two
topologies. The reduction needs four inputs.

1. Every cospan in the site of `X` is completed by a square whose underlying
   analytic square is a pullback. This is the theorem
   `equivariantQuasiEtalePullbacks` of the module
   `Langlands.Geometry.Analytic.EquivariantQuasiEtalePullbacksProof`.
2. `F` sends such squares to squares with the same property. Let a square
   `p, q, g, h` in the site of `X` have a pullback as underlying analytic
   square. Pasting the naturality square of `p` above this square with
   `IsPullback.paste_vert` gives a pullback. By the naturality squares of `q`
   and `g`, it is the composite of the image square with the naturality
   square of `h`. That naturality square is a pullback, so `IsPullback.of_bot`
   shows that the image square is a pullback.
3. If the structure map of `U` is invertible, so is that of `F U`. After
   restriction of the action the structure map is still invertible, and a
   pullback of an isomorphism is an isomorphism (`IsPullback.isIso_snd_of_isIso`).
4. `F` sends generating coverings to generating coverings.

For the fourth input, `equivariantCompactProbeQuasiEtalePrecoverage_eq_of_comparison`
with `compactProbeQuasiEtaleHausdorffComparison K`, proved in the module
`Langlands.Geometry.Analytic.CompactProbeQuasiEtaleHausdorffComparisonProof`, replaces both
compact-probe precoverages by `equivariantQuasiEtalePrecoverage`, since every
object of an equivariant site has a Hausdorff underlying space. A family of
arrows into `U` is a covering of this precoverage when its underlying family
satisfies `HasQuasiEtaleChartNeighborhoods`: every point of `U` has a
neighbourhood that is a finite union of images of atlas chart domains under
arrows of the family. The private lemma `map_mem_quasiEtalePrecoverage` shows
that `F` preserves this condition.

## Chart neighbourhoods after base change

Let `R` be a covering of `U` and `x` a point of `F U`, and let `b` be the first
projection from `F U` to `U`. The covering condition at `b x` gives a finite
set `σ` of chart images whose union is a neighbourhood of `b x`. The space of
`F U` is weakly locally compact (`weaklyLocallyCompactSpace_localized`), so `x`
has a compact neighbourhood `N`.

Fix a member of `σ`: the image of the chart domain `C` of an object `V` under
an arrow `g : V ⟶ U` of `R`. The chart domain `C` is compact. The set `Z` of
pairs `(z, y)` with `z` in `C`, `y` in `N` and `g z = b y` is a closed subset of
`C × N`, hence compact. The naturality square of `g` is a pullback, and `g` is
quasi-étale by `EquivariantQuasiEtaleSite.quasiEtale_map_left`. So
`hasCompactPairPreimages_of_quasiEtale` shows that the points of `F V` whose
pair of images lies in `Z` form a compact set. The atlas charts of `F V` form
a net, so finitely many chart domains of `F V` cover this set. Their images
under `F g` are chart images of the arrow `F g` of `R.map F`.

These finitely many images cover `N ∩ b⁻¹(g C)`. Let `y` be a point of `N`
with `b y = g z` for some `z` in `C`. The private lemma
`exists_point_of_isPullback_of_quasiEtale` gives a point `t` of `F V` over `z`
and `y`. To prove it, `exists_compatible_localizedFieldPoints` lifts `z` and
`y` to field points over one complete algebraically closed extension of `K`
with equal images in `U`. Field points preserve pullbacks along quasi-étale
maps (`localizedFieldPoint_isPullback_of_quasiEtale`), so the pair of field
points comes from a field point of `F V`; its underlying point is `t`. The
point `t` lies in the compact set above, hence in one of the chosen chart
domains, and `y = (F g) t` lies in its image.

Taking all members of `σ` gives finitely many chart images whose union
contains `N ∩ b⁻¹(⋃ σ)`. This set is a neighbourhood of `x` because `N` is one
and `b` is continuous. So `R.map F` satisfies the chart-neighbourhood
condition at `x`.

## Sources

V. G. Berkovich, *Étale equivariant sheaves on p-adic analytic spaces*,
unfinished manuscript (1995–1996), §1.2, printed/PDF p. 3. A morphism
`ϕ : X′(G′) → X(G)` gives a morphism of sites `X′(G′)_qét → X(G)_qét`, and
the direct image of a sheaf `F′` takes the value `F′((X′ ×_X U)(G′))` on
`U(G)`. Literature ID
`provided-7bb3903652336bd799aad8853b8efd7ff3bcc0c7652745417f4745a14ac08e90`,
folder SHA-256 `e046cadfb9dcec4b0cf6624f80d6316bf532416153b82023f5100bd1ab0726cd`,
member `Berkovich--Etale equivariant sheaves on p-adic analytic spaces (unfinished manuscript)--1996.pdf`,
member SHA-256 `91567a75866a27cbe6690b6f075693df5afaa02524223d94d52ea37d77bb6637`.

V. G. Berkovich, *Vanishing cycles for formal schemes*, Invent. Math. 115
(1994), §3, printed p. 544 (PDF p. 6), defines the coverings of the
quasi-étale site by the neighbourhood condition on finite unions of images of
affinoid domains. Literature ID
`berkovich-1994-vanishing-cycles-formal-schemes`, SHA-256
`f4f7bc00cc46a0a5f72a69d7bbb220bce1d3ed9fd465aeda629f37dfc054bed1`.

The manuscript calls the morphism of sites evident and gives no proof. The
Lean proof checks the finite-limit conditions on underlying analytic squares
and the chart-neighbourhood condition with compact sets and field points.
