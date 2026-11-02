# Compact-open containment in actual dynamic unipotent radicals: proof

This module proves the published statement
[`DynamicUnipotentCompactOpenContainmentStatement`](CompactOpenContainmentStatement.md).
The final theorem is `Langlands.BruhatTits.dynamicUnipotentCompactOpenContainment`.

Let `F` be a nonarchimedean local field, `G` a connected reductive group scheme over
`Spec F`, and `χ : 𝔾_m ⟶ G` a cocharacter. Give `G(F)` the canonical rational-point
topology. Write `U = U_G(χ)(F)` for the rational points of the dynamic unipotent subgroup,
with the subspace topology. The theorem says that every compact subset `C ⊆ U` lies in a
compact open subgroup of `U`.

The mathematical result is Renard, *Représentations des groupes réductifs p-adiques*,
V.5.2(iii), whose source is cited in the statement's Markdown. The Lean proof follows the
usual contraction argument, written in coordinates:

1. `U` is closed in `G(F)`.
2. Conjugation by `χ(t)` acts on the coordinates of points of `U` by polynomials in `t`.
   The resulting map `(t, u) ↦ χ(t) u χ(t)⁻¹`, extended by `1` at `t = 0`, is continuous
   on `F × U`.
3. A tube-lemma argument then gives one `t ≠ 0` with `χ(t) C χ(t)⁻¹ ⊆ K₀`. Here `K₀` is a
   compact open subgroup of `G(F)`.
4. `K = U ∩ χ(t)⁻¹ K₀ χ(t)` is the required subgroup.

All auxiliary declarations are in `Langlands.BruhatTits.DynamicUnipotentContainment`.

## Imported results

- `Langlands.GroupScheme.Dynamic.AffineChart` describes any affine group scheme `G`
  through `B = Γ(G, ⊤)`:
  - `pointRing x : B ⟶ A` is the ring map classifying a point `x`.
  - `coaction χ : B ⟶ B[T, T⁻¹]` is the coaction of the conjugation orbit.
  - `counit G` classifies the identity.
  - `pointRing_laurentPoint_comp_orbit` computes the orbit of a point `x` as
    `coaction χ ≫ laurentCoeffMap (pointRing x)`.
  - `mem_unipotent_iff` describes membership in `U_G(χ)` by coefficients.
- `Langlands.BruhatTits.Unipotent.RationalPointCompactOpen` provides two facts about
  `G(F)`. It is a topological group (`rationalPoint_isTopologicalGroup`, from
  `RationalPointGroups`), and it has a compact open subgroup
  (`rationalPoint_exists_compactOpenSubgroup`, by van Dantzig). It also provides
  `localField_t2Space`.
- `Langlands.LocalField.NonzeroParameter.exists_nonzero_mem_of_mem_nhds_zero`: every
  neighbourhood of `0` in `F` contains a nonzero element.
- The point topology of `Langlands.AlgebraicGeometry.PointTopology`, through
  `rationalPointHomeomorph`, `affineSchemePointHomeomorph` and `AlgPoint.continuous_iff`.

## Coordinates

`pointRing_apply` shows that `pointRing x b` is the evaluation of `b` at `x` in the
published point topology, that is, at the image of `x` under `rationalPointEquiv` and
`affineSchemePointEquiv`. The proof unfolds `affineSchemeOverIso` to `isoSpec` and uses
`rationalPointEquiv_left`. Two consequences follow:

- `continuous_pointRing_apply`: each coordinate `x ↦ pointRing x b` is continuous on
  `G(F)`.
- `continuous_iff_pointRing`: a map `T → G(F)` is continuous exactly when all its
  coordinates are. The point topology is induced by the evaluations, and
  `AlgPoint.continuous_iff` gives this.

## Closedness of `U`

`unipotentPoints χ` is the subgroup `(unipotent χ).carrier (Over.mk (𝟙 (Spec F)))` of
`G(F)`, which is the `U` of the statement. `mem_unipotentPoints_iff` specializes
`mem_unipotent_iff` to the identity test object, using `Spec.preimage_id`. A point `x` is in
`U` exactly when:

- `pointRing x` kills every negative coefficient of every `coaction χ b`; and
- `pointRing x ((coaction χ b).coeff 0) = counit G b` for every `b`.

`isClosed_unipotentPoints` (for Hausdorff `F`) follows. Each condition is an equation
between a continuous coordinate and a constant, so `U` is an intersection of closed sets.

## Conjugation by `χ(t)` in coordinates

For `t ∈ Fˣ`, these are the constructions:

- `laurentEval t : F[T, T⁻¹] ⟶ F` evaluates at `t`.
- `laurentSection t` is the corresponding `F`-point of `Spec F[T, T⁻¹]`.
- `unitPoint t` is that point composed with `laurentPoint`: the point `(1, t)` of
  `Spec F × 𝔾_m`.
- `cocharPoint χ t = χ(t)` is `unitPoint t` followed by the projection and `χ`.

`unitPoint_comp_orbit` shows that composing the orbit of `x` with `unitPoint t` gives
`χ(t) x χ(t)⁻¹`. The orbit is `χ(t) · g · χ(t)⁻¹` evaluated at the two projections. The
first projection composed with `unitPoint t` is the identity, because maps into the terminal
object `Over.mk (𝟙 (Spec F))` are unique (`hom_overMkId_ext`).

`pointRing_conj` follows from `pointRing_laurentPoint_comp_orbit`, with
`Spec.preimage_map` giving the last step:

```text
pointRing (χ(t) x χ(t)⁻¹) = coaction χ ≫ laurentCoeffMap (pointRing x) ≫ laurentEval t.
```

The following definitions turn this into a polynomial in `t` for points of `U`:

- `degBound χ b` bounds the exponents in the support of `coaction χ b`.
  `coeff_eq_zero_of_degBound_lt` shows that coefficients beyond it vanish.
- `conjCoord χ b t x = ∑_{i ≤ degBound χ b} pointRing x ((coaction χ b).coeff i) · tⁱ` is
  defined for every `t ∈ F`, including `t = 0`.

`pointRing_conj_apply_of_mem`: for `x ∈ U` and `t ∈ Fˣ`, the coordinate `b` of
`χ(t) x χ(t)⁻¹` is `conjCoord χ b t x`. The Laurent polynomial
`laurentCoeffMap (pointRing x) (coaction χ b)` has no negative coefficients, because `x ∈ U`.
It is therefore the image of its truncation (`toLaurent_trunc`). Then `eval₂_toLaurent` and
`Polynomial.eval_eq_sum_range'` give the finite sum, with the degree bound from `degBound`.

`conjCoord_zero_of_mem`: for `x ∈ U`, `conjCoord χ b 0 x = counit G b`. Only the constant
term survives, and it equals `counit G b` by the second membership condition.

## The contraction map

`contraction χ : F × U → G(F)` is `(t, u) ↦ χ(t) u χ(t)⁻¹` for `t ≠ 0`, and `1` for
`t = 0` (`contraction_zero`, `contraction_of_ne_zero`).

`pointRing_contraction`: every coordinate of `contraction χ (t, u)` is
`conjCoord χ b t u`. For `t ≠ 0` this is `pointRing_conj_apply_of_mem`. For `t = 0` both
sides are `counit G b`: the identity has classifying map `counit G`, and
`conjCoord_zero_of_mem` gives the right side.

`continuous_contraction` (for a topological ring `F`): each `conjCoord χ b` is a finite sum
of products of continuous coordinates and powers of `t`, so it is continuous on
`F × G(F)` (`continuous_conjCoord`). The coordinates of `contraction χ` are these
functions composed with the continuous inclusion `F × U → F × G(F)`, so
`continuous_iff_pointRing` gives continuity.

## Moving a compact set into a compact open subgroup

`exists_conj_mem`: let `K₀` be an open subgroup of `G(F)` and `C ⊆ U` compact. Then some
`t ∈ Fˣ` satisfies `χ(t) u χ(t)⁻¹ ∈ K₀` for all `u ∈ C`.

- For each `u ∈ C`, `contraction χ (0, u) = 1 ∈ K₀`, and `K₀` is open. By continuity,
  `contraction χ` maps a neighbourhood of `(0, u)` into `K₀`.
- `IsCompact.eventually_forall_of_forall_eventually` (the tube lemma) gives a
  neighbourhood `V` of `0` in `F` with `contraction χ (s, u) ∈ K₀` for all `s ∈ V` and
  `u ∈ C`.
- `exists_nonzero_mem_of_mem_nhds_zero` gives a nonzero `t ∈ V`.
- `contraction_of_ne_zero` rewrites the contraction at `t` as conjugation by `χ(t)`.

`exists_compactOpenSubgroup`: assume `G` is affine and locally of finite type over `F`.
Every compact `C ⊆ U` lies in a compact open subgroup `K` of `U`.

- `G(F)` is a topological group, and `F` is Hausdorff. Choose a compact open subgroup `K₀`
  of `G(F)`, and `t` as in `exists_conj_mem`.
- Write `s = χ(t)`. Let `φ : U →* G(F)` be `u ↦ s u s⁻¹`, which is continuous, and let
  `K = K₀.comap φ`. It is an open subgroup of `U` and contains `C` by the choice of `t`.
- The image of `K` in `G(F)` is `(x ↦ s x s⁻¹)⁻¹(K₀) ∩ U`. The first set is compact,
  because `x ↦ s x s⁻¹` is a homeomorphism of `G(F)` and `K₀` is compact. Its intersection
  with the closed set `U` is therefore compact. `Subtype.isCompact_iff` transfers this back
  to `K`.

## The final theorem

`dynamicUnipotentCompactOpenContainment` proves the statement. After introducing `F`, `G`,
`hG` and `χ`, it installs the statement's instances: `IsAffineHom` from `hG.isAffineHom`,
then `IsAffine G.X.left` by `isAffine_of_isAffineHom`. Smoothness (`hG.smooth`) gives
`LocallyOfFiniteType G.X.hom` by instance search. The statement's topology on `G(F)` is
`rationalPointTopology F G.X`, the instance used throughout the module. `U` is
`unipotentPoints χ`. The goal is then exactly `exists_compactOpenSubgroup χ C hC`.

The proof uses only `propext`, `Classical.choice` and `Quot.sound`. Of the reductivity
hypothesis it uses only affineness and smoothness. The other fields of
`IsConnectedReductive` (connectedness and trivial geometric unipotent radical) are not
needed for this containment.
