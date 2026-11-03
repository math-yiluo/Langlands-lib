# Chart lemmas for limits of actual scheme points

This helper module of the proof of
`Langlands.AlgebraicGeometry.PointTopology.LocalFieldProperPointProperties`
collects the chart-level facts about families of actual relative points used by
the valuative-criterion argument in `LocalFieldProperPointLimits`. All points are
the Library's actual relative points `RingPoint K X S` (morphisms
`ringTest K S ⟶ X` in `Over (Spec K)`), the scheme topology is the Library's
`schemePointTopology`, and affine coordinates are taken with the Library's
`affineSchemePointEquiv`. The content is internal to the chosen proof route; it is
not taken from Conrad's paper.

## Families

`exists_family_of_eventually`: if along a nontrivial filter `l` eventually some
`b` satisfies `P i b`, then there is one function `F` with `P i (F i)` eventually.
(Choice on the set where a witness exists, a fixed witness elsewhere.)

## Charts and convergence

Here `K` is a field. The first result assumes a topology on `K`; the second also
assumes `IsTopologicalDivisionRing K` and `T2Space K`; the third assumes no
topology on `K`.

- `tendsto_schemePoint_of_chart`: for an affine open `U` of `X`, if the points
  `p i` eventually equal `openPointMap K X K U (q i)` and every coordinate of
  `q i` converges to the corresponding coordinate of a point `x` of `U`, then
  `p i` converges to `openPointMap K X K U x` in `schemePointTopology K X K`.
  Proof: the affine point topology of `U` is induced by evaluation of coordinates
  (`affineSchemePointHomeomorph`, `AlgPoint.isEmbedding_evaluation`), so `q i → x`;
  the chart map is continuous (`schemePointTopology_continuous_chart`).
- `exists_chart_family_of_tendsto`: if `p i` converges in
  `schemePointTopology K Y K` to `openPointMap K Y K V y` for an affine open `V`,
  then there is a family `r` with `openPointMap K Y K V (r i) = p i` eventually,
  whose coordinates converge to those of `y`. Proof: the chart is an open
  embedding (`isOpenEmbedding_schemeAffineChart`), so `p i` is eventually in its
  range and the chart lifts converge to `y`; coordinates are continuous.
- `exists_affine_eventually_factor`: let `f : X ⟶ Y` have quasi-compact
  underlying morphism, `V` an affine open of `Y`, and `𝒰` an ultrafilter of
  indices along which `p i ≫ f` eventually factors through `V`. Then there is an
  affine open `W` of `X` with `W ≤ f.left ⁻¹ᵁ V` through which `p i` eventually
  factors. Proof: the images of the closed point of `Spec K` lie eventually in the
  quasi-compact set `f⁻¹(V)`, so the image ultrafilter converges in the Zariski
  topology to some `ξ ∈ f⁻¹(V)` (`IsCompact.ultrafilter_le_nhds`); take an affine
  open neighbourhood `W ⊆ f⁻¹(V)` of `ξ`; a point over the local ring `K` factors
  through an open containing the image of the closed point
  (`range_subset_open_iff_closedPoint`).

## Basic opens

Here `K` is a field, `Z` is an object of `Over (Spec K)` with affine underlying
scheme, and points take values in an arbitrary commutative `K`-algebra `S`.
For `g` in the coordinate ring of `Z`, local instances record
that the basic open `D(g)` (as `openOver K Z (Z.left.basicOpen g)`) is affine with
coordinate ring the localization away from `g` (`Γ_restrict_isLocalization`), as in
the Library module `AffineOpenPoints`.

- `basicOpen_coord_openPointMap`: coordinates of `d ≫ (D(g) ⟶ Z)` are those of
  `d` restricted along the localization map.
- `exists_basicOpen_lift`: a point of `Z` whose coordinate at `g` is a unit
  factors through `D(g)` (via `AlgPoint.range_precomp_localization`).
- `isUnit_basicOpen_coord`: a point factoring through `D(g)` has unit coordinate
  at `g`.

## Coordinate germs

Fix a commutative `K`-algebra `L` and a `K`-algebra map `G : (I → K) →ₐ[K] L`.

- `germCoord G Z q` (definition): for a family `q : I → RingPoint K Z K` of
  points of an affine `Z`, the `L`-valued algebra point
  `a ↦ G (fun i => coordinate of q i at a)`; `germCoord_apply` is its formula.
- `germCoord_congr`: if `G` identifies functions agreeing eventually along a
  filter, families agreeing eventually have equal coordinate germs.
- `germCoord_comp`: precomposing a coordinate germ with the coordinate pullback of
  a morphism `F : Z ⟶ Z'` of affine schemes gives the germ of `q i ≫ F`.

## Transfer of germs

In this section `L` is a field with a `K`-algebra structure, `G` is as above,
`𝒰` is an ultrafilter on `I`, and `G` identifies functions agreeing
`𝒰`-eventually (hypothesis `hG`).

- `germCoord_basicOpen`: for an affine `Z`, `g` in its coordinate ring, a family
  `q` of `K`-points of `Z`, and an `L`-point `zD` of `D(g)` whose image `z` in `Z`
  has coordinate germ `germCoord G Z q`: if `d` is a family of `K`-points of `D(g)`
  lying `𝒰`-eventually over `q`, then `zD` has coordinate germ
  `germCoord G _ d` (both sides agree on the image of the coordinate ring of `Z`,
  using `hG`; `IsLocalization.algHom_ext`).

`germ_transfer`: let `W`, `U` be affine opens of `X`, `qW` a
family of points of `W` lying eventually over `p i`, `zW` the `L`-point of `W`
with coordinate germ `germCoord G _ qW`, and `zU` an `L`-point of `U` with the
same image in `X`. Then there is a family `qU` of points of `U` lying eventually
over `p i` with `zU` having coordinate germ `germCoord G _ qU`.

Proof as implemented: the image of the closed point under `zW` lies in
`W ∩ U`; choose a basic open `D(g)` of `W` contained in `W ∩ U` and containing it
(`IsAffineOpen.exists_basicOpen_le`). Then `zW` factors through `D(g)`, so its
coordinate at `g`, the germ of the coordinates of `qW i` at `g`, is a unit, hence
nonzero; since `𝒰` is an ultrafilter and `G` kills eventually-zero functions, the
coordinates of `qW i` at `g` are eventually nonzero, so `qW i` eventually factors
through `D(g)` (`exists_basicOpen_lift`). Composing with the inclusion
`D(g) ⟶ U` (`relativeOpenLift`) gives `qU`; the germ identity follows from
`germCoord_basicOpen` and `germCoord_comp`.
