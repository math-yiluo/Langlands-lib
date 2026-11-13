# Integral points of split reductive groups over strictly Henselian local domains

Module `Langlands.GroupScheme.Reductive.LocalSplitIntegralGeneration`, namespace
`Langlands.GroupScheme.LocalSplitCell`. It uses the vocabulary of the published
`LocalSplitCell` and `LocalSplitBigCellProof` modules: split tori
`splitTorus (Spec R) I`, root parametrizations `u α : Ga R ⟶ G`, and the big-cell map
`cellMap`.

## Declarations

* `generators i u` is a set of `R`-points of `G`, that is, of morphisms
  `𝟙_ (Over (Spec R)) ⟶ G.X`. It is the union of the images `t ≫ i` of the `R`-points `t`
  of the split torus and the root points `rootPoint (u α) (𝟙_ _) c`, over all roots `α` and
  all `c ∈ R`.
* `exists_lift_of_closedPoint_mem`: let `R` be a local ring and `f : Y ⟶ X` a morphism
  over `Spec R` whose underlying scheme morphism is an open immersion. An `R`-point `x` of
  `X` whose closed point lies in the range of `f` factors as `y ≫ f` for some `R`-point `y`
  of `Y`.
* `exists_rationalPoint_mem_inv_mul_mem`: let `H` be a smooth, affine, connected group
  scheme over a separably closed field `k`. Let `U` be an open set of `H` that contains the
  point of some rational point `u₀`. Then for every rational point `p` there is a rational
  point `q` such that the points of `q` and of `q⁻¹ * p` both lie in `U`.
* `orderedProduct_mem_closure` and `cellMap_mem_closure`: ordered products of root points,
  and composites `y ≫ cellMap i u neg pos` of `R`-points `y` of the cell source, lie in
  `Subgroup.closure (generators i u)`.
* `mem_closure_generators`, the main theorem. Let `R` be a Henselian local domain whose
  residue field is separably closed. Let `G` be a group scheme over `Spec R` with
  `IsAffineHom G.X.hom` and `IsReductive G`. Let `i : splitTorus (Spec R) I ⟶ G` be a
  closed subgroup that is a maximal torus on every residue-field fibre. Let `P` be a root
  datum with `IsFibrewiseRootDatumOf I G i P`, let `b` be a base, and let `u` be root
  parametrizations (`IsRootParametrization i (P.root α) (u α)` for every root `α`). These
  are exactly the hypotheses of the published `LocalSplitBigCellStatement`. Then every
  `R`-point `g` of `G` lies in `Subgroup.closure (generators i u)`.

## Implemented proof

*Factorization through an open.* Every point of `Spec R` specializes to the closed point
(`IsLocalRing.specializes_closedPoint`). The range of an open immersion is open and
therefore stable under generization. So the whole range of `x` lies in the range of `f`.
`IsOpenImmersion.lift` then gives the factorization; it is a morphism over `Spec R`
because `f` is.

*The field step.* `H` is irreducible: the published identity component
`identityComponent H` is irreducible, and its inclusion has range the connected component
of the identity (`range_identityComponentι`), which is everything because `H` is connected.
Put `ψ = (𝟙)⁻¹ * (toUnit ≫ p) : H.X ⟶ H.X`. On rational points `q ≫ ψ = q⁻¹ * p`, and
`W = ψ⁻¹(U)` is open. `W` contains the point of `p * u₀⁻¹`, whose image under `ψ` is
`u₀`. By irreducibility `U ∩ W` is nonempty. By the published density theorem
`hasDenseRationalPoints_of_smooth_of_isSepClosed` it contains the point of a rational
point `q`, which has the required property.

*Main theorem.* `hP.finite` gives finitely many roots. We enumerate the negative and the
positive roots and take the big cell `Ω = cellMap i u neg pos`. It is an open immersion
by the published `localSplitBigCell`, which applies because `R` is a reduced local ring.
Let `κ` be the residue field and `π = Spec.algebraMap R κ`.

1. Points over the residue field: `G_κ` is `GroupScheme.baseChange π` applied to `G`. It is
   smooth and affine, and it is connected because it is connected reductive, by
   `fieldReductive_of_residueReductive` and `IsReductive.isConnectedReductive_residueFiber`.
   The published `baseChangeBasePointsEquiv π G` identifies its rational points with the
   points `Over.mk π ⟶ G.X`. Restricting `R`-points along `Over.homMk π` is a group
   homomorphism `r`. The point of `r x` is the point of `x` at the closed point of `Spec R`,
   because `π` maps the closed point of `Spec κ` to the closed point
   (`IsLocalRing.comap_closedPoint`).
2. The open set `U` is the preimage, under the projection `G_κ → G`, of the range of `Ω`.
   It contains the point of the restriction of an `R`-point of `Ω`: we take the cell point
   built from the identity points of the three factors.
3. The field step, applied to `p = r g`, gives a rational point `q`. Its point lies over
   `Ω`, and so does the point of `q⁻¹ * r g`.
4. `q` factors through `Ω` over `κ` (`IsOpenImmersion.lift`). The cell source is smooth
   over `R`, since its structure map is `Ω` followed by the smooth structure map of `G`.
   The published Henselian lifting
   `HenselianSections.exists_section_of_smooth_of_surjective` therefore gives an `R`-point
   `σ` of the cell source restricting to it. Put `h = σ ≫ Ω`; then `r h = q`.
5. The restriction of `h⁻¹ * g` is `q⁻¹ * r g`, whose point lies over `Ω`. By the
   factorization step `h⁻¹ * g = y ≫ Ω` for some `R`-point `y` of the cell source.
6. The published `comp_cellMap` writes `y ≫ Ω` and `h` as products of ordered root-point
   products and a torus point. Hence both lie in the closure, and so does
   `g = h * (h⁻¹ * g)`.

## Provenance and scope

This is an internal unit. It proves the standard fact that a split reductive group over a
strictly Henselian local ring has its integral points generated by the integral points of
a split maximal torus and of the root groups. The argument "the closed fibre of
`Ω ∩ g Ω⁻¹` has a rational point, which lifts" is the usual big-cell argument (Conrad,
*Reductive group schemes*, around Theorem 5.1.13). It is carried out here with the
Library's big-cell theorem, the density of rational points on smooth varieties over
separably closed fields, and Henselian lifting of sections. No source statement is quoted.
The unit does not construct root parametrizations, frames or models.
