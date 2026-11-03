# Limits of actual points through the valuative criterion

This helper module of the proof of
`Langlands.AlgebraicGeometry.PointTopology.LocalFieldProperPointProperties`
contains one theorem, `exists_limit_of_valuationSubring`. It is the core of the
proof route, internal to this formalization: Conrad's Proposition 4.4 (printed
page 11 of *Weil and Grothendieck approaches to adelic points*) instead reduces to
projective space by Chow's lemma.

## Statement

Let `K` be a field with a topology, `IsTopologicalDivisionRing K` and
`T2Space K`. Let `f : X ⟶ Y` be a morphism in `Over (Spec K)` whose underlying
scheme morphism is quasi-compact and universally closed (so in particular any
proper `f.left`). Let `𝒰` be an ultrafilter on an index type `I`, `p` a family
of actual points `RingPoint K X K`, and `y : RingPoint K Y K` such that
`p i ≫ f → y` along `𝒰` in `schemePointTopology K Y K`. Suppose given

- a field `L` that is a `K`-algebra and a `K`-algebra map
  `G : (I → K) →ₐ[K] L` with `G g₁ = G g₂` whenever `g₁ = g₂` `𝒰`-eventually;
- a valuation subring `O` of `L` that is a `K`-algebra compatibly with `L`, and a
  `K`-algebra map `ρ : O →ₐ[K] K`;
- `hO`: if `g → c` along `𝒰` then `G g ∈ O`;
- `hρ`: if `a : O` has `a = G g` in `L`, then `g → ρ a` along `𝒰`.

Then there is `x : RingPoint K X K` with `x ≫ f = y` and `p i → x` along `𝒰` in
`schemePointTopology K X K`.

In the final proof `L` is the ultrapower of `K` along `𝒰`, `O` the subring of
germs of convergent families and `ρ` the limit map.

## Proof as implemented

1. `y` factors through an affine open `V` of `Y` (`exists_affineOpenPoint`);
   `exists_chart_family_of_tendsto` gives `V`-points `r i` over `p i ≫ f`
   eventually, with converging coordinates.
2. `exists_affine_eventually_factor` gives an affine open `W ≤ f⁻¹(V)` of `X` and
   (by `exists_family_of_eventually`) `W`-points `qW i` over `p i` eventually.
3. `zW` is the `L`-point of `W` with coordinates `germCoord G _ qW`. Since the
   coordinate families of `r` converge, `hO` makes `germCoord G _ r` take values
   in `O`; restricting the codomain gives a `K`-algebra map `H` and an `O`-point
   `wV` of `V`.
4. With `F : W ⟶ V` the restriction of `f` (`relativeOpenLift`), `zW ≫ F` and
   `wV` changed along `O → L` have the same coordinates: both are the germ of the
   coordinates of `r i` (`germCoord_comp`, `germCoord_congr`, and
   `qW i ≫ F = r i` eventually by injectivity of `openPointMap`). Hence the
   square `Spec L → X`, `Spec O → Y` over `f.left` commutes.
5. `UniversallyClosed.eq_valuativeCriterion` gives the existence part of the
   valuative criterion for `f.left`; applied to this `ValuativeCommSq` (Mathlib's
   instances make `O` a valuation ring with fraction field `L`), it yields
   `l : Spec O ⟶ X.left`, which is an actual point `lA : RingPoint K X O` with
   `lA ≫ f` the `O`-point of `Y` and `lA` changed to `L` equal to `zW`'s image.
6. Put `x = lA.changeRing ρ`. Then `x ≫ f = y`: on the chart `V` the coordinates
   of `wV.changeRing ρ` are `ρ (H b)`, which equal the coordinates of `y` by `hρ`,
   step 1 and uniqueness of limits in `K`.
7. `lA` factors through an affine open `U` (as `O` is local). The transfer lemma
   `germ_transfer`, applied to `zW` and the `L`-point of `U` obtained from `lA`,
   gives `U`-points `qU i` over `p i` eventually with coordinate germs equal to the
   coordinates of the `U`-point of `lA`, which lie in `O`. By `hρ` the coordinates
   of `qU i` converge to those of `x` on `U`, and `tendsto_schemePoint_of_chart`
   gives `p i → x`.
