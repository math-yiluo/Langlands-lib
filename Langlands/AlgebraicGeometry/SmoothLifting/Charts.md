# Lifts along a square-zero thickening, computed in affine charts

Namespace `Langlands.AlgebraicGeometry.SmoothLifting`. This module puts the
lifting problem of `SmoothThickeningLiftingStatement` into charts.

## Chart representatives

For an affine open `U` of a scheme `X` and a morphism `y : Spec R ⟶ X`
whose points all lie in `U`, `chartRep hU y h : Γ(X, U) ⟶ R` is the ring map
with `Spec.map (chartRep hU y h) ≫ hU.fromSpec = y` (`chartRep_spec`).

It is built from `IsOpenImmersion.lift` along `hU.fromSpec` (whose range
is `U` by `IsAffineOpen.range_fromSpec`) followed by `Spec.preimage`.
- `fromSpec_cancel` and `chartRep_eq` give uniqueness: `fromSpec` is a
  monomorphism and `Spec.map` is injective.
- `fromSpec_mem` says that every `Spec.map φ ≫ hU.fromSpec` lands in `U`.
- `chartRep_comp` says that representatives are natural in the ring.

`specMap_surjective` says that `Spec.map ε` is surjective on points when `ε`
is surjective with kernel in the nilradical. It uses
`range_comap_of_surjective`. `SqZero.le_nilradical` and `SqZero.isNilpotent`
connect this to square-zero ideals.

## The lifting data

Fix `f : X ⟶ S`, a ring `C` with an ideal `I`, and morphisms
`x₀ : Spec (C ⧸ I) ⟶ X` and `s : Spec C ⟶ S`. For a `C`-algebra `R`:
- `redIdeal I R = I R`;
- `redMap I R : R ⟶ R ⧸ I R` is the reduction map;
- `redStruct I R : C ⧸ I ⟶ R ⧸ I R` and `strMap R : C ⟶ R` are the
  structure maps.

`IsLift f I x₀ s R y` means that `y : Spec R ⟶ X` restricts to
`Spec.map (redStruct I R) ≫ x₀` on `Spec (R ⧸ I R)` and satisfies
`y ≫ f = Spec.map (strMap R) ≫ s`. For `R = C` this is the lifting problem
itself.

A `Chart f I x₀ s` bundles:
- affine opens `V ⊆ S` and `U ⊆ f ⁻¹ᵁ V`;
- an element `g : C` such that `s` maps the basic open of `g` into `V`, and
  `x₀` maps the basic open of the image of `g` in `C ⧸ I` into `U`.

When `g` becomes a unit in `R`, the following lemmas hold:
- `chart_x₀_mem`, `chart_s_mem`: the restrictions of `x₀` and `s` land in
  `U` and `V`.
- `chart_lift_mem`: every lift lands in `U`. Its reduction does, and
  `Spec (R ⧸ I R) → Spec R` is surjective on points.

## Chart description of lifts

- `Chart.θ = f.appLE V U _` is the chart ring map.
- `Chart.ψ R` is the chart representative of `s` on `R`, and `Chart.φ₀ R`
  that of `x₀` on `R ⧸ I R`.
- `Chart.θ_φ₀` is the compatibility `θ ≫ φ₀ = ψ ≫ redMap`, obtained from
  `x₀ ≫ f = Spec.map (mk I) ≫ s` and `IsAffineOpen.SpecMap_appLE_fromSpec`.
- `Chart.isLift_of_hom`: a ring map `φ : Γ(X, U) ⟶ R` with `θ ≫ φ = ψ` and
  `φ ≫ redMap = φ₀` gives the lift `Spec.map φ ≫ hU.fromSpec`.
- `Chart.rep`: conversely, a lift `y` has the representative
  `Chart.rep R hI hg y hy`, which satisfies `Chart.rep_θ` and
  `Chart.rep_red`.
- `Chart.rep_sub_mem`: representatives of two lifts differ by elements of
  `I R`.
- `Chart.exists_hom` gives local existence: `Γ(S, V) → Γ(X, U)` is smooth
  by `Smooth.smooth_appLE`, hence formally smooth, and
  `Algebra.FormallySmooth.liftOfSurjective` lifts `φ₀` through
  `R → R ⧸ I R`, whose kernel is nilpotent.
- `IsLift.restrict` and `Chart.rep_restrict` say that lifts and their
  representatives restrict along `C`-algebra maps `R → R'`.

## Affine combinations and chart independence

`Chart.comb` is the affine combination `y₀ + ∑ₖ cₖ (yₖ - y₀)` of lifts on
`R`. It is computed as `Spec.map (affComb …) ≫ hU.fromSpec` from their chart
representatives, and it is a lift (`Chart.comb_isLift`).

`Chart.comb_eq` is the key point: the combination is the same for any two
charts `ch`, `ch'` whose elements are both units in `R`. The proof uses the
fibre ring `P = fibreRing ι (I R)`:
1. The tuple maps of the representatives in the two charts give
   `Y, Y' : Spec P ⟶ X`.
2. The map `P → R ⧸ I R` is surjective with nilpotent kernel, and the
   composite of `Y'` with it is the restriction of `x₀`. So `Y'` lands in
   the first chart, and its representative there has the coordinates of
   the first chart's representatives.
3. By `fibreRing_hom_ext`, `Y' = Y`.
4. Both combinations are `Spec.map (fibreComb …)` followed by `Y = Y'`.

## Provenance

This is an internal formalization. The Stacks Project proof of Lemma
37.11.7 (Tag 02H6) lets the sheaf of local lifts act as a torsor under
`Hom(a*Ω, C_{T/T'})`. Here that torsor structure is only used through
affine combinations computed in charts. Chart independence is proved with
the fibre ring instead of a global sheaf of differentials. Worker 496 wrote
the Lean code and this description.
