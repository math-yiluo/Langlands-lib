# Affine charts of geometrically irreducible curve families

Lean module: `Langlands.AlgebraicGeometry.LangWeil.CurvePlaneCharts`, namespace
`Langlands.AlgebraicGeometry.LangWeil.CurvePlane`.

Author: Worker 189. This module is a helper for the proof of
`Langlands.AlgebraicGeometry.LangWeil.FamilyCurvePlaneComparisonStatement` (Task 5581).
Provenance: internal. It transfers hypotheses of a morphism of schemes to the rings of its
affine charts and counts field-valued points by charts. No statement is a cited theorem.

Setting: `S` a scheme, `S₀` an affine open of `S` (`hS₀ : IsAffineOpen S₀`), `Y : Over S` with
structure morphism `Y.hom`. A chart `c : Chart S₀ Y` (Library module
`Langlands.AlgebraicGeometry.AffineChartPoints`) is an affine open `c.U` of `Y` lying over
`S₀`, with ring `c.Ring = Γ(Y, c.U)`, a `Γ(S, S₀)`-algebra. For a `Γ(S, S₀)`-algebra `C`,
`testObj hS₀ C` is `Spec C` as an object over `S`, and `c.pt hS₀ ψ` is the point of `Y`
defined by an algebra map `ψ : c.Ring →ₐ[Γ(S, S₀)] C`.

## Ring lemmas

- `ringKrullDim_eq_of_hasPureRingDimension`: a ring `T` with prime nilradical and pure
  dimension `d` (Library `HasPureRingDimension`: `T ⧸ q` has dimension `d` for every minimal
  prime `q`) has Krull dimension `d`. *Proof.* The nilradical is the only minimal prime, and
  `T ⧸ nilradical T` has the same prime spectrum as `T` (`ringKrullDim_quotient` and the zero
  locus of the nilradical is everything).
- `algHom_finite_of_finiteType`: there are finitely many `A`-algebra maps from a finite type
  `A`-algebra to a finite ring, since such a map is determined by the images of finitely many
  generators.

## Chart lemmas

- `chart_finiteType`: if `Y.hom` is locally of finite type, each `c.Ring` is a finite type
  `Γ(S, S₀)`-algebra (`HasRingHomProperty.appLE`).
- `chart_nilradical_isPrime`: if `Y.hom` is geometrically irreducible, `L` is a field with a
  `Γ(S, S₀)`-algebra structure and `L ⊗[Γ(S, S₀)] c.Ring` is nontrivial, then its nilradical
  is prime. *Proof.* By the Library equivalence
  `irreducibleSpace_pullbackSpec_iff_nilradical_isPrime` it suffices that the pullback of
  `Spec c.Ring → Spec Γ(S, S₀)` along `Spec L → Spec Γ(S, S₀)` is irreducible. The map of
  pullbacks induced by the open immersions `Spec c.Ring → Y` and `Spec Γ(S, S₀) → S` is an
  open immersion (`Scheme.pullback_map_isOpenImmersion`) into the pullback of `Y.hom` along
  `Spec L → S`, which is irreducible by Mathlib's `pullback_of_geometrically`. A nonempty open
  subspace of an irreducible space is irreducible; nonemptiness comes from
  `pullbackSpecIso` and nontriviality of the tensor product.
- `chart_hasPureRingDimension_fiber`: if `Y.hom` is locally of finite type and all its fibres
  over points of `S` have pure dimension `d`, then for every prime `p` of `Γ(S, S₀)` the fibre
  ring `p.ResidueField ⊗[Γ(S, S₀)] c.Ring` has pure dimension `d`. *Proof.* The Library
  property `PureFibreDimensionMorphismProperty d` holds for `Y.hom`, is preserved by
  precomposition with the étale map `Spec c.Ring → Y` (`pureFibreDimension_precomp_etale`) and
  descends along postcomposition with the étale map `Spec Γ(S, S₀) → S`
  (`pureFibreDimension_of_postcomp_etale`); then `hasPureDimension_specFiber_iff` turns the
  fibre condition at `p` into the ring statement.

## Counting points by charts: `card_points_bounds`

Let `κ` be a finite field with a `Γ(S, S₀)`-algebra structure, `Y.hom` locally of finite type,
`c i` (`i` in a finite type) charts covering `Y.hom⁻¹(S₀)`, `c₀` a chart, and `h i ∈ (c i).Ring`
with the principal open `D(h i)` of `(c i).U` contained in `c₀.U`. Then

`#(c₀.Ring →ₐ κ) ≤ #(testObj hS₀ κ ⟶ Y) ≤ #(c₀.Ring →ₐ κ) + Σᵢ #((c i).Ring ⧸ (h i) →ₐ κ)`.

*Proof.* The left inequality is injectivity of `c₀.pt` (`pt_injective`). For the right
inequality, the map from `(c₀.Ring →ₐ κ) ⊕ Σᵢ ((c i).Ring ⧸ (h i) →ₐ κ)` sending `ψ₀` to
`c₀.pt ψ₀` and `(i, ψ)` to `(c i).pt (ψ ∘ quotient map)` is surjective. Indeed a point `x`
has one-point source, whose image lies over `S₀`, hence in some `(c i).U`, so
`x = (c i).pt ψ` (`exists_pt`). If `ψ (h i) = 0`, `ψ` factors through `(c i).Ring ⧸ (h i)`.
Otherwise the image of `x` lies in `D(h i) ⊆ c₀.U` (`IsAffineOpen.fromSpec_preimage_basicOpen`)
and `x` comes from `c₀`. All sets involved are finite by `algHom_finite_of_finiteType` and
`chart_finiteType`; the count follows from `Nat.card_sum` and `Nat.card_sigma`.
