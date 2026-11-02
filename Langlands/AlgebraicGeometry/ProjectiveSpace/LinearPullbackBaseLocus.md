# Base locus of pulled-back linear forms through a rational point

This module works over a field `K` with `ProjectiveSpace K m`. It combines the
two modules `RationalPointLinearForms` and `LinearSectionGenerationOpen`.

- `ProjectiveSpace.forall_linear_mem_iff_eq_section`: let
  `i : X ⟶ ProjectiveSpace K m` be injective on points, and let
  `σ : Spec K ⟶ X` satisfy `σ ≫ i ≫ projectiveSpaceToSpec K m = 𝟙`. For a point
  `y` of `X` the following are equivalent:
  - every linear form in the homogeneous prime of `i (σ pt)` is in that of
    `i y`;
  - `y = σ pt`.

  The proof applies `exists_linearCoordinates_of_section` to `σ ≫ i`, then
  `eq_of_forall_linear_mem`, then injectivity of `i`.
- `mem_trivializationOpen_isoPullbackSection_twistOne_iff`: pull the section
  `f / 1` of `𝒪(1)` back along `i` and transport it along any isomorphism
  `i^* 𝒪(1) ≅ N`. A point `x` lies in the generation open of the result iff
  `f ∉ (i x).asHomogeneousIdeal`.
- `linearPullbackSection i M eM h eN l` is a global section of `N`. It is built
  from a linear form `l`, a line bundle `M` on `X`, isomorphisms
  `eM : i^* 𝒪(1) ≅ M` and `eN : h^* M ≅ N`, and a morphism `h : Y ⟶ X`. To
  build it, pull `l / 1` back along `i` to `M` and then along `h` to `N`
  (`isoPullbackSection` twice).
- `mem_trivializationOpen_linearPullbackSection_iff`: `y` is in the generation
  open of that section iff `l ∉ (i (h y)).asHomogeneousIdeal`.
- `linearPullbackSystem i M eM h eN x₀` is the set of these sections for the
  linear forms `l` in the homogeneous prime of `i x₀`.
- `baseLocus_linearPullbackSystem`: assume `i` is injective on points and `σ`
  is a `K`-point of `X` over `K`. Take the points of `Y` that lie outside the
  generation open of every member of `linearPullbackSystem … (σ pt)`. They form
  exactly `h ⁻¹' {σ pt}`.

## Intended use and provenance

These are internal helper lemmas for the published target
`Langlands.AbelianScheme.PolarizedFiniteLevel.CubicTorsionHyperplaneBoundStatement`
(Mumford–Fogarty–Kirwan, GIT 3rd ed., Prop. 7.7). The planned instance has:
- `X` the abelian variety and `i` the supplied closed immersion;
- `σ` the identity section and `h` multiplication by `n`;
- `M` the cubic bundle and `N = M^(n·n)`, given by an isomorphism
  `[n]^* M ≅ M^(n·n)`.

Then the base locus of the linear system is the `n`-torsion `[n]⁻¹(0)`. This is
the system used in Mumford's proof of the proposition. The module proves only
these set-theoretic identities; it supplies neither the isomorphism
`[n]^* M ≅ M^(n·n)` nor the count.
