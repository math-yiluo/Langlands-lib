# The full model at a special vertex and its cocharacters

This internal unit chooses the integral model whose congruence tower
`Langlands.BruhatTits.SpecialCompact.CongruenceBasis.Assembly` uses. It also
shows that every cocharacter of the maximal split torus lifts to that model.
Here `F` is a nonarchimedean local field with valuation ring `𝒪[F]` and `G`
is a group scheme over `F`.

## Results

- `exists_fullModelCocharacter`: let `D : RelativeComponentModelData 𝒪[F] F G`
  be a relative-component model datum. Let `T : IntegralTorusData D S i` be an
  integral torus datum over a torus `i : S ⟶ G`, and suppose its integral
  torus `T.torus` is split. Then for every cocharacter `y` of `S` there is a
  cocharacter `χ : 𝔾_m ⟶ D.full.group` of the full integral model with
  `D.full.genericCocharacter χ = groupHom y ≫ i`. The proof applies the
  published `IsSplitTorus.existsUnique_baseChangeCocharacter` to the split
  integral torus. This gives an integral cocharacter `ν` of `T.torus` whose
  base change is `groupHom y` transported through `T.genericIso`. The lift is
  `χ := groupHom ν ≫ T.inclusion ≫ D.inclusion.hom`. Its generic cocharacter
  is computed from the two published generic-fibre compatibilities
  `T.generic_comm` and `D.inclusion.generic_comm`.
- `exists_specialVertexModel`: **the full model at a special vertex.** Let
  `𝔅` be a KP assignment with `𝔅.IsAvailableFor F G hG`, and let `x` be a
  special vertex of the apartment of its base datum. Then there is an
  integral model `M : IntegralModel 𝒪[F] F G` with two properties:
  1. `M.integralPoints` is exactly `specialCompactSubgroup x`;
  2. for every cocharacter `y` of the maximal split torus `S` of the base
     datum, there is a cocharacter `χ` of `M.group` with
     `M.genericCocharacter χ = groupHom y ≫ i`.

  `M` is the full model of the assignment's model family at the vertex model
  index `vertexModelIndex` of the image of `x`. That index is the image of the
  singleton `{x}` under the identity translate of the apartment map.
  - Property 1 is the published `integralPoints_vertexModelIndex`
    (`IntegralModel.BuildingComparisonAssembly`). It is applied to the
    full-points clause `full_points` of the model axioms, which availability
    supplies as `h𝔅.bruhatTitsGroupSchemes` (KP Axiom 4.1.20).
  - Property 2 uses the torus clause `torus_clause` of the same axioms (KP
    Axiom 4.1.20(3)), applied at the presentation `1 · {x}`. It says the
    integral torus attached to that presentation is closed and split.
    `exists_fullModelCocharacter` then lifts each `y`. The torus inclusion of
    the presentation is `innerIso 1 ≫ i`. The published `innerIso_one_hom`
    reduces it to `i`.

Only the single-group availability `𝔅.IsAvailableFor F G hG` is used. Global
validity `𝔅.IsValid` implies it through the published
`KPBuildingAssignment.IsValid.isAvailableFor`.

The provenance is internal composition of the published model-family and
building-comparison results named above. The KP axioms enter only through the
Library's existing formalization of the assignment. No literature statement is
newly formalized here.
