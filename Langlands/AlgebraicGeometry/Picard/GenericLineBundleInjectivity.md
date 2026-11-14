# Line bundles over a valuation ring are determined by their generic fibre

Worker 386 wrote this internal module for Task 6296. It works in namespace
`Langlands.AlgebraicGeometry.Picard`, in every universe `u`. The main result is
`nonempty_iso_of_generic_iso`. It proves the uniqueness half of extending line
bundles from the generic fibre, using the published cocycle-gluing and
closed-fibre machinery.

## Gauge lemmas (namespace `CocycleGluing`)

`IsGauge g h a` is the published relation
`h i j = res(a i) * g i j * res((a j)⁻¹)` between two unit cocycles on a family
of opens `T`.

- `IsGauge.mul_compatible`: suppose `a` is a gauge from `g` to `h`, and `c` is a
  family of units on the `T i` whose restrictions agree on every overlap
  `T i ⊓ T j`. Then `fun i ↦ a i * c i` is also a gauge from `g` to `h`. The proof
  is a ring identity (`linear_combination`) using that the restrictions of `c i`
  and `(c j)⁻¹` multiply to `1`.
- `isGauge_of_pullback`: let `q : Y ⟶ X` be injective on the sections over every
  overlap `T i ⊓ T j`. If the images of the units `a i` under `q.app (T i)` form a
  gauge between the published pullback cocycles `pullbackCocycle q g` and
  `pullbackCocycle q h`, then `a` is a gauge from `g` to `h` on `X`. The proof
  applies the injectivity to the gauge identity on each overlap, rewriting `q.app`
  as `q.appLE` and using the published `appLE_res`.

## Setting

In section `Valuation`, `R` is an arbitrary valuation domain (`ValuationRing R`,
`IsDomain R`; any rank) and `K` is a supplied fraction field with its given
algebra structure. `p : X ⟶ Spec R` is smooth with geometrically connected
fibres. `q : Y ⟶ X` and `s : Y ⟶ Spec K` form a pullback square `H` of `p` along
`Spec (algebraMap R K)`; that is, `q` includes the generic fibre.

## Descending a generic gauge

`exists_isGauge_of_generic_isGauge` additionally assumes `p` is separated and
takes:

- a family of affine opens `T i` such that every pairwise intersection
  `T i ⊓ T j` meets the closed fibre;
- `AffineClosedFibreSectionProjectivity p`, the published hypothesis that the
  section algebras of affine opens meeting the closed fibre are projective
  `R`-modules;
- injectivity of `q.app U` for every open `U`;
- two unit cocycles `g`, `h` on the `T i`, and a gauge `b` between their generic
  pullbacks.

It concludes that some family `a` of units on the `T i` is a gauge from `g` to
`h`. Proof:

1. If the index type is empty the statement is trivial. Otherwise fix an index
   `i₀`. Separatedness makes the diagonal affine, so every `T i ⊓ T j` is affine.
2. The published `affineGenericUnitDecomposition_eq` writes `b i₀` as
   `affineGenericScalarRatio r d` times the image of a total unit `a₀` on `T i₀`,
   for nonzero `r, d ∈ R`. The decomposition is extracted inside the local algebra
   instances `affineSectionAlgebra` and `pullbackSectionAlgebra`.
3. The scalar ratios `ρ i := affineGenericScalarRatio r d` on all the `T i` agree
   on overlaps (`affineGenericScalarRatio_restrict`). So by
   `IsGauge.mul_compatible`, `β i := b i * (ρ i)⁻¹` is again a generic gauge, and
   `β i₀` is the image of `a₀`.
4. For each `i`, the gauge identity at `(i₀, i)` shows that the restriction of
   `β i` to `T i₀ ⊓ T i` is the image of the total unit
   `c i := (h i₀ i)⁻¹ * res(a₀) * g i₀ i`. This is a ring identity
   (`linear_combination`) using the published helper lemmas `res_app` and
   `appLE_res`.
5. The published `affineGenericUnitOfRestriction` then gives a total unit `α i`
   on `T i` whose generic image is `β i`. It uses that `T i₀ ⊓ T i` meets the
   closed fibre and that the sections over `T i` are projective.
6. `isGauge_of_pullback` descends the gauge `β` to the gauge `α` on `X`.

## Generic injectivity

`nonempty_iso_of_generic_iso` assumes in addition that `p` is universally closed
and separated. It takes the projectivity hypothesis, sectionwise injectivity of
`q`, and two locally free rank-one module sheaves `L`, `M` on `X` with an
isomorphism `ψ : q* L ≅ q* M`. It concludes `Nonempty (L ≅ M)`. Proof:

1. For each point `x` of the closed fibre `p.fiber (closedPoint R)`, choose an
   affine open `T x` containing its image in `X` on which both `L` and `M` have
   frames. Frames come from the published
   `OpenImmersionIdeal.exists_isFrameOn_of_isLocallyFreeRankOne`; the affine open
   comes from the affine basis, and the frames are restricted to it.
2. `iSup_eq_top_of_closedFibre_neighbourhoods` (this needs universal closedness)
   shows that the `T x` cover `X`. Each `T x` meets the closed fibre, so it
   contains the published `closedFibreGenericPoint p`
   (`closedFibreGenericPoint_mem`). That point lies in the closed fibre
   (`closedFibreGenericPoint_spec`), so every pairwise intersection meets the
   closed fibre.
3. The frames give transition cocycles `frameCocycle` and isomorphisms
   `frameIso : L ≅ glued (frameCocycle e he)` and similarly for `M`. Combining
   these with `ψ` and the published `pullbackIso` gives an isomorphism of the
   glued sheaves of the two pulled-back cocycles. `nonempty_iso_glued_iff` turns
   it into a generic gauge `b`.
4. `exists_isGauge_of_generic_isGauge` gives a gauge `a` on `X`, and
   `frameIso ≪≫ gaugeIso a ha ≪≫ frameIso.symm` is the required isomorphism.

## Provenance

The provenance is internal. The module composes published Library results: the
cocycle-gluing and gauge theory (`CocycleLineBundleGauge`,
`CocycleLineBundleFrame`, `CocycleLineBundlePullback`), local frames of rank-one
sheaves (`OpenImmersionIdealLocalFreeness`), the closed-fibre cover
(`ProperLocalClosedFibreCover`) and the scalar-unit decomposition over valuation
rings (`AffineGenericScalarUnits`, `AffineGenericUnitRestriction`). The
projectivity hypothesis is an explicit argument, not an instance or an axiom.
This is the classical fact that on a smooth proper scheme with geometrically
connected fibres over a valuation ring, the restriction of line bundles to the
generic fibre is injective. The module proves it by gluing data on a closed-fibre
cover, without divisors or regularity.
