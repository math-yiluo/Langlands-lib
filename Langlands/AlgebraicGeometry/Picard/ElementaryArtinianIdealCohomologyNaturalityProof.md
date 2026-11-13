# Proof: naturality of elementary Artinian ideal cohomology in residue coordinates

Module `Langlands.AlgebraicGeometry.Picard.ElementaryArtinianIdealCohomologyNaturalityProof`.
Author: Worker 134.

The theorem
`Langlands.AlgebraicGeometry.Picard.ElementaryArtinianIdealCohomology.naturalityStatement`
proves the published proposition
`Langlands.AlgebraicGeometry.Picard.ElementaryArtinianIdealCohomology.NaturalityStatement.{u}`
exactly, for arbitrary elementary surjections `φ : R →+* S` of local Artinian
rings, every pair of flat proper `X, Y` over `Spec R`, every degree `n`, every
morphism `f : Y ⟶ X` and every compatible coefficient map `k`. No residue
splitting is assumed; `K = ResidueField S` and `s = residueBaseMap φ`.

## Inputs from the Library

- `exists_idealResidueProductIso` (module
  `...Picard.ElementaryArtinianIdealResidueProduct`, Workers 208/219): one finite
  index type `ι : Type u` and isomorphisms
  `e X : ideal φ X ≅ ∏ᶜ (fun _ : ι => residueModule φ X)` for all flat `X`, with the
  square `k ≫ f_*((e Y).hom ≫ π_j) = (e X).hom ≫ π_j ≫ residueCoefficient φ f`
  for every compatible `k`. Here `residueModule φ X` is the pushforward along
  `residueι φ X = pullback.fst X.hom s` of the structure sheaf of the residue fibre,
  and `residueCoefficient` is the functorial composite of `unitToPushforwardUnit`,
  `pushforwardComp` and `pushforwardCongr` (module
  `...Picard.ElementaryArtinianResidueCoefficient`).
- `canonicalPushforwardCohomologyMap` and its laws (module
  `...Modules.CanonicalPushforwardCohomology`, Worker 210): coefficient
  naturality, composition, factorization `relativeCohomologyPullback_coefficient`
  of canonical pullback with a coefficient map, and invertibility for closed
  immersions.
- `relativeCohomologyPullback_overMap` (module
  `...Modules.CohomologyPullbackBaseRing`, Worker 134): canonical pullback commutes
  with `relativeCohomologyBaseRingIso` when schemes over `Spec K` are regarded over
  `Spec R`.
- `finiteProductCohomologyIso` and `finiteProductCohomologyIso_apply`
  (`ArtinianResidueCohomology`), `FieldGlobalFunctions.pullbackUnitIso_unit`.

## Auxiliary lemmas in this module

- `canonicalPushforwardCohomologyMap_congr`: transport along equal morphisms by
  `pushforwardCongr` (proof by `subst`).
- `canonicalPushforwardCohomologyMap_eq_pullback_counit`: the canonical
  pushforward comparison is canonical pullback of `h_* N` followed by the counit.
- `canonicalPushforwardCohomologyMap_overMap`: base-ring compatibility of the
  canonical pushforward comparison, from the previous lemma,
  `relativeCohomologyPullback_overMap` and naturality of
  `relativeCohomologyBaseRingIso`.
- `residueOver φ X = (Over.map s).obj ((residuePullback φ).obj X)` and
  `residueιOver φ X : residueOver φ X ⟶ X` (the residue inclusion over `Spec R`);
  `residueιOver_naturality` is the residue square; `residueι_isClosedImmersion`
  (base change of the closed immersion `Spec K → Spec R`).
- `coordinateEquiv`: for one coordinate, the additive equivalence
  `H^n_R(X, residueModule φ X) ≃+ structureCohomology ((residuePullback φ).obj X) n`
  given by the invertible canonical comparison along `residueιOver φ X` followed by
  `relativeCohomologyBaseRingIso` for `residueRingHom φ : R → K`.
- `coordinate_square`: the morphism-level square
  `H(residueCoefficient f) ≫ cpc f ≫ cpc(ι_Y) ≫ B_Y = cpc(ι_X) ≫ B_X ≫ ρ(structurePull f_K)`.
  Proof: `canonicalPushforwardCohomologyMap_comp` for `ι_Y` and `f`, cancellation of
  `pushforwardComp`, `canonicalPushforwardCohomologyMap_congr` with the residue
  square, composition for `f_K` and `ι_X`, naturality for the unit
  `unitToPushforwardUnit f_K`, `canonicalPushforwardCohomologyMap_overMap`,
  naturality of the base-ring isomorphism, and finally
  `relativeCohomologyPullback_coefficient` over `K` with
  `pullbackUnitIso_unit`, which identifies the adjoint of `pullbackUnitIso` with
  `unitToPushforwardUnit`.
- `idealCoordinates`: `eX` is cohomology of `e X`, then
  `finiteProductCohomologyIso`, then `coordinateEquiv` in each coordinate, then
  reindexing along `ι ≃ Fin d` (`reindexAddEquiv`). `idealCoordinates_apply`
  computes coordinate `j` as `coordinateEquiv` of cohomology of
  `(e X).hom ≫ π_(eι.symm j)`.
- `idealPull_eq`: `idealPull φ f k n` is cohomology of `k` followed by
  `canonicalPushforwardCohomologyMap f`, by `relativeCohomologyPullback_coefficient`.

## Main proof

Obtain `ι`, `e`, the square from `exists_idealResidueProductIso`, put
`d = Fintype.card ι` and use `idealCoordinates` for `X` and `Y` with the same
`Fintype.equivFin ι`; these choices precede `f` and `k`. For given `f`, compatible
`k`, `x` and `j`, rewrite both coordinates with `idealCoordinates_apply` and the
pullback with `idealPull_eq`. The morphism identity `key` follows from coefficient
naturality of `canonicalPushforwardCohomologyMap f` for `(e Y).hom ≫ π_i`, the
published square for `k`, and `coordinate_square`. Evaluating `key` at `x` gives the
required coordinate equation; `structurePull` unfolds to the same canonical
pullback with `pullbackUnitIso`.

The theorem uses `set_option maxRecDepth 8192` for the final definitional
comparison. Axioms: `propext`, `Classical.choice`, `Quot.sound`. No Artinian or
field reduced-coproduct injectivity statement, primitive line-bundle lifting,
Picard-zero lifting, dual-scheme geometry or abelian representability result
occurs in the import closure.
