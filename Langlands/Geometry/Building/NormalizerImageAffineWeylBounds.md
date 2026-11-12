# The first sentence of AS 5 from AS 3, AS 4 and V 6

This internal helper module proves, for valuation building data
`B : ValuationBuildingData G` of a connected reductive group over a
nonarchimedean local field, the two inclusions in the first sentence of KP
Axiom 4.1.6, AS 5: the image of `N(F)` in the affine automorphisms of the
apartment contains `W(Ψ)` and lies in `W(Ψ)ᵉˣᵗ`. Here `Ψ` is
`B.affineRoots`. `ValuationBuildingData` includes V 6 on all of `Z(F)` for
its centralizer datum.

## Results

- `normalizerAffineEquiv_centralizer_mem_extendedAffineWeylGroup`: a point
  `z ∈ Z(F)` acts through `W(Ψ)ᵉˣᵗ`. Its action preserves `Ψ`
  (`KPApartmentData.normalizerAffineEquiv_mem_rootStabilizer`, from
  `NormalizerAffineRootAction`). By V 6
  (`KPApartmentData.IsOmegaCompatible.normalizerAffineEquiv_eq`) it is a
  translation, so its derivative is trivial.
- `range_le_extendedAffineWeylGroup_of_AS4`: under AS 4 the image of `N(F)`
  lies in `W(Ψ)ᵉˣᵗ`. Every `n ∈ N(F)` is a product `r z` with `r` in the
  reflection normalizer and `z ∈ Z(F)`
  (`ValuationBuildingData.exists_reflection_mul_centralizer`, from
  `ReflectionTranslationLattice`, with
  `reflectionRelativeWeylMap_surjective'` from
  `SimplyConnectedFacetFixingReduction`). By AS 4,
  `reflectionNormalizer_map_le_affineWeylGroup_of_AS4` (from
  `ReflectionNormalizerWeylAction`) places the action of `r` in
  `W(Ψ) ≤ W(Ψ)ᵉˣᵗ`. The previous result handles `z`.
- `affineWeylGroup_le_range_of_AS3`: under AS 3 the image of `N(F)` contains
  `W(Ψ)`. This is
  `affineWeylGroup_le_normalizerAffineEquiv_range_of_isAffineRootSystem` (from
  `NormalizerAffineRootAction`), with the opposite factor pairs
  `ValuationBuildingData.hasOppositeFactorPairs` (from
  `SimplyConnectedNormalizerAffineWeylAssembly`).

## Provenance

KP Axiom 4.1.6 and Remark 4.1.7 (Kaletha–Prasad, *Bruhat–Tits Theory: A New
Approach*, printed pp.159–160): AS 1–AS 4 already imply that the image of
`N(k)` contains `W(Ψ)` and lies in `W(Ψ)ᵉˣᵗ`. The implemented route uses AS 3,
AS 4 and V 6 together with the Library's description of `N(F)` as reflections
times `Z(F)`. It is derived from these Library results; no new source
assertion is used.
