# Actual torus/root model families inside zero-fixer models

Module `Langlands.BruhatTits.IntegralModels.OrderedIntegralOpenCellFamily`,
namespace `Langlands.BruhatTits.IntegralModels.OrderedIntegralOpenCell`.

Throughout, `F` is a nonarchimedean local field in universe `u`,
`K = inertiaFixedField F`, `O = fixedFieldIntegers F`, `G` an affine group scheme
over `K`, `C : MaximalUnramified.BuildingData F G`, `E : UnramifiedZeroDatum F G`,
`Ω` a subset of the apartment and `N` an integral model of `G` over `O` with

```text
N.integralPoints = E.zeroPoints ⊓ C.pointwiseFixer (C.apartmentMap '' Ω).
```

## Declarations

- `exists_integralSplitTorusData`: such an `N` contains an actual closed integral
  split torus `T : IntegralSplitTorusData N C.i`. The proof is that of the published
  `exists_unramifiedIntegralSplitTorusData`, with the one-fixer point identity
  replaced by the zero-fixer one: the published
  `map_characterValuationKernel_le_zeroPoints_inf_pointwiseFixer` puts `S(K)^1` into
  `N.integralPoints`, and `SplitTorusClosure.exists_isSplitTorus_genericTorusMap_eq_of_bounded`
  supplies the torus.
- `rootData`: for smooth `N`, nonempty `Ω` bounded under every real affine
  functional, a reference point `x` and a relative root `a`, the actual
  `RootFiltrationModelData` at depth `C.apartment.rootFixerDepth a x Ω` built from
  the published `IntegralSplitTorusData.rootModel` (the `SplitRoot` root group of
  `T`). Its point image is `N.integralPoints ⊓ U_a(K)`
  (`rootModel_integralPoints_eq`), which is the root fixer by
  `rootGroupPoints_inf_unramifiedZeroFixer_eq_rootFixer` and the filtration at that
  depth by `rootFixer_eq_filtration_of_bounded`.
- `family`: given in addition `hrep : (torusCentralizer C.i).IsRepresentedBy E.i`,
  geometric connectedness of `E.T`, an actual relative identity component
  `iH : H ⟶ (T.centralizerModel E.i hrep).group` of the published integral
  centralizer model, smoothness and geometric connectedness of `H`, and the point
  equation `htor` of its neutral model, the actual
  `TorusRootModelFamilyData C E x Ω N`. The torus model is the published
  `IntegralModel.neutralModel` of the centralizer model; its map to `N` is
  `iH` followed by the closed centralizer inclusion, whose generic square is
  obtained from `neutralGenericIso_hom` and the centralizer model map. The root
  models and maps are `rootData` and `IntegralSplitTorusData.rootModelMap`.
- `torusIwahori_le_characterValuationKernel`: `E.torusIwahori` has unit values
  under all rational characters for the normalized valuation of `K` (published
  `torusNormIwahori_le_characterValuationKernel` and equivalence of valuations).
- `map_mem_pointwiseFixer_of_mem_characterValuationKernel`: the image under `E.i`
  of a point of `E.T(K)^1` fixes the image of every apartment point. It transports
  the point to the centralizer datum of `C` along the isomorphism of the two
  representatives of `torusCentralizer C.i` and applies V 6
  (`IntegerValuationBuildingData.map_mem_oneStabilizer`).
- `torusIwahori_le_centralizerModel`: hence `E.torusIwahori` lies in the integral
  points of the centralizer model, which are the `E.i`-preimage of
  `N.integralPoints` (`centralizerModel_integralPoints_eq_comap`).
- `neutralCentralizer_integralPoints_eq`: assuming the published, unproved
  propositions `UnramifiedTorusConnectedBoundStatement` and
  `UnramifiedTorusIwahoriConnectedImageStatement`, the neutral model of the
  centralizer model has integral points exactly `E.torusIwahori`. The inclusion
  `≤` is the connected bound applied to this smooth model with geometrically
  connected fibres. For `≥`, the connected image statement gives a smooth
  geometrically connected model `W` mapping onto `E.torusIwahori`; the proved
  `smoothHomExtension` (through `exists_hom_of_map_integralPoints_le`) extends the
  map into the centralizer model, it factors through the identity component
  (`exists_hom_lift`), and `map_integralPoints_le_neutralModel` concludes. This is
  the argument of the published `unramifiedTorusIwahoriModelAssembly`.

## Provenance

The family is the one of Kaletha–Prasad (2023), 8.3.6 and the proofs of
Theorem 8.3.13 and Proposition 8.3.14, printed pp. 297–300 / PDF pp. 328–331
(`kaletha-prasad-2023-bruhat-tits-new-approach`): root groups of the integral
split torus inside the model, and the connected Néron model of `T` realized, as in
the proof of Proposition 8.2.4 (printed pp. 289–290 / PDF pp. 320–321), as the
relative identity component of the integral centralizer. The two torus inputs are
the published statements of KP Corollary B.8.7 with the argument of
Proposition B.8.8(3), and of Lemma B.3.1 with Definition 2.5.13; they are
premises here, not proved.
