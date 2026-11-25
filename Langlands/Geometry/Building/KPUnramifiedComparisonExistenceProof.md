# Existence of the unramified comparison of building data

`Langlands.Geometry.Building.unramifiedComparisonExistence` proves exactly
`Langlands.Geometry.Building.UnramifiedComparisonExistenceStatement.{u}`
at arbitrary universe `u`. It retains all hypotheses of the published statement:
a nonarchimedean local field `F` in either characteristic, an affine group scheme
`G` over `Spec F`, and `P : ParahoricBuildingData G` satisfying
`P.SatisfiesApartmentAxioms`. It adds no premise.

The implemented proof applies the published assembly theorem
`unramifiedComparisonExistence_of_fields` to six published proofs:

| Assembly input | Supplied theorem | Module |
| --- | --- | --- |
| Special torus containing `P.S` | `specialTorusExistence` | `SpecialTorusExistenceProof` |
| Descent of apartment valuations | `unramifiedValuationDescent` | `UnramifiedValuationDescentProof` |
| Root comparison | `unramifiedComparisonRootField` | `KPUnramifiedComparisonRootFieldProof` |
| Levi comparison | `unramifiedComparisonLeviField` | `KPUnramifiedComparisonLeviFieldProof` |
| Depth-zero comparison | `unramifiedComparisonZeroField` | `KPUnramifiedComparisonZeroFieldProof` |
| Openness | `unramifiedComparisonOpenField` | `KPUnramifiedComparisonOpenProof` |

## Construction of the witnesses

Write `K = UnramifiedClosure F`, definitionally `inertiaFixedField F`.
The assembly calls `exists_unramifiedApartmentLift` with the first two
theorems. This constructs a special torus `t : P.UnramifiedComparisonTorus`
and a lift `L : t.ApartmentLift`; neither is an additional hypothesis.

First, `specialTorusExistence` gives `T`, its closed inclusion `iT` in `G`,
and `f : P.S → T` factoring `P.i`, with `T_K` maximal split in `G_K`.
`UnramifiedBuildingDescent.exists_omegaCompatible`, using
`quasiSplitIntegerApartmentExistence` and
`unramifiedQuasiSplit_of_henselianDiscrete henselianDiscreteQuasiSplit`,
constructs the upstairs apartment class `D`, its centralizer datum `C`,
and their omega compatibility. `rootRankOneFactorization`, through
`RelativeRoot.hasRankOneFactorization_iff_hasOppositeFactorPairs`, supplies
the opposite-factor property needed for restriction of valuations.

Next, `unramifiedValuationDescent` constructs a downstairs compatible class:
its members are exactly the restrictions of coefficient-fixed points of
`D`, restriction is injective on those points, and the normalizer action is
compatible in the reduced building. `omegaCompatibleApartmentUniqueness`
identifies this class with the supplied `P.apartment`.
`UnramifiedBuildingDescent.descentPoint` then chooses `L.e`.
Its fixedness, restriction identity and normalizer compatibility are
`descentPoint_fixed`, `descentPoint_val` and `descentPoint_normalizer'`.

The existential witnesses in the target are precisely
`B = L.buildingData`, `hZ = L.centralizer_isTorus` and `e = L.e`.
Here `B` retains `T_K`, `iT_K`, `D`, `C` and omega compatibility;
`connectedReductiveFieldExtensionStatement` supplies connected reductivity
of `G_K`. The torus proof `hZ` follows from quasi-splitness of `G_K` and
`isTorus_of_quasiSplit_torusCentralizer`, using
`quasiSplitTorusCentralizerExistence` and `maximalSplitTorusConjugacy`.
Thus these are actual building data and actual Moy–Prasad groups for the
scalar extension of `G`.

## The comparison fields

The assembly constructs `P.IsUnramifiedComparison B hZ e` field by field.
All four field theorems apply to the same constructed `t` and `L`.

| Field | Implemented justification |
| --- | --- |
| `apartmentMap_smul` | `L.normalizer`, furnished by `descentPoint_normalizer'`, gives the required equality in the upstairs reduced building for every downstairs normalizer point. |
| `rootComparison` | `unramifiedComparisonRootField F G P hP t L` gives `Ψ`, `ν` and all seven root fields for each downstairs relative root. The witnesses and fields are described below. |
| `levi` | `unramifiedComparisonLeviField F G P hP t L` chooses a generic integral downstairs cocharacter and descends its real vector upstairs. `L.centralizer_mem_pairingLeviSpan_descent_tmul` gives centralizer containment; `L.exists_generic_levi_geometry` gives valuation constancy on the zero-pairing roots, using the fact that differences of fixed points are descended vectors. |
| `comap_zero` | `unramifiedComparisonZeroField F G P hP t L` identifies the double preimage of the actual norm-defined depth-zero group with `P.centralizerZero`. It constructs `UnramifiedZeroDatum.ofConnectedReductive`, rewrites by `zeroPoints_inf_fixer_eq_moyPrasad_of_sharpComparison` with `unramifiedZeroFixerSharpComparison`, and applies `L.comap_zeroPoints_inf_fixer`. |
| `isOpen` | `unramifiedComparisonOpenField F G P hP t L` uses `isOpen_localTorusFiltration` and `MaximalUnramified.BuildingData.isOpen_moyPrasad_of_isOpen_torus` for upstairs openness, then `ParahoricBuildingData.isOpen_unramifiedCentralizerComap`. The latter takes continuous preimages along the actual centralizer inclusion and rational extension. The resulting topology is exactly `rationalPointTopology F P.centralizer.Z.X`, at every nonnegative depth including zero. |

For `rootComparison`, the published root theorem is
`unramifiedComparisonRootField_of_doubledRootDepthModel
unramifiedDoubledRootDepthModel`. For a relative root `a`, its reduction
chooses `Ψ = L.rootFiber a`, the upper roots restricting to positive
integral multiples of the base-changed character `a`. It chooses a lower
integral cocharacter `ζ` with positive pairing against `a`, and takes
`ν` to be the descent of `(1 : ℝ) ⊗ₜ[ℤ] ζ`.
`L.exists_rootComparison_of_rootFiberBlockDescent` assembles:

| Root field | Library proof |
| --- | --- |
| `closed` | `L.rootFiber_closed a` |
| `pos` | `L.rootFiber_pos a` at the chosen vector |
| `root_mem` | `L.root_mem_rootFiber a` |
| `neg_mem` | `L.neg_mem_negativePairingRoots a` at the chosen vector |
| `levi_mem` | `L.centralizer_mem_pairingLeviSpan_descent_tmul ζ` |
| `filtration_mem` | `L.filtration_mem_rootFiber`, comparing multiplier-scaled upper depths with the required uniform nonnegative depth |
| `block_mem` | `L.hasRootFiberBlockDescent_of_doubledRootDepthModel`, supplied with `unramifiedDoubledRootDepthModel` |

For the last field, if `2a` is not a root,
`L.block_mem_rootFiber_of_not_double` gives the first lower factor and the
identity gives the second. Otherwise the published model theorem supplies
the smooth connected integral doubled-root model at depth `2r`.
`L.block_mem_rootFiber_of_doubledRootModel` descends the corrected factors
and yields `U_(a,y,r) U_(2a,y,r)`. Both lower factors retain the same uniform
depth `r`, also at zero. No model proposition remains as a premise.

## Provenance

This proof is a derived composition of the named Library constructions and
proofs. It changes neither the target pair nor any pair imported by that
target. Its source motivation is Kaletha–Prasad, *Bruhat–Tits Theory: A New
Approach* (2023), Construction 9.6.1, Lemma 9.6.3 and Theorem 9.6.5
(printed pp. 365–366, PDF pp. 396–397), §9.8.2 and Proposition 9.8.3
(printed pp. 375–376, PDF pp. 406–407). The depth-zero field uses the
comparisons associated with Definition 2.6.23(2), Corollary 9.7.3 and
Lemma 9.8.1, as explained in its proof module.

The registered source is `kaletha-prasad-2023-bruhat-tits-new-approach`,
SHA-256 `05ad9a284a2577b34d1a270228b74dfb28f520561ae7772d8f38dddb78938732`.
The registered `kaletha-prasad-2024-corrections`, SHA-256
`23293f51e58d5ceecb91f834743f68058b98431797d2531142415d013fdf61ed`,
PDF p. 41, corrects the projection domain in the proof of Lemma 9.8.1 to
`B(G)_M`. The implemented comparison uses the fixed apartment lift and the
named field proofs, without asserting a projection from all of `B(G)`.
