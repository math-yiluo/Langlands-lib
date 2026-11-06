# Every actual geometric CM transporter as a finite-etale cover

This internal development applies the arbitrary-transporter geometry of
`HarrisTaylorCMTransporterEtale` to the existing geometric tower
`cmGeometricSchemeTower ... q`. It retains the original arithmetic,
tensor, Picard, duality, polarization, torsion, exact representability,
rigidity and dominant-criterion inputs. It asserts no new theorem from
external literature.

For every actual arrow `k : V ⟶ U` between small CM levels, the published
`cmGeometricSchemeTower_map_isPullback` identifies its geometric tower
map with the base change of the original chosen tower map. The square
uses the original natural transformation `cmGeometricProjection`.
It does not replace the tower or any of its maps.

`cmGeometricSchemeTower_map_surjective` transfers surjectivity of the
original chosen map across this square. This result requires the named
`RelativeDualSchemeExistenceStatement` and
`RelativeDualSchemeGeometryStatement`, together with the original
parameters and exact representability witness `q`. It needs neither
rigidity nor the dominant criterion.

For the remaining results, rigidity is supplied at every small level as
`∀ U : SmallCMLevel D, CMGeometricCoarseRigidity ... U.obj`, and
`DominantUnramifiedEtaleStatement` remains explicit.
`cmGeometricSchemeTower_map_etale_of_dominantCriterion` and
`cmGeometricSchemeTower_map_isFinite_of_dominantCriterion` transfer
etaleness and finiteness of the original transporter across the same
square, by stability under base change.

`cmGeometricFiniteEtaleTransition_of_dominantCriterion` places that
identical geometric transporter in
`FiniteEtale.Cover ((cmGeometricSchemeTower ... q).obj U)`.
Its `_left` and `_hom` formulas hold by definition: the source is the
original geometric level at `V`, and the structural map is the existing
geometric tower map at `k`.

`cmGeometricFiniteEtaleTransitionPullbackIso` is the canonical isomorphism
from this cover to the pullback of
`cmFiniteEtaleTransition_of_dominantCriterion ... k` along the original
geometric projection at `U`. It is obtained directly from the actual
cartesian square, as an isomorphism over the geometric target.
Its `_hom_fst` equation identifies the first pullback projection with
the original geometric projection at `V`. Its `_hom_snd` equation
identifies the second pullback projection with the original geometric
transporter. Both equations are the projection equations of the
cartesian-square isomorphism.

The statements are conditional on the listed original prerequisites.
They do not prove representability, small-level existence, dual
existence or geometry, rigidity, the dominant criterion, canonical
models, or a cohomological tower comparison.
