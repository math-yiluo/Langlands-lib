# Actual Haar determinant on a common positive intersection

This is an internal prerequisite by Worker 184 for the rational-point geometric
lemma. It constructs the character on the literal intersection and proves its
forward determinant formula; it does not prove the exact-K0 expansion.

## Original point map and Haar character

`Dynamic.centralizingUnipotentIntersectionNormalizerHom` works over any field.
Given two cocharacters `chi`, `psi` of `G` and a homomorphism `iZ : Z ⟶ G`
whose all-test range centralizes both, it restricts the codomain of
`rationalPoints.map iZ` to the normalizer of
`(Dynamic.unipotent chi ⊓ Dynamic.unipotent psi).carrier (Over.mk (𝟙 _))`.
Centralizer points normalize the corresponding unipotent subgroup, so the
intersection normalizer contains this image. Its coercion theorem states
that the underlying point is exactly `z ≫ iZ.hom.hom`.

`centralizingUnipotentIntersectionHaarCharacter` equips `G(k)` with the
canonical evaluation topology `pointTopology`. Assuming that this is a locally
compact topological group and that the literal intersection is closed, the
character is `HaarModulus.closedNormalizerCharacter` composed with the preceding
point map. Its values are positive nonnegative-real units. It uses forward
conjugation `x ↦ g*x*g⁻¹`, the forward Haar-scaling convention, and the original
acting point. Its definition does not require a representative of the
intersection, or any Lie coordinates.

## Determinant theorem and exact scope

`unipotentIntersectionHaarDeterminant` works over every nonarchimedean local
field in universe `u`, without a characteristic restriction. Its ambient group
scheme `G` is smooth and affine. The canonical point topology is used, with
explicit local compactness, nonarchimedean-group and Hausdorff instances. It
assumes:

- the all-test range of `chi` lies in `Dynamic.centralizer psi`;
- the all-test range of `iZ` centralizes both cocharacters;
- `iU : U ⟶ G` represents their literal unipotent intersection;
- `Z` is affine, `U` is affine over the field, and `c : Lie.FiniteCoordinates U d`;
- the literal point intersection is closed.

For every original point `m : rationalPoints Z`, it proves that the
nonnegative-real coercion of the Haar character equals `distribHaarChar k`
applied to the evaluation at `m` of
`(Dynamic.centralizingUnipotentIntersectionAction chi psi iZ hZ hZ' hU).determinantCharacter c`.
This is the determinant of the actual common-centralizing action on the same
represented `U`, using the given coordinates. No reductivity, splitness,
positive rank, character-detection hypothesis or representation-theoretic
expansion premise occurs.

## Implemented proof

The proof first constructs the canonical affine centralizer `M` of `psi`.
`dynamicSmooth` supplies its smoothness, and all-test centralization factors
`chi` through `M` as `chiM`. It then constructs the canonical centralizer `H`
of `chiM` inside `M`. This group is again smooth and affine. Its composite
closed inclusion `iH : H ⟶ G` centralizes both original cocharacters. The
self-centralization lemma `Dynamic.range_le_centralizer` factors `chiM`
through `H`, giving `chiH` with `chiH ≫ iH = chi`.

The canonical dynamic unipotent group `N` of `psi` is smooth by
`dynamicSmooth` and affine by its closed inclusion in `G`. The original
intersection representative factors through it as `fU`. The original map
`iZ` factors successively through `M` and `H` as `fZ`; the factorization lemma
`Dynamic.range_factor_le_centralizer` justifies the second step. All these
are factorizations of the original scheme homomorphisms.

Let `a` be the actual conjugation action of `H` on `N` and `A` its semidirect
product. Products give smoothness and affineness of `A`. The lifted cocharacter
is `chiA = chiH ≫ a.semidirectInr`, and the intersection inclusion is
`jU = fU ≫ a.semidirectInl`.
`Dynamic.isRepresentedBy_unipotentIntersection_semidirect` identifies the same
`U` with the full dynamic unipotent group of `chiA`. Represented dynamic
closedness makes `jU` closed. Reflecting closedness through `semidirectInl`
and composing with the inclusion of `N` proves closedness of the original
`iU`. Centrality of `chiH` in `H` puts `jZ = fZ ≫ a.semidirectInr` in the
centralizer of `chiA`.

The canonical point topology of the smooth affine `A` is locally compact and
Hausdorff. The auxiliary theorem `affineRationalPoint_nonarchimedeanGroup`
obtains its open subgroup basis from
`BruhatTits.rationalPoint_isLocallyProfinite` and the project van Dantzig
characterization; the helper applies to any affine group scheme locally of
finite type over this field. Closed represented-point embeddings make the
internal dynamic unipotent point subgroup closed.

`smoothAffineCentralizingUnipotentHaarDeterminant` now gives its Haar formula.
`Dynamic.semidirectUnipotentIntersectionAction_eq` identifies the internal
action with the original ambient action on the identical `U`, so the Lie
coordinates, determinant character and acting point stay the same.

Finally, `rationalPointSubgroupHomeomorph` gives canonical multiplicative
homeomorphisms from `U(k)` onto the internal dynamic subgroup and the original
literal intersection. The explicit inclusion formula for the internal action
identifies forward normalizer conjugation with that action. Its equality with
the ambient action then proves the forward intertwining equation for the
composite homeomorphism. Applying
`CorrectedFiltration.mulEquivHaarChar_eq_closedNormalizerCharacter` transports
the internal Haar factor to the original literal subgroup. The proof does not
need a homomorphism from the semidirect ambient group `A` to `G`.

## Provenance and remaining boundary

The proof is a deduction from represented dynamic subgroups, actual conjugation
identities, canonical point topology and the existing smooth-affine Haar
formula. It introduces no new literature assertion. Its uses from
`CorrectedOrbitJacquet` are the general Haar-transport theorem, with its
underlying locally compact subgroup machinery; no orbit-representation
comparison is invoked in this proof body. This describes direct dependencies,
not an independent audit of the entire imported-module closure.

Existence of the represented intersection and its finite Lie coordinates are
explicit inputs here. Whole-common-Levi determinant detection, normalized
representation comparisons, ordered filtration and the actual exact-K0 sum
remain obligations of the host task.
