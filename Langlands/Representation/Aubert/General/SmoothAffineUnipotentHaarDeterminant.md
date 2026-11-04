# Vector filtrations and Haar determinants for smooth affine groups

Authors: Worker 184 and Worker 1423. Worker 184 adapts Worker 1423's published
`DynamicUnipotentVectorFiltrationProof` graded-coordinate proof. The original
published statement and proof remain unchanged.

## Objects and hypotheses

`VectorFiltrationDeterminantData k H U g delta` records a finite filtration of
an actual subgroup `U` of a topological group `H`, normalized by `g`, with
successive vector-space quotients and prescribed product `delta` of the actual
linear determinants. Its fields consist of:

- a length `N`, subgroups `F r`, dimensions `n r`, quotient maps
  `q r : F r → k^(n r)` and linear automorphisms `L r`;
- `F 0 = U`, `F N = ⊥`, descent and normalization by `g` for `r < N`;
- additivity, the exact kernel `F (r + 1)`, continuity, openness and
  surjectivity of each quotient map for `r < N`;
- intertwining of actual conjugation `x ↦ g*x*g⁻¹` with `L r`;
- the equality `∏ r < N, det (L r) = delta` in `kˣ`.

The data structure itself requires only a topological field `k` and a group
`H` with a topology. Its existence is proved below in the geometric setting.

`exists_smoothAffineUnipotentVectorFiltration` and
`smoothAffineUnipotentVectorFiltration` work over any nonarchimedean local
field `k`, including positive characteristic. Their ambient group scheme `G`
is smooth and affine over `Spec k`, expressed by `[Smooth G.X.hom]` and
`[IsAffineHom G.X.hom]`. Its rational points have the canonical
`pointTopology`. Local compactness, the nonarchimedean group property and
Hausdorffness of that topology are explicit instance hypotheses.

The cocharacter `chi` is arbitrary, including the trivial one. Maps `iZ` and
`iU` represent the actual dynamic centralizer and unipotent subgroup of
`chi`. The determinant construction retains `[IsAffine Z.X.left]`,
`[IsAffineHom U.X.hom]` and an arbitrary natural finite Lie coordinate system
`c : Lie.FiniteCoordinates U d`. For any rational point `m` of `Z`, these
results give filtration data for the exact subgroup
`(Dynamic.unipotent chi).carrier (Over.mk (𝟙 _))` of `G(k)`, the element
`g = m ≫ iZ.hom.hom`, and
`delta = rationalCharacterEval ((centralizerAdjointAction hZ hU).determinantCharacter c) m`.
The definition chooses one of the proved data structures using classical
choice. It supplies all the displayed fields with proofs.

## Implemented vector-filtration proof

The proof reuses the published graded rational-coordinate and Lie-coordinate
helpers. Affineness identifies `G` with its coordinate algebra; smoothness
supplies formal smoothness and finite type. The cyclic-tail coordinate theorem
then provides polynomial coordinates of strictly positive integral weights.
No connectedness or reductivity premise is needed at any later step.

Conjugation by `m` has a graded-coordinate matrix `J`. Its determinant equals
the evaluation of the actual Lie determinant character, by
`rationalCharacterEval_determinantCharacter` and `det_differential`.
`det_conjMatrix` expresses it as the product of its weight-block determinants;
every block is invertible. Let `N` be the largest coordinate weight and
`F r = rationalFiltration G chi r`. The quotient `q r` reads the coordinates
of weight `r + 1`; `L r` is the corresponding reindexed block of `J`.

The actual rational filtration gives its initial and terminal subgroups,
descent and normalization. Coordinate multiplication gives additivity and
membership by coordinate vanishing gives the exact kernel. The coordinates
are continuous. Placing a vector in the weight `r + 1` coordinates and zeros
elsewhere defines a continuous section, proving surjectivity and openness.
`ratCoord_conj` proves intertwining with the actual conjugation. The two
published finite-sum and block-product lemmas then identify the product of
the determinants of `L r` with `det J`.

## Haar formulas

`smoothAffineUnipotentHaarDeterminant` retains the same smooth affine and
rational-topology hypotheses. It also displays closedness `hUc` of the actual
unipotent point subgroup and the fact `hm` that `g` normalizes it. It proves

`closedNormalizerCharacter U(k) hUc ⟨g, hm⟩ = distribHaarChar k (delta)`.

The left side is the Haar factor of forward conjugation on the actual
closed subgroup, as defined in the Library; the right side is in `ℝ≥0`.
The proof takes the constructed filtration. The general affine, locally
finite type theorem
`BruhatTits.DynamicUnipotentContainment.exists_compactOpenSubgroup`, applied
to each singleton, provides the compact open cover. Smoothness supplies local
finite type. The published `vectorFiltrationHaarModulus` computes the Haar
factor as the product of the absolute determinant factors; multiplicativity
and the determinant field of the constructed data finish the equality.

`smoothAffineCentralizingUnipotentHaarDeterminant` allows any homomorphism
`iZ : Z ⟶ G` whose all-test image is contained in `Dynamic.centralizer chi`.
Here `Z` need not represent the whole centralizer, nor be monomorphic.
The acted-on map still represents the actual dynamic unipotent subgroup,
with the same affine and finite Lie coordinate assumptions, and closedness
of its rational points is explicit. The normalizing point is the actual
`Dynamic.centralizingUnipotentNormalizerHom chi iZ hZ m`, whose underlying
point is `m ≫ iZ.hom.hom`. Its determinant is that of the actual conjugation
action `centralizingUnipotentAction chi iZ hZ hU` in the coordinates `c`.

This last proof factors `iZ` through the canonical represented affine full
centralizer. It applies the smooth affine full-centralizer Haar formula to
the corresponding point, then uses the published equality of restricted
actual actions and determinant characters, rational evaluation under
restriction, and equality of the two actual normalizer points.

## Provenance and retained obligations

This is an internal generalization and construction from Library results,
with no new external-source assertion. The substantive vector proof is
adapted from Worker 1423's published
`DynamicUnipotentVectorFiltrationProof`, keeping its exact rational-coordinate,
Lie-coordinate and weight-block route. The Haar step reuses the published
vector-filtration Haar theorem and general dynamic compact-open containment.
The smaller centralizing-group step adapts Worker 184's
`CentralizingUnipotentHaarDeterminant` proof with the new smooth affine formula.

The module proves neither a Haar formula for an arbitrary intersection of
two dynamic unipotent subgroups nor a comparison between the Haar factors
of the same subgroup in different ambient groups. Those require further
actual-object identifications and topological transport. Whole-common-Levi
character detection, normalized half-modulus comparison, the geometric
filtration and the exact-K0 expansion remain separate obligations. The host
`RationalGeometricK0ExpansionStatement` receives no new premise.
