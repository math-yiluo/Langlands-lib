# Regularity of the actual standard unipotent point subgroups

Worker 480 constructed this derived adapter from the published dynamic unipotent
containment proof and the standard-cocharacter assertion. The ambient group is
the existing `RationalPoint k G.X`, with exactly `RationalPointFamily.pointTopology`.
Each index is a finite subset of the literal simple-root subtype `SimpleRoot i ν`.
The subgroup is the existing `unipotent i ν I`, evaluated at the identity test
object. No replacement topology or subgroup is supplied.

The common geometric hypotheses are an affine group scheme `G` over a
topological field `k : Type u`, a commutative group scheme `T`, a homomorphism
`i : T.toGrp ⟶ G`, a cocharacter `ν`, connected reductivity of `G`, maximal
splitness of `i` and genericity of `ν`. The existing universal
`StandardCocharacterStatement.{u}` is an explicit premise. This module does not
prove it. Applying it to `rootSet i ν I` gives an actual standard cocharacter
`ζ` and an equality between the standard unipotent subgroup functor and the
dynamic unipotent subgroup functor for `CommGroupScheme.groupHom ζ ≫ i`.
Evaluating that equality rewrites the desired point-subgroup property to the
published dynamic property. The existence part of the assertion is used.

`standardUnipotent_isClosed_of_standardCocharacterStatement` needs only a
Hausdorff topology on `k` in addition to those hypotheses. After the rewrite,
it applies
`BruhatTits.DynamicUnipotentContainment.isClosed_unipotentPoints`. That theorem
describes dynamic subgroup membership by equations in the continuous coordinate
evaluations. Its canonical `rationalPointTopology` is definitionally the
`pointTopology` installed here, with the affine instance obtained from
`IsAffineHom G.X.hom`.

`standardUnipotent_isLimitOfCompactSubgroups_of_standardCocharacterStatement`
assumes that `k` is a nonarchimedean local field, with the published
`Field`, `ValuativeRel`, `TopologicalSpace` and `IsNonarchimedeanLocalField`
instances. It composes the unconditional theorem
`BruhatTits.dynamicUnipotentCompactOpenContainment` with
`BruhatTits.dynamicUnipotent_isLimitOfCompactSubgroups`, which forgets openness.
The subgroup equality then gives
`Jacquet.Localization.IsLimitOfCompactSubgroups (unipotent i ν I)`.
Thus every compact subset of this actual subgroup, with its inherited topology,
is contained in a compact subgroup. No compact-limit hypothesis remains.

`standardUnipotentCompactContainer` makes this existence result available as
actual subgroup data. For a compact subset `C` of `unipotent i ν I`, it chooses
one subgroup of `unipotent i ν I` from the proved existence theorem.
`standardUnipotentCompactContainer_spec` proves that the chosen subgroup is
compact in the inherited topology and contains `C`. The choice is
noncomputable; no canonical choice, functoriality or openness is asserted.

The remaining theorems retain local compactness and the nonarchimedean group
structure of the rational-point group at the same canonical topology. They
take any proof `hU` that this unipotent subgroup is closed, so they can be used
with the closedness arguments in existing consumer statements.
`standardUnipotent_isUnimodular_of_standardCocharacterStatement` applies
`General.isUnimodularModulus_of_isLimitOfCompactSubgroups` to the proved
compact-limit property. It says that the Haar modulus of every inner
automorphism of the actual unipotent subgroup is one.

`standardJacquetFunctor_map_isShortExact_of_standardCocharacterStatement`
uses the published standard semidirect decomposition and applies
`General.jacquetFunctor_map_isShortExact` to that same compact-limit result.
It preserves every actual short exact sequence of smooth complex
representations, without a length assumption. Its representation carrier
universe `v` is independent of `u`.
`standardJacquetFunctor_preservesShortExact_of_standardCocharacterStatement`
applies the published finite-length exactness wrapper. The resulting
`PreservesFiniteLengthShortExact` concerns the images of short exact
sequences whose original terms have finite length. It does not assert that
these images have finite length.

The provenance is internal composition and transport of published theorems.
The dynamic containment proof constructs a continuous contraction in
coordinates and uses compactness to move each compact set into a compact
open subgroup. The general Jacquet exactness proof uses character localization
exactness; normalization twists the action and preserves the quotient maps.
The unimodularity proof applies compact containment to a singleton and
uses the open kernel of the Haar character. None of these proofs assumes
the geometric lemma, cuspidal support, classification, or non-self-associated
induction irreducibility. This adapter supplies regularity prerequisites
for the assigned self-association proof; it does not establish that target,
opposite-Jacquet duality, or any finite-length preservation assertion.
