# Unimodularity of the rational points of connected reductive groups

Module `Langlands.Representation.Aubert.General.RationalReductiveUnimodularityProof`,
namespace `Langlands.Aubert.General.RationalPointFamily`.

## Result

`rationalReductiveUnimodularity : RationalReductiveUnimodularityStatement.{u}` proves
the published proposition for every universe `u`. Let `k` be a nonarchimedean local
field with its given field, valuation and topology, and `G` a connected reductive group
over `k`. Give `RationalPoint k G.X` the published `pointTopology`, and assume the
statement's instance premises (local compactness, nonarchimedean group, Hausdorff) and
`StandardCocharacterStatement`. Then Mathlib's `Measure.modularCharacter` on
`RationalPoint k G.X` is identically `1`. The standard-cocharacter premise is not used.

## Provenance and route

Internal. The statement's Markdown cites Renard, *Représentations des groupes
réductifs p-adiques* (2026), V.5.4, Proposition, whose proof uses the Cartan
decomposition and Iwahori decompositions. This proof takes a different route that
uses neither. It is the local, nonarchimedean form of the argument behind the
published adelic result `Langlands.Global.AdelicGroupPoints.adelicHaarUnimodularity`:

1. The modular character of `G(K)` is at most the Haar scaling factor of any linear
   automorphism of `K^d` with determinant `det Ad(g)`. This is the published
   `Langlands.Global.LocalModularCharacter.modularCharacter_le_of_adjoint_ultrametric`,
   for a smooth affine group over a field `F` and a complete, proper, ultrametric,
   nontrivially normed field `K` that is an `F`-algebra.
2. For connected reductive `G`, the rational adjoint determinant character vanishes.
   This is the published
   `Langlands.GroupScheme.Lie.connectedReductiveAdjointDeterminant_of_centralDerivedProduct`,
   applied to the proved `Langlands.GroupScheme.reductiveCentralDerivedProduct`.
3. A linear automorphism of determinant `1` preserves additive Haar measure, by the
   published `Langlands.Global.addEquivAddHaarChar_linearPi_eq`.

So `Δ(g) ≤ 1` for every `g`. Applied to `g⁻¹`, it also gives `Δ(g)⁻¹ ≤ 1`, hence `Δ(g) = 1`.

## Declarations

### The normed field structure

`localFieldNormedField k : NontriviallyNormedField k` is Mathlib's
`Valued.toNontriviallyNormedField`. It is built over the right uniform structure
`IsTopologicalAddGroup.rightUniformSpace k`, with the rank-one structure from
`ValuativeRel.IsRankLeOne`, exactly as in Mathlib's `IsNonarchimedeanLocalField`
instances and the published `HarmonicAnalysis.GeneralLocalField.properNormedField`.
The module proves:

- `localFieldNormedField_toField`: its underlying field is the given one, by `rfl`;
- `localFieldNormedField_topology`: its metric topology is the given topology of `k`,
  by `rfl` at reducible-and-instances transparency;
- `localFieldNormedField_completeSpace`, `localFieldNormedField_properSpace` and
  `localFieldNormedField_isUltrametricDist`: completeness (Mathlib's instance for a
  compatible uniform structure), properness
  (`ProperSpace.of_nontriviallyNormedField_of_weaklyLocallyCompactSpace`), and the
  ultrametric inequality (Mathlib's instance for `Valued.toNormedField`).

Since the field and topology agree definitionally, the published adjoint bound can be
applied with `F = K = k` and `Algebra.id`, without changing any structure on `k`.

### Determinant of the adjoint action

`det_adjoint_eq_one_of_adjointDeterminantCharacter_eq_zero`: suppose `G` is affine of
finite type over a field `k` and `Lie.adjointDeterminantCharacter G = 0`. Then for every
test algebra `A` and every `g : G.affinePoints A`, `LinearMap.det (adjoint G A g) = 1`.
The proof rewrites with the published `Lie.adjointDeterminantCharacter_val`. It then
evaluates the zero character through `evalHom`'s `map_zero`, as in the published
`AdelicGroupPoints.characterUnits_zero`.

### The bound and the equality on `G.affinePoints (CommAlgCat.of k k)`

The section gives `G.affinePoints (CommAlgCat.of k k)` the published evaluation
topology `G.affinePointsTopologicalSpace` and its topological-group structure
`G.affinePointsIsTopologicalGroup`, as local instances.

- `affinePoints_modularCharacter_le_one`: `G` is smooth, affine and of finite type,
  its adjoint determinant character is zero, and its points are locally compact and
  Hausdorff. Then `Δ(g) ≤ 1`. The proof installs `localFieldNormedField k` and its
  completeness, properness and ultrametric distance. It derives second countability
  of the points from that of `k` (`GeneralLocalField.secondCountableTopology`, through
  the published `affinePointsSecondCountableTopology`), takes the Borel structure, and
  applies `modularCharacter_le_of_adjoint_ultrametric` with `c = 1`. It remains to show
  that each linear automorphism `A` of `k^d` with `det A = det Ad(g)` has Haar scaling
  factor `1`. Here `det A = 1` by the previous lemma. Mathlib's `distribHaarChar k`
  satisfies `μ.map (a * ·) = (distribHaarChar k a)⁻¹ • μ` for an additive Haar measure
  `μ` on `k`, which is regular by `GeneralLocalField.haarMeasure_regular`. So
  `addEquivAddHaarChar_linearPi_eq` evaluates the factor as
  `distribHaarChar k (det A) = distribHaarChar k 1 = 1`.
- `affinePoints_modularCharacter_eq_one`: under the same hypotheses, `Δ(g) = 1`.
  Combine the bound at `g` and at `g⁻¹` with `Δ(g⁻¹) = Δ(g)⁻¹` and `Δ(g) > 0`.

### Comparison with the identity-test points

`rationalPointContinuousMulEquiv k G` is a topological-group isomorphism
`RationalPoint k G.X ≃ₜ* G.affinePoints (CommAlgCat.of k k)`. The source carries
`rationalPointTopology k G.X` and the target its evaluation topology. Its group
isomorphism is the published `GaloisPointComparison.rationalCoeffEquiv`. Its underlying
map agrees with the published homeomorphism `rationalPointsAffineHomeomorph`
(`rationalCoeffEquiv_eq`), so it is a homeomorphism.

### Main theorem

`rationalReductiveUnimodularity`: from connected reductivity, `G` is affine and smooth.
`pointTopology` unfolds to `rationalPointTopology`. Transporting local compactness and
the Hausdorff property along `rationalPointContinuousMulEquiv` gives these instances on
the affine points. The published `modularCharacter_continuousMulEquiv` (module
`RationalLeviUnimodularityReduction`) says the isomorphism preserves modular
characters. So it suffices to apply `affinePoints_modularCharacter_eq_one`, with the
vanishing of the adjoint determinant character from step 2.

## Integrated contributions

This module combines the independently reviewed unimodularity development in
artifact `a1f079ad-9c12-41be-8f7c-cef49eaca617` with Worker 4850's contribution
`87c0d17f-51e2-46fa-9322-fc7bd7e4d34f`. Both prove the same published proposition.
The combined module keeps one `rationalReductiveUnimodularity` theorem, the
all-test-algebra determinant lemma, and the distinct reusable interfaces from both.
The main proof is the local-field construction described above.

## Additional normed-field interfaces

The following helpers retain Worker 4850's normed-field and topological comparison
interfaces. The determinant calculation reuses the general lemma above.

1. `addEquivAddHaarChar_linearPi_eq_one_of_det`. For a nontrivially normed proper field
   `K` and a `K`-linear automorphism `A` of `K^d` with `det A = 1`, the Haar character
   `addEquivAddHaarChar` of `A` is `1`. The proof applies the published
   `Langlands.Global.addEquivAddHaarChar_linearPi_eq` (module
   [`HaarScaleNorm`](../../../Global/LocalModularCharacter/HaarScaleNorm.md)). That theorem
   expresses the Haar character of `A` as `χ (det A)` for any character `χ` of `Kˣ` that
   describes how multiplication by units scales an additive Haar measure of `K`. Here `χ` is
   Mathlib's `distribHaarChar K`. Its defining property is `distribHaarChar_mul`, together
   with `Set.preimage_smul`. Since `det A = 1`, the value is `χ 1 = 1`.
2. The general `det_adjoint_eq_one_of_adjointDeterminantCharacter_eq_zero` above specializes to the normed base field. If
   `Lie.adjointDeterminantCharacter G = 0`, then `LinearMap.det (adjoint G K g) = 1` for
   every point `g` of `G` with values in `K`. The published
   `Lie.adjointDeterminantCharacter_val` identifies this determinant with the value at `g` of
   the character `adjointDeterminantCharacter G`. The zero character evaluates to the unit:
   evaluation at `g` (`GroupScheme.evalHom`) is additive, so it sends `0` to `1`.
3. `modularCharacter_affinePoints_le_one`. Let `K` be complete, proper and ultrametric, and
   let `G` be smooth, affine and of finite type with trivial adjoint determinant character.
   Give `G(K) = G.affinePoints (CommAlgCat.of K K)` the evaluation topology, and assume it
   is locally compact, Hausdorff and second countable, with its Borel structure. Then
   `modularCharacter g ≤ 1`. The proof applies the published
   `Langlands.Global.LocalModularCharacter.modularCharacter_le_of_adjoint_ultrametric`
   (module [`AdjointBound`](../../../Global/LocalModularCharacter/AdjointBound.md)), with
   base field `F = K` and constant `c = 1`. Its hypothesis asks that every linear
   automorphism with determinant `det Ad(g)` have Haar character `c`. Steps 2 and 1 give
   this.
4. `modularCharacter_affinePoints_eq_one`. Under the same hypotheses,
   `modularCharacter g = 1`. Step 3 gives `≤`. For `≥`, step 3 at `g⁻¹` and
   multiplicativity give `1 = Δ(g) Δ(g⁻¹) ≤ Δ(g)`.
5. `rationalPointsAffineContinuousMulEquiv`. For a topological field `k` and an affine group
   scheme `G` over `k`, this is an isomorphism of topological groups between
   `rationalPoints G` (with `rationalPointTopology k G.X`) and
   `G.affinePoints (CommAlgCat.of k k)` (with the evaluation topology). The group
   isomorphism is the published `GaloisPointComparison.rationalCoeffEquiv`. The published
   `rationalCoeffEquiv_eq` shows that its underlying map is `rationalPointEquiv`. That map is
   also the underlying map of the published homeomorphism `rationalPointsAffineHomeomorph`
   (module [`PointTopology`](../../../GroupScheme/Rational/PointTopology.md)), which gives
   continuity in both directions.

## Consumers

The published `rationalReductiveUnimodularity_of_structural_inputs` (module
[`RationalReductiveUnimodularityReductionProof`](RationalReductiveUnimodularityReductionProof.md))
derives the same statement from six structural inputs; the present proof needs none of them.
The statement is a premise of the published reductions
`rationalParabolicModulus_of_reductiveUnimodularity` (module
[`RationalLeviUnimodularityReduction`](RationalLeviUnimodularityReduction.md)) and
`maximalLeviSupercuspidalUnitarizableConstituent_of_positiveConstituent` (module
[`MaximalLeviUnitarizableConstituentReduction`](../../Exponents/MaximalLeviUnitarizableConstituentReduction.md)),
among others.
