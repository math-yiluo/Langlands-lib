# The actual geometric filtration of `r_J i_I σ` in the extraction-input form

Author: Worker 174, Task 5323 (`c79b0cd0-661f-4239-9f65-483d6f319480`).

Module `Langlands.Representation.Aubert.General.RationalInducedJacquetGeometricFiltration`,
namespace `Langlands.Aubert.General.RationalPointFamily`.

This module proves, with no hypothesis beyond the displayed rational data, the
geometric-filtration input `PointInducedJacquetGeometricFiltration` of the
published extraction route in
[RationalCuspidalExtractionInputs](RationalCuspidalExtractionInputs.md). That
predicate was published as an explicit unproved input of
`rationalCuspidalJacquetFactorExtraction_of_inputs`. It is the first conjunct of
`RationalCuspidalExtractionInputsStatement`; the second conjunct, proper-standard
induction exclusion, is not proved here.

## Setting

`k : Type u` is a nonarchimedean local field (`ValuativeRel`,
`TopologicalSpace`, `IsNonarchimedeanLocalField`). `G` is a group scheme over
`Spec k` with affine structure map, `i : T.toGrp ⟶ G` a monomorphism from a
commutative group scheme, and `ν` a cocharacter. The rational points
`RationalPoint k G.X` carry the canonical `pointTopology`, assumed locally
compact, nonarchimedean and Hausdorff (`T2Space`). The remaining premises are
the displayed ones of the extraction target: the point normalizer and
centralizer comparisons `hN`, `hZ`, `StandardCocharacterStatement` (`hStandard`),
`StandardLeviIntersectionStatement` (`hInter`), `HasRelativeRootSystem i`
(`hRoots`), connected reductivity `hG`, maximal splitness `hi`, genericity
`hν`, closedness of all actual standard Levis (`hM`) and unipotent radicals
(`hU`), and a finite enumeration of `SimpleRoot i ν`. The field universe `u`
and the carrier parameter `v` are independent; all carriers are in
`max (u + 1) v`. The inducing representation `σ` is an arbitrary smooth
representation: no irreducibility, admissibility, finite generation or finite
length is assumed.

## Declarations

`pointInducedJacquetGeometricFiltration_of_leviWeyl` takes, in addition, a
finite actual Weyl group (`Fintype (Weyl i)`), an actual point Coxeter system
`cs` with the actual standard-Levi Weyl identification
`actualLeviWeylIdentification (torusPoints i) (levi i ν) cs` and the
root-length comparison `RootLengthComparison i ν hN hZ cs`. It concludes
`PointInducedJacquetGeometricFiltration i ν hStandard hG hi hν hM hU cs`:
for all `I`, `J` and every smooth `σ` on `levi i ν I`, the actual object
`r_J(i_I σ)` (actual normalized induction `normalizedInductionFunctor`, then
actual normalized Jacquet restriction `jacquetFunctor`, along the standard
decompositions `isSemidirectDecomposition_of_standardCocharacterStatement`) has
a finite `ObjectRepFiltration` with zero bottom and full top, each of whose
smooth graded objects is actually isomorphic to the normalized geometric term
`(geometricTermFunctor … J I n hs ht).obj σ` at some `w` with
`IsMinimal cs J I w`, some normalizer lift `n` of `w` and some source and
target decompositions `hs`, `ht`.

`exists_pointInducedJacquetGeometricFiltration` removes the supplied Coxeter
data: it proves that some actual point Coxeter system `cs` satisfies
`RootLengthComparison i ν hN hZ cs` together with the preceding filtration
property. This is exactly the first conjunct of the published
`RationalCuspidalExtractionInputsStatement` at one datum.

## Proof

For `pointInducedJacquetGeometricFiltration_of_leviWeyl`:

1. `positiveSimpleReflectionComparison_of_rootLength` (module
   `RationalSuppliedCoxeterComparisons`) derives the positive-simple-reflection
   comparison from `hRoots`, `hν` and the root-length comparison.
2. Fix `I`, `J`, `σ`. Worker 124's `pointGeometricObjectFiltrationOfEpsilonBalance`
   (module `RationalGeometricObjectFiltrationConstruction`) is applied with its
   target index `J` and its source index `I`. It constructs the actual ordered
   support filtration of `pointInducedJacquetObject … J I σ`, which is by
   definition `r_J(i_I σ)`, together with an enumeration of the minimal
   classes, a lift of each class, source and target decompositions and the
   actual grade isomorphisms with the geometric terms.
3. Its only extra hypothesis, cancellation of the two original Haar
   corrections at every minimal lift, is supplied by Worker 4021's
   `geometricEpsilon_mul_eq_one` (module `RationalGeometricEpsilonBalance`).
   That theorem needs closedness of the actual standard parabolics and
   continuity of the actual Levi projections; these are the published
   `isClosed_standard_parabolic` and `continuous_standard_projection`, applied
   to `hStandard`, `hG`, `hi`, `hν`.
4. The filtration has `tailLength + 1` grades. For each grade `q`, the class
   `(enumeration q).val` is minimal by `mem_minimalReps`; the lift, its class
   equation and both decompositions are the constructed ones. The constructed
   grade isomorphism lives in `Rep`; since the smooth graded object has the
   same underlying representation by definition
   (`smoothGradedObject_representation`), `Representation.equivOfIso` followed
   by `SmoothRep.mkIso` turns it into the required isomorphism of smooth
   representations.

For `exists_pointInducedJacquetGeometricFiltration`, the published
`exists_rootSpanPointCoxeterSystem` (module `RationalRootSpanCoxeterComparisons`)
gives, from `hN`, `hZ`, `hG`, `hi`, `hRoots`, `hν`, finiteness of `Weyl i`, an
actual point Coxeter system, its root-length comparison and its standard-Levi
Weyl identification. A `Fintype` structure is chosen by `Fintype.ofFinite`, and
the previous theorem applies.

The identity-last refinement of the constructed filtration and the bijectivity
of its enumeration are not used: the extraction input asks only for some
minimal class at each grade.

## Source and provenance

This is the per-object form of the geometric lemma, D. Renard,
*Représentations des groupes réductifs p-adiques*, version of 9 July 2026,
registered as `renard-2026-representations-groupes-reductifs-padiques`
(SHA-256 `7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`),
VI.5.1, printed pp.161–164 / PDF pp.167–170. The theorems here are an internal
(derived) composition of published Library declarations; they add no source
translation of their own. The source correspondence of the filtration, the
grade terms and the minimal representatives is documented with
`PointInducedJacquetGeometricFiltration`, `PointGeometricObjectFiltration` and
the construction module.

The proof bodies of this module apply only the declarations named above. Their
own dependencies are recorded in their paired Markdown; in particular the
construction uses the proved `standardParabolicPointsStatement_proof` for the
actual double-coset classification, and the epsilon balance uses the common
centralizer Haar balance. No adjointness, cuspidal-support, character
independence or Langlands classification theorem is invoked here.
