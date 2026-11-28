# Actual rational cuspidal Jacquet-factor extraction: proof

Module `Langlands.Representation.Aubert.General.RationalCuspidalJacquetFactorProof`,
namespace `Langlands.Aubert.General.RationalPointFamily`.

The type of `rationalCuspidalJacquetFactorExtraction` is the entire proposition
`Langlands.Aubert.General.RationalPointFamily.RationalCuspidalJacquetFactorExtractionStatement.{u, v}`
of the module `Langlands.Representation.Aubert.General.RationalCuspidalJacquetFactorTarget`
at independent universes `u` and `v`. The theorem depends on the axioms
`propext`, `Classical.choice` and `Quot.sound`.
[Statement](RationalCuspidalJacquetFactorTarget.md)

## What is proved

The statement quantifies over every field `k : Type u` with `ValuativeRel`,
`TopologicalSpace` and `IsNonarchimedeanLocalField`, and every connected
reductive group scheme `G` over `Spec k`. It uses the literal rational-point
group `RationalPoint k G.X` with canonical `pointTopology` and the
`LocallyCompactSpace`, `NonarchimedeanGroup` and `T2Space` premises for that
topology. It uses an actual maximal split torus `i` and generic cocharacter
`ν`, the hypotheses `hStandard` and `hInter` for the standard families and
intersections, `hRoots` for the relative root system, `hN` and `hZ` for the
normalizer and centralizer comparisons, and `hU` and `hM` for closedness of
the actual standard unipotent radicals and Levis.

Let `I` and `J` be finite subsets of `SimpleRoot i ν`, including empty
subsets. Let `σ` on `levi i ν I` and `τ` on `levi i ν J` be irreducible
smooth complex representations satisfying `IsLeviCuspidal`, the vanishing
of every proper standard Jacquet restriction inside the respective Levi.
The representation `π` can be any smooth actual subquotient of the
normalized induction `i_I σ`. If `τ` is an actual subquotient of the
normalized Jacquet module `r_J π`, the theorem supplies a rational point
`n` and a witness `hn : ∀ x, x ∈ levi i ν J ↔ n⁻¹ * x * n ∈ levi i ν I`
with `rootAssociation i ν hN hZ I J n` and
`Nonempty (τ ≅ (conjugationFunctor n hn).obj σ)`. The root comparison is
equality of the indicated root sets under the class of `n` in the
normalizer modulo the full centralizer. The transported action of `x` in
the target Levi is `σ(n⁻¹ * x * n)` via the same Levi comparison `hn`.
The representation carriers have universe `max (u + 1) v`.
[Root action](RationalWeylRootAction.md)
[Conjugation transport](Parabolic.md)

## Proof

The Lean term applies the published reduction to the joint basis theorem.

```
rationalCuspidalJacquetFactorExtraction_of_jointBasis
  BruhatTits.SpecialCompact.jointSpecialCompactBasisExistence
```

- `rationalCuspidalJacquetFactorExtraction_of_jointBasis` (module
  `Langlands.Representation.Aubert.General.RationalCuspidalExtractionFromSpecialVertex`)
  proves
  `JointSpecialCompactBasisExistenceStatement.{u} →
  RationalCuspidalJacquetFactorExtractionStatement.{u, v}`.
  [Reduction](RationalCuspidalExtractionFromSpecialVertex.md)
- `Langlands.BruhatTits.SpecialCompact.jointSpecialCompactBasisExistence`
  (module `Langlands.BruhatTits.SpecialCompact.JointBasisProof`) proves
  `JointSpecialCompactBasisExistenceStatement.{u}` with no hypothesis: one
  apartment and special vertex with the special compact properties, the
  simultaneous standard basis and the Renard Cartan comparison, for every
  connected reductive group over every nonarchimedean local field in universe
  `u`. [Joint basis](../../../BruhatTits/SpecialCompact/JointBasisProof.md)

1. `Langlands.CuspidalSupport.rationalSpecialVertexCompactInputs_of_jointBasis`
   (module `RationalCuspidalInertiaDecompositionReduction`) turns the joint
   basis into the special-vertex inputs: a special vertex with
   `SpecialCompactProperties`, `SimultaneousStandardBasisAt` and
   `FiniteCartanCovering`. The covering comes from
   `rationalPositiveCartanCover`.
2. `rationalCuspidalJacquetFactorExtraction_of_specialVertexInputs` composes
   `rationalCuspidalExtractionInputs_of_specialVertexInputs` with
   `rationalCuspidalJacquetFactorExtraction_of_inputs` (module
   `RationalCuspidalExtractionInputs`).
3. `rationalCuspidalJacquetFactorExtraction_of_inputs` rewrites the target
   with `rationalCuspidalJacquetFactorExtractionStatement_iff_induced`
   (module `CuspidalJacquetFactorReduction`). That equivalence uses exactness
   of the actual Jacquet functor on short exact sequences via
   `standardJacquetFunctor_map_isShortExact_of_standardCocharacterStatement`
   (module `RationalUnipotentRegularity`). Exactness makes `r_J π` a
   subquotient of `r_J (i_I σ)`. Composing the two subquotient occurrences
   places `τ` in `r_J (i_I σ)`.
4. `inducedCuspidalJacquetFactorExtraction_of_filtration_exclusion` (module
   `RationalCuspidalExtractionInputs`) then extracts the factor. It combines
   `positiveSimpleReflectionComparison_of_rootLength`,
   `pointCuspidalExtractionGeometry_of_rootComparisons`,
   `pointProperTargetGeometricTermExclusion_of_standardInduction` and
   `pointCuspidalJacquetFactor_of_geometricFiltration`. The geometric
   filtration of `r_J (i_I σ)` is finite, and each grade is actually
   isomorphic to a `geometricTermFunctor` term of `σ`. If the source
   intersection of a term is proper, cuspidality of `σ` makes the term zero.
   If the source is full and the target is proper, the term is an induction
   inside `levi i ν J` from a proper standard Levi, and the exclusion of
   step 5 shows that it has no irreducible `IsLeviCuspidal` subquotient. If
   both are full, `pointGeometricTerm_full_intersections` uses the
   grade's normalizer lift `n` to prove the root association and construct
   `hn`. It then uses `geometricTermFullLeviIso` for the isomorphism of the
   term with `(conjugationFunctor n hn).obj σ`. The finite-filtration
   argument in `CuspidalJacquetFiltrationExtraction` puts the irreducible
   subquotient `τ` in a grade. The first two cases are ruled out, and the
   transported representation in the third case is irreducible, so
   `τ` is isomorphic to it.
5. `rationalCuspidalExtractionInputs_of_specialVertexInputs` supplies the two
   inputs of step 4, the geometric filtration and
   `pointLeviStandardInductionCuspidalExclusion_of_specialVertexInputs`.
   For the latter it transports to the rational points of the Levi scheme,
   applies `rationalCuspidalCompactRestriction` at a special vertex and
   uses `not_isSubquotient_of_compactRestriction` with the first-adjointness
   vanishing.

## Transitive dependencies on classification, the geometric lemma and adjointness

The dependencies below follow references in the types and values of the
declarations reachable from `rationalCuspidalJacquetFactorExtraction`.

### Geometric lemma (Renard VI.5.1)

`Langlands.Aubert.General.RationalPointFamily.exists_pointInducedJacquetGeometricFiltration`
takes the displayed rational data and supplies an actual point Coxeter
system with the root-length comparison and a finite filtration of
`r_J (i_I σ)` for every smooth `σ`. Its grades are isomorphic to the
`geometricTermFunctor` images of `σ` at minimal double-coset representatives.
It uses `pointInducedJacquetGeometricFiltration_of_leviWeyl` with the actual
Coxeter and standard-Levi Weyl comparisons from
`exists_rootSpanPointCoxeterSystem`.
[Filtration](RationalInducedJacquetGeometricFiltration.md)

`Langlands.Aubert.General.RationalPointFamily.pointGeometricObjectFiltrationOfEpsilonBalance`
forms the Jacquet support filtration of the ordered rational double
cosets. At each lifted representative, `jacquetSupportGeometricTermIso`
identifies the support grade with the normalized geometric term using
`jacquetSupportOrbitIso` and `orbitPieceCoinvariantsIso`. The grade
identification uses cancellation of the two Haar corrections, supplied in
this application by `geometricEpsilon_mul_eq_one`.
[Construction](RationalGeometricObjectFiltrationConstruction.md)
[Orbit term](RationalGeometricOrbitTerm.md)

### Adjointness

`Langlands.Aubert.General.FirstAdjointness.equiv` identifies intertwiners
from a smooth representation `A` of the ambient group into a normalized
induction of a smooth Levi representation `ρ` with intertwiners from
normalized Jacquet restriction of `A` to `ρ`. It uses a semidirect
decomposition with closed unimodular radical in a locally compact
nonarchimedean group. The maps `forward` and `backward` come from
`evaluation`, `descendedEvaluation` and `orbitMap`, with
`Langlands.Jacquet.CharacterReciprocity.evaluation` and its
`evaluation_covariance` and `evaluation_translate` lemmas.
[First adjointness](FirstAdjointness.md)

`Langlands.Aubert.General.RationalPointFamily.pointLeviStandardInductionCuspidalExclusion_of_specialVertexInputs`
uses `Langlands.Aubert.General.hom_eq_zero_of_isCuspidalFor_of_induction`
for induction along the proper standard family member indexed by
`K : Finset J` with `K ≠ Finset.univ` inside the target Levi `levi i ν J`.
The inside-Levi cuspidality of the domain makes its Jacquet restriction at
that member zero.
`isUnimodularModulus_standardUnipotent_in_levi` supplies the radical
unimodularity for the first-adjointness equivalence.
[Exclusion](RationalCuspidalExtractionFromSpecialVertex.md)

### Classification

The classification uses concern algebraic groups, algebraic
representations, forms and fields. For the smooth representation
subquotient argument,
`Langlands.Representation.Classification.SupercuspidalSupport` supplies
`SmoothRep.isSubquotient_iff_exists`, `SmoothRep.hom_hom_injective`,
`SmoothRep.hom_hom_surjective` and `SmoothRep.IsSubquotient.of_iso_right`.

#### Bruhat–Tits construction

`jointSpecialCompactBasisExistence` uses
`Langlands.Geometry.Building.bruhatTitsAvailability`, whose proof uses
`Langlands.Geometry.Building.groupAxiomsExistence`. The root valuation
branch goes through `Langlands.Geometry.Building.rootValuationBuildingConstruction`
and `Langlands.Geometry.Building.affineIwahoriTits`.

- `Langlands.GroupScheme.localRankOneClassification` gives the models of
  affine, simply connected, absolutely almost-simple groups of split rank
  one over a nonarchimedean local field. These are `SL₂(D)` for a central
  division algebra, special unitary groups of Witt index one in three or
  four variables over a separable quadratic extension, and the quaternionic
  symplectic and spin groups of Witt index one in ranks two or three and four
  or five, respectively. It takes the index from
  `Langlands.GroupScheme.titsIndexExistence`, which gives compatible Tits
  index choices for semisimple groups over arbitrary fields.
  [Rank-one classification](../../../GroupScheme/SimplyConnected/LocalRankOneClassificationProof.md)
- `Langlands.GroupScheme.localRankOneTitsIndex` gives five alternatives for
  the actual Tits index of an affine locally finite-type, simply connected,
  absolutely almost-simple group of split rank one over a nonarchimedean
  local field. The alternatives specify the numbering, distinguished
  vertices and full star action.

  | Index in the statement | Alternatives |
  | --- | --- |
  | `TitsIndexData.HasRankOneInnerAIndex` | `¹A_(2d−1),1^(d)` for `d > 0` |
  | `TitsIndexData.HasRankOneOuterAIndex` | `²A_2,1^(1)` or `²A_3,1^(1)` |
  | `TitsIndexData.HasRankOneCIndex` | `C_2,1^(2)` or `C_3,1^(2)` |
  | `TitsIndexData.HasRankOneOuterD4Index` | `²D_4,1^(2)` |
  | `TitsIndexData.HasRankOneInnerD5Index` | `¹D_5,1^(2)` |

  [Rank-one Tits index](../../../GroupScheme/SimplyConnected/LocalRankOneTitsIndexStatement.md)

The group-model step of `localRankOneClassification` uses the following
presentations.

- `Langlands.GroupScheme.innerTypeANormOne` identifies a simply connected,
  absolutely almost-simple group of inner type `A_n` over any field with
  the reduced-norm-one group of a central simple algebra of degree `n + 1`.
  `Langlands.GroupScheme.specialLinearInnerFormNormOne` provides this
  model for an inner form of `SL_(n+1)`. The identification of the split
  model uses `Langlands.GroupScheme.specialLinearSimplyConnectedPinning`
  for the split `A_n` pinning of `SL_(n+1)` over any field,
  `Langlands.LinearAlgebra.corootSpanCartanEquiv` for equivalence of finite
  reduced root data with spanning coroots and matching simple Cartan
  entries, and `Langlands.GroupScheme.pinnedIsomorphism` to lift a based
  root datum equivalence to a unique isomorphism of pinned split reductive
  groups over a field.
- `Langlands.GroupScheme.outerTypeARankOneHermitian` identifies the
  simply connected, absolutely almost-simple outer-A groups with the
  indicated rank-one indices over arbitrary fields with special unitary
  groups having an anisotropic middle of dimension `n − 1`.
  `Langlands.GroupScheme.outerTypeAHermitianPresentation` gives the
  determinant-one Hermitian model over a separable quadratic extension for
  the numbered `A_n` index with full star image generated by reversal and
  distinguished endpoints. It uses
  `Langlands.GroupScheme.SpecialLinearTorusAutomorphism.specialLinearTorusAutomorphism`
  for the all-test formula for torus-preserving automorphisms of the split
  special linear group. The formula is matrix conjugation with inverse
  transpose in the nontrivial based-root-action case.
- `Langlands.GroupScheme.typeCRankOneQuaternionic` produces the
  quaternionic symplectic models for the indices `C_2,1^(2)` and
  `C_3,1^(2)` over arbitrary fields. It uses
  `Langlands.GroupScheme.typeCDivisionForm` for the trace-valued
  antihermitian division form and the comparison of distinguished
  vertices for simply connected absolutely almost-simple type `C_n`
  (`n ≥ 2`). In that proof,
  `Langlands.GroupScheme.typeCQuasiSplitInnerForm` identifies the
  quasi-split model as `Sp_(2n)` and
  `Langlands.GroupScheme.symplecticInnerFormAntihermitian` gives the
  division form for the inner twist of this model. The latter uses
  `Langlands.GroupScheme.symplecticInnerFormInvolution` for reduced-norm-one
  isometries of a central simple algebra of degree `2n` with a finite Galois
  symplectic splitting chart, and
  `Langlands.GroupScheme.symplecticInvolutionAntihermitian` to express such
  an involution on a matrix algebra over a central division algebra using
  a trace-valued antihermitian Gram matrix.
  `Langlands.GroupScheme.typeCDistinguishedVertices` reads the distinguished
  vertices as the positive multiples of the division degree up to the
  Witt index. It uses `Langlands.GroupScheme.titsIndexIndependence`, the
  equivalence of the indices from compatible choices for a given
  semisimple field group.
- `Langlands.GroupScheme.classicalTypeDSpinPresentation` applies to
  simply connected, absolutely almost-simple groups of numbered type
  `D_n` (`n ≥ 4`) over arbitrary fields with the full star action fixing
  the nonfork vertices. It gives an actual spin model of a nondegenerate
  quadratic form over a central division algebra with involution. The
  Witt index equals split rank, and the nonfork distinguished vertices
  occur at the positive multiples of the division degree up to that index.
  The local classification specializes it through
  `Langlands.GroupScheme.typeDRankOneSpin_of_classicalTypeDSpinPresentation`.
  [Spin presentation](../../../GroupScheme/SimplyConnected/ClassicalTypeDSpinPresentationStatement.md)

  `Langlands.GroupScheme.classicalTypeDAlignedSpinCover` supplies the
  cover with the first fundamental weight trivial on its kernel over the
  separable closure. It uses `Langlands.GroupScheme.typeDVectorQuotient`,
  which gives the aligned central quotient with split form `SO_(2n)` when
  the star action fixes the first vertex, and
  `Langlands.GroupScheme.Quaternionic.evenSpecialOrthogonalForm`. The latter
  realizes every form of `SO_(2n)` split over the separable closure, for
  `n ≥ 4`, as the identity component of the isometry group of a
  nondegenerate quadratic form over a central division algebra with
  involution of Tits type 1. Its automorphism input
  `Langlands.GroupScheme.OrthogonalMatrix.specialOrthogonalAutomorphism`
  realizes automorphisms of split `SO_(2n)` for `n ≥ 2` by similitude
  conjugation on all scheme tests over a field.
  `Langlands.GroupScheme.alignedSpinCoverTitsIndex` gives the index
  comparison for these aligned covers and uses
  `Langlands.GroupScheme.Quaternionic.orthogonalMoritaRepresentation`
  for the split comparison of the actual row representation after
  extension to an algebraically closed field.

The index calculation in `localRankOneTitsIndex` uses
`Langlands.GroupScheme.localRankOneTitsIndexReductionToE6D4` and
`Langlands.GroupScheme.localRankOneTitsIndexReduction`. The following
identifications enter these reductions and the remaining exclusions.

- `Langlands.GroupScheme.typeBOddQuadraticPresentation` gives a central
  isogeny onto the determinant-one isometry group of a regular scalar
  quadratic form of dimension `2n + 1`, with Witt index equal to split
  rank, for simply connected, absolutely almost-simple type `B_n` with
  `n ≥ 3` over an arbitrary field. This is the input to the higher-B
  exclusion in `localRankOneTitsIndexReductionToE6D4`.
- `Langlands.GroupScheme.typeG2CayleyPresentation` identifies simply
  connected, absolutely almost-simple groups of numbered type `G₂` over
  arbitrary fields with the automorphism functors of Cayley data. It uses
  `Langlands.GroupScheme.splitCayleyAutomorphismPinning` for the split
  simply connected `G₂` pinning and trivial scheme centre of the split
  Cayley automorphism group over every field. This is the model used in
  the `G₂` exclusion in `localRankOneTitsIndexReduction`.
- `Langlands.GroupScheme.localAnisotropicTypeA` gives type `A_n` for the
  actual index of an affine anisotropic absolutely almost-simple group
  over a nonarchimedean local field. Its input
  `Langlands.GroupScheme.localAnisotropicAffineDiagram` presents the finite
  Cartan matrix as the finite block of an affine matrix with positive null
  vector and transitive permutation symmetry.
  `Langlands.GroupScheme.localAnisotropicTypeAInner` gives trivial full
  star action in the simply connected anisotropic type-A case over such a
  field. It uses `Langlands.GroupScheme.outerTypeAUnitarySplitPresentation`,
  which gives an all-test determinant-one Hermitian presentation of the
  simply connected absolutely almost-simple outer-A group over a field
  satisfying `UnitaryInvolutionSplitting`. The local splitting argument
  uses `Langlands.localUnitaryDivisionCommutative`, which identifies
  division algebras with a unitary involution over a separable quadratic
  extension of a nonarchimedean local field with their centres, and
  `Langlands.Algebra.CentralSimple.unitaryDivisionSplitting` to pass to the
  central simple algebra. The outer-A index argument uses the same
  splitting theorem.
- `Langlands.GroupScheme.absolutelyAlmostSimpleCartanClassification`
  numbers any actual Tits index of an absolutely almost-simple group over
  a field by an irreducible finite Cartan matrix. The matrix hypotheses
  come from `Langlands.GroupScheme.absolutelyAlmostSimpleFiniteCartan`.
  `Langlands.LinearAlgebra.finiteCartanClassification` gives the nine
  irreducible families for nonempty indecomposable finite Cartan matrices.
  These enter through
  `Langlands.GroupScheme.localRankOneTitsIndex_or_E6_or_residual_of_componentFactor`.
  The component step uses `Langlands.GroupScheme.semisimpleTitsComponentFactor`
  and `Langlands.GroupScheme.simplyConnectedTitsComponentFactor` to realize
  each connected absolute Cartan component of an actual semisimple
  field-group index as the index of a simply connected absolutely
  almost-simple factor over a finite separable extension, preserving the
  Cartan entries and the stabilizer star image.
- `Langlands.GroupScheme.splitHighestWeightClassification` gives
  existence of simple highest-weight representations for dominant
  characters and classifies irreducible algebraic representations up to
  isomorphism by their highest weights, for a supplied split pinning over
  an arbitrary field. It enters through
  `Langlands.GroupScheme.TitsIndexData.not_hasRankOneE6BranchIndex` and the
  Levi comparison of Tits obstructions in `SplitLeviTitsComparison`.

The local arithmetic in these branches includes the dimension bound for
anisotropic quadratic forms `Langlands.localQuadraticAnisotropicDimensionBound`,
the degree-six tensor-cube obstruction
`Langlands.CentralSimple.centralDivisionDegreeSixTensorCubeNonSplit` and
the division algebra results `Langlands.CentralDivision.localSK1`,
`Langlands.CentralDivision.localResidueDegree` and
`Langlands.CentralDivision.fieldEmbeddingsConjugate` used in the local
Kneser–Tits argument.

`Langlands.Geometry.Building.affineIwahoriTitsStatement_of_localArithmeticInputs`
uses `Langlands.GroupScheme.simplyConnectedAlmostSimpleWeilRestriction`
to express a simply connected almost-simple group over any field as a Weil
restriction from a simply connected absolutely almost-simple group over a
finite separable extension. Its input
`Langlands.GroupScheme.separablyClosedAlmostSimpleAbsolute` identifies
almost-simple groups over separably closed fields as absolutely almost
simple. The rank-one classification enters local Kneser–Tits through
`Langlands.GroupScheme.localAbsolutelyAlmostSimpleRankOneKneserTits_of_classification`
for local simply connected absolutely almost-simple groups of split rank
one and
`Langlands.GroupScheme.localKneserTits_of_rankOneLeviFactors_of_classification`
for the local simply connected case via rank-one Levi factors.
The Iwahori argument for induced tori also uses
`Langlands.GroupScheme.inducedTorusWeilDecomposition` through
`Langlands.Geometry.Building.inducedTorusIwahori`. With a finite Galois
splitting field for an induced torus, the theorem exhibits it as a
product of Weil restrictions of `Gₘ` from intermediate fields.

#### Central simple algebras and local arithmetic

Mathlib's Artin–Wedderburn theorem
`IsSimpleRing.exists_algEquiv_matrix_divisionRing_finite` identifies a
module-finite simple Artinian algebra over a commutative semiring with
a matrix algebra of positive size over a module-finite division
algebra. In the field applications the algebra is finite-dimensional.
The proofs use `IsArtinianRing.of_finite` and deduce centrality of the
division algebra from the matrix algebra isomorphism.

- `Langlands.GroupScheme.CentralSimpleUnits.divisionMatrixPresentation`
  uses this theorem for the reduced-norm-one group of a finite-dimensional
  central simple algebra over a field. This gives the division algebra
  in the binary norm-one model of the inner-A rank-one branch.
- `Langlands.GroupScheme.symplecticInvolutionAntihermitian` uses it
  for the finite-dimensional central simple algebra with a symplectic
  splitting chart in the type-C branch. The proof transports the
  involution to the matrix algebra over the central division algebra
  and constructs the trace-valued antihermitian Gram matrix.
  `Langlands.GroupScheme.OrthogonalInnerForm.orthogonalInvolutionHermitian`
  uses it in the even-orthogonal branch for an involution of the first
  kind with a split polar chart. The resulting Gram matrix is invertible
  and hermitian.
- `Langlands.Algebra.CentralSimple.unitaryDivisionSplitting` uses it
  over the separable quadratic extension in the outer-A index argument.
  It transfers the unitary involution to the division algebra and uses
  commutativity of that division algebra to split the original algebra.
- `Langlands.CentralSimple.exists_algEquiv_matrix_of_isSepClosed` uses
  it to split a finite-dimensional central simple algebra over a
  separably closed field. The division algebra is the ground field by
  `Langlands.CentralSimple.bot_eq_top_of_isSepClosed`, which applies
  `JacobsonNoether.exists_separable_and_not_isCentral'` to an algebraic
  central division algebra that properly contains its base field.
  The splitting enters the `E₆` index exclusion through
  `Langlands.CentralSimple.separableClosureChart`.

`IsSimpleRing.exists_algEquiv_matrix_of_isAlgClosed` gives a full matrix
algebra over the base for a finite-dimensional simple algebra over an
algebraically closed field. `Langlands.CentralSimple.exists_matrix_chart`
applies it after scalar extension of a finite-dimensional central simple
algebra in `Langlands.GroupScheme.Quaternionic.SpinKernel.spinKernelGenerator`,
used for local spin Kneser–Tits.

`IsSimpleRing.exists_algEquiv_matrix_end_mulOpposite` identifies a
simple Artinian algebra with matrices over the opposite of the
endomorphism algebra of a simple left ideal.
`Langlands.Brauer.exists_matrix_divisionRing_corner` uses it to present a
finite-dimensional simple algebra over a field and its corner at a nonzero
idempotent as matrix algebras over the same division algebra. The corner
Brauer comparison enters the `E₆` index exclusion through
`Langlands.Algebra.GaloisTwistedMatrix.isBrauerEquivalent_toCSA_compressed`.
The twisted-matrix construction also uses
`IsSimpleRing.isSemisimpleRing_iff_isArtinianRing`, the equivalence of
semisimplicity and Artinianness for simple rings.
`Langlands.Algebra.GaloisTwistedMatrix.exists_idempotent_ker_eq` uses
semisimplicity to complement a left ideal and obtain an idempotent with
a prescribed stable kernel. `IsSimpleRing.isIsotypic` makes every module
over a simple Artinian ring isotypic.
`Langlands.CentralDivision.exists_twist_linearMap_ne_zero` uses this
for the twisted modules in the conjugacy of field embeddings.

Mathlib's `littleWedderburn` gives a field structure on a finite division
ring. `Langlands.CentralDivision.localDivisionResidueField` applies it to
the actual residue ring of the reduced-norm valuation of a finite-dimensional
central division algebra over a nonarchimedean local field. This field
enters `Langlands.CentralDivision.localSK1` and the cyclic subfield
construction
`Langlands.CentralDivision.exists_localDivision_fullResidue_reducedDegree_cyclic_subfield`.
The residue field extension is Galois by `GaloisField.instIsGaloisOfFinite`,
which applies to a field extension with finite upper field.

`Langlands.ClassFieldTheory.Local.localBrauerInvariant` identifies the
Brauer group of a nonarchimedean local field with `ℚ/ℤ`.
`Langlands.GroupScheme.TitsIndexData.not_hasRankOneD4InnerOrNoFixedLeafIndex`
uses it with `localBrauerInvariant_division_degree_two`, which gives the
invariant `1/2` for a central division algebra of degree two, and with
`localBrauerInvariant_corestriction` for corestriction compatibility.
The construction of the invariant uses
`Langlands.ClassFieldTheory.Local.finiteUnramifiedResidueEquiv` to identify
the Galois group of a finite unramified extension with that of its residue
extension.

#### Integral models

The integral-model branch of `groupAxiomsExistence` uses
`Langlands.Geometry.Building.integralModelAxioms` and
`Langlands.BruhatTits.IntegralModels.unramifiedModelKernel`.
`Langlands.GroupScheme.quasiSplitSteinbergQuotient` supplies a
conjugation-invariant morphism for a simply connected quasi-split group
over a field, with conjugacy after field extension in a fibre with a
strongly regular point. Its fibre argument in
`Langlands.GroupScheme.ClassFunctions.stronglyRegularFibres` uses
`Langlands.GroupScheme.Dynamic.exists_unipotent_conj_eq_mul`, which reaches
`Langlands.AlgebraicGeometry.axGrothendieck_points`,
`Langlands.Algebra.axGrothendieck_algHom` and Mathlib's
`ax_grothendieck_zeroLocus` and `ax_grothendieck_of_definable`. The latter
uses `FirstOrder.Field.ACF_isComplete` and `FirstOrder.Field.ACF_categorical`.
They reach `IsAlgClosed.ringEquiv_of_equiv_of_char_eq`, which identifies
uncountable algebraically closed fields of the same characteristic and
cardinality up to field isomorphism. Its proof uses the characteristic-zero
case `IsAlgClosed.ringEquiv_of_equiv_of_charZero` and the corresponding
positive-characteristic case, both using
`IsAlgClosed.equivOfTranscendenceBasis` to extend a bijection of
transcendence bases to a field isomorphism.

Integral-model smoothening also uses `CompositionSeries.jordan_holder`
through `Module.length_compositionSeries`. The former gives equivalence
of composition series with the same endpoints in a Jordan–Hölder lattice.
The latter applies it to the lattice of submodules to compute the module
length from a composition series from bottom to top. The length enters
the finiteness argument for the smoothening defect.

`Langlands.GroupScheme.IntegralModel.Greenberg.nonempty_wittDecomposition`
uses `Module.equiv_directSum_of_isTorsion` to give truncated Witt vector
coordinates for a commutative `W(k)`-algebra that is finitely generated
as a module and killed by a power of the residue characteristic. Here
`k` is a perfect field of characteristic `p`. The result applies to
the congruence rings in the Greenberg construction.

#### Other joint-basis dependencies

- `Langlands.GroupScheme.isSimplyConnectedFieldExtension` supplies the
  field-extension step for the joint basis. It uses
  `Langlands.GroupScheme.rootDatumExistence` to give an actual reduced
  root datum of the split maximal torus of a connected reductive group
  over a field. In the other direction,
  `Langlands.GroupScheme.splitReductiveExistence` realizes any finite
  reduced root datum on a finitely generated lattice and its dual over
  every field. `Langlands.GroupScheme.splitCentralIsogenyExistence` lifts
  a central isogeny of split root data to a central isogeny of the actual
  reductive groups. That proof uses
  `Langlands.GroupScheme.splitCommonTorusIsomorphism` for agreement of
  roots and coroots up to reindexing on a common split maximal torus,
  with `Langlands.GroupScheme.splitRankOneCommonTorusIsomorphism` for the
  case where any two roots are linearly dependent. The lattice
  criterion for simply connectedness enters through
  `Langlands.GroupScheme.splitCorootSpanSimplyConnected`, for split
  semisimple field groups with a supplied root datum and spanning
  coroots.
- The Iwasawa construction `Langlands.BruhatTits.Iwasawa.availableIwasawa`
  uses minimal parabolic conjugacy. Its split radical argument
  `Langlands.GroupScheme.splitRadicalWoundQuotient` uses
  `Langlands.GroupScheme.RelativeRoot.commutativePTorsionVectorFactor`
  (CGP B.2.5). Over a field of characteristic `p`, a smooth connected
  commutative affine group satisfying `x^p = 1` on all tests is a product
  of a vector group and a complement whose affine-line maps over the
  separable closure are constant. The factorization uses
  `Langlands.GroupScheme.RelativeRoot.smoothCommutativePTorsionVectorEmbedding`
  (CGP B.1.10), a closed embedding in a vector group for a smooth
  commutative affine field group with the same exponent law in
  characteristic `p`.
- `AddCommGroup.equiv_free_prod_directSum_zmod` decomposes any finitely
  generated abelian group as the product of a finite-rank free abelian
  group and a finite direct sum of cyclic groups of prime-power order.
  It uses `Module.equiv_free_prod_directSum`, the decomposition of
  finitely generated modules over a PID into a finite free module and
  a finite sum of cyclic prime-power quotients.
  `Langlands.GroupScheme.Diagonalizable.exists_splitFiniteIso` applies
  the abelian group theorem to identify a diagonalizable group of
  finitely generated character group with a split torus times a finite
  diagonalizable group over any commutative base ring. This enters the
  split torus domination in `Langlands.GroupScheme.solvableMaximalTorusConjugacy`.
- `Module.equiv_directSum_of_isTorsion` gives the cyclic prime-power
  decomposition for a finitely generated torsion module over a PID.
  For the building comparison,
  `Langlands.GroupScheme.SplitTorusIsogeny.finite_cokernel_of_right_quasiInverse`
  applies it through `Module.finite_of_fg_torsion` to obtain a finite
  cokernel for the map on cocharacters of a split torus isogeny.
- `Submodule.smithNormalForm` diagonalizes the inclusion of a submodule
  of a finite free module over a PID. For the Cartan comparison,
  `Langlands.Plancherel.RenardCartan.IntegralRestriction.finiteIndex_range_of_injective`
  uses its equal-rank consequence to prove that the image of the
  integral pairing has finite index.
  `Langlands.GroupScheme.TorusEndomorphism.exists_surjective_annihilator`
  uses it to obtain a primitive integer functional annihilating the image
  of a noninjective endomorphism of a finite free integer lattice.

#### Relative parabolics and centralizers

- `Langlands.GroupScheme.RelativeRoot.commutativeVectorClassification`
  gives two vector group identifications over algebraically closed fields.
  In characteristic zero,
  `Langlands.GroupScheme.RelativeRoot.commutativeUnipotentVectorCharZero`
  applies to an affine smooth connected commutative group scheme that is
  unipotent. In characteristic `p`,
  `Langlands.GroupScheme.RelativeRoot.smoothCommutativePTorsionVector`
  applies to an affine smooth connected commutative group scheme
  satisfying `x^p = 1` for every scheme test and every point `x` on it.
  Both identifications enter
  `Langlands.GroupScheme.RelativeRoot.centralStableVectorSubgroup`,
  used by `unipotentSemigroupOrderedProduct` and
  `dynamicRootOrderedProduct_of_rayDecomposition` in the standard
  parabolic point theorem `standardParabolicPointsStatement_proof` and
  in the Iwasawa construction. The characteristic-zero case also occurs
  in the split unipotent and torus argument for
  `Langlands.GroupScheme.dynamicCentralizerReductive`.
- `Langlands.GroupScheme.perfectFieldOneDimensionalUnipotent` identifies
  an affine smooth connected unipotent group of dimension one over a
  perfect field with `Gₐ` on all scheme tests. It is used in the split
  solvable argument `Langlands.GroupScheme.algebraicallyClosedSplitSolvable`
  and hence in `dynamicCentralizerReductive`.
  `Langlands.GroupScheme.perfectFieldUnipotentSplit` gives a finite normal
  series with represented one-dimensional vector quotients for affine
  smooth connected unipotent groups over a perfect field. It reaches the
  same centralizer proof through
  `Langlands.GroupScheme.RelativeRoot.splitUnipotentStableVectorSubgroup`
  and `centralizerBorelIntersection`.
- `Langlands.GroupScheme.Diagonalizable.closedSubgroupPresentation`
  gives an isomorphism of any closed subgroup of `D(Λ)` over a field,
  with `Λ` finitely generated abelian, to `D(Λ')` for a finitely
  generated abelian group `Λ'`. The scope includes nonsmooth and
  disconnected subgroups. It enters `dynamicCentralizerReductive`
  through `chevalleyUnipotentEnvelope` and the triangular diagonal
  splitting `triangularDiagonalSplitting`.

## Scope

The field scope includes positive characteristic. The group scope includes
nonsplit and non-quasi-split groups and relative rank zero. The geometric
filtration uses the compact-limit property from
`standardUnipotent_isLimitOfCompactSubgroups_of_standardCocharacterStatement`
and parabolic quotient compactness from
`Langlands.BruhatTits.dynamicParabolicQuotientCompact` on the rational data.
The induction uses the positive half Haar modulus and the Jacquet functor
uses the inverse half, the reciprocal modular convention to Renard's.

## Source

David Renard, *Représentations des groupes réductifs p-adiques*, French
edition dated 9 July 2026
(`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`):
Proposition VI.5.3(ii),(iii) (printed p. 173, PDF p. 179) gives the
transported-factor consequence. The first proof paragraph of Théorème
VI.5.4 (printed p. 174, PDF p. 180) applies exact Jacquet restriction to the
subquotient occurrence in the induction. VI.5.1 (printed pp. 161–162,
PDF pp. 167–168) supplies the geometric-lemma comparison and VI.5.2
(printed p. 173, PDF p. 179) the proper-induction exclusion. The Library
proves the exclusion using first adjointness as in VI.1.2 (printed
pp. 135–136) and compact restriction as in VI.2.1 (printed pp. 137–139).
[Compact restriction and exclusion](RationalCuspidalExtractionFromSpecialVertex.md)
