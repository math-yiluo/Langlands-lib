# Strict normalized Jacquet exponents imply square integrability: proof

`Langlands.Aubert.General.RationalPointFamily.rationalStrictJacquetSquareIntegrability`
proves the proposition
`Langlands.Aubert.General.RationalPointFamily.RationalStrictJacquetSquareIntegrabilityStatement.{u, v}`
of the module
`Langlands.Representation.Aubert.General.RationalSquareIntegrabilityStatement`,
exactly as stated. [Statement](RationalSquareIntegrabilityStatement.md)

The theorem has the two universe parameters `u` (field) and `v`
(representation carriers live in `max (u + 1) v`), and no parameter or
hypothesis besides those of the proposition. Its axioms are `propext`,
`Classical.choice` and `Quot.sound`.

## What is proved

Let `k` be any nonarchimedean local field, of either characteristic, `G` a
connected reductive group scheme over `k`, `i : T → G` a maximal split torus
and `ν` a generic cocharacter of `T`, with `G(k)` carrying the canonical
evaluation topology `pointTopology`. Let `A` be an admissible smooth complex
representation of `G(k)` with a unitary central character such that, for every
set `J` of simple roots, every exponent `χ` of the actual normalized Jacquet
module along the actual standard parabolic of type `J` (a character of the full
center of the actual standard Levi) satisfies `‖χ(z)‖ < 1` at every central Levi
point `z` coming from a torus point in the closed negative chamber with some
simple-root value of valuation below one. Then for every Borel Haar measure on
`G(k) / Z(G(k))`, every coefficient of `A` is square integrable modulo the full
center (`IsSquareIntegrableModCenter`).

This is the sufficiency direction of W. Casselman, *Introduction to the theory
of admissible representations of p-adic reductive groups*, draft of 1 May 1995,
Theorem 4.4.6 (p.45), with the exponent conventions of pp.44–45, in the
normalization described in the statement's Markdown. No splitness,
quasi-splitness, characteristic, finite-length, irreducibility or nonempty-root
hypothesis is added: groups that are not quasi-split, fields of positive
characteristic and groups whose relative root system is empty are all covered.

## The Lean proof

The proof is one application:

```
rationalStrictJacquetSquareIntegrabilityReduction.{u, v}
  BruhatTits.SpecialCompact.jointSpecialCompactBasisExistence.{u}
```

- `Langlands.Aubert.General.RationalPointFamily.rationalStrictJacquetSquareIntegrabilityReduction`
  (module
  `Langlands.Representation.Aubert.General.RationalSquareIntegrabilityReductionProof`)
  proves `RationalStrictJacquetSquareIntegrabilityReductionStatement.{u, v}`,
  which is by definition the implication
  `JointSpecialCompactBasisExistenceStatement.{u} →
  RationalStrictJacquetSquareIntegrabilityStatement.{u, v}`.
  [Reduction](RationalSquareIntegrabilityReductionProof.md)
- `Langlands.BruhatTits.SpecialCompact.jointSpecialCompactBasisExistence`
  (module `Langlands.BruhatTits.SpecialCompact.JointBasisProof`) proves
  `JointSpecialCompactBasisExistenceStatement.{u}` with no hypotheses.
  [Joint witness](../../../BruhatTits/SpecialCompact/JointBasisProof.md)

Both universe instantiations are the ones of the statements, so the term has
exactly the target type.

## The mathematical argument

The argument follows the structure of Casselman's proof: a Cartan decomposition
reduces the integral to double cosets `K a K` with `a` in the negative chamber;
on those, coefficients decay through the Jacquet module exponents and volumes
grow at most like the inverse modulus; strictness makes the resulting series
converge.

**Geometry (the joint witness).** `jointSpecialCompactBasisExistence` gives, for
the given `G`, `T`, `i` and `ν`, one apartment datum `D` of a valid corrected
Kaletha–Prasad building assignment, a special vertex `x`, the subgroup
`K0 = D.specialCompactSubgroup x` (compact, open, maximal), a represented torus
centralizer with its character comparison, Iwasawa products for `G(k)` and all
actual standard Levis, the Renard Cartan comparisons for `G(k)` and the standard
Levis, and a simultaneous standard compact-open basis at `K0`, all at the same
`D` and `x`. Its proof composes `Langlands.Geometry.Building.bruhatTitsAvailability`
(existence of a valid assignment) with
`Langlands.BruhatTits.SpecialCompact.availableSimultaneousStandardBasis`, via
`jointSpecialCompactBasisExistence_of_availability_and_basis`.

**Cartan cover.** In `rationalStrictJacquetSquareIntegrabilityReduction`,
`exists_isFiniteLatticeTransversal` and `rationalFiniteChamberCartanCover` turn
these comparisons into one integral cocharacter `gen a` for each simple root
`a` (pairing positively with `a`, trivially with the other simple roots) and a
finite set `T` with
`G(k) = K0 · ϖ^(Σ n_a gen_a) · T · K0 · Z(G(k))`, `n` ranging over natural
tuples. This is the analogue of Casselman's `G = Γ A⁻ Γ`, with the full center
of `G(k)` in place of the split component `A_Δ`.

**Coefficient decay.** `rationalCompactTranslateCoefficientBound` applies the
admissibility and the strict normalized exponent hypothesis to the faces
`J a = (all simple roots) \ {a}`. It chooses points `z a` in the full center of
the actual standard Levi of type `J a` equal to `ϖ^(gen a)`, and gives, for
every vector and smooth functional, radii `r a` and a constant `C` with
`|c(k₁ ϖ^(Σ n_a gen_a) t k₂)| ≤ C ∏ r_a^(n_a)` uniformly on `K0`, `T`, `K0`,
and `r_a² · δ_a(z_a)⁻¹ < 1`, where `δ_a` is the Haar modulus
`HaarModulus.closedRestrictCharacter` of the actual unipotent radical of type
`J a`. This plays the role of Casselman's 4.3.4: its proof chain
(`rationalLatticeCoefficientDecay`, `haarNormalizedLatticeCoefficientBound`,
`normalizedJacquetCompressionSpectrum`, `compressedLatticeCoefficientBound`)
compares coefficients with the action of central Levi points on the actual
Jacquet module through the compression operators on fixed vectors of a member
of the simultaneous basis, and bounds the eigenvalues of that finite-dimensional
action by the strict exponents.

**Volumes.** `rationalLatticeQuotientVolume` bounds the measure of the image of
`K0 ϖ^(Σ n_a gen_a) t K0` in `G(k)/Z(G(k))` by `D ∏ δ_a(z_a)^(-n_a)` with one
constant `D`, uniformly in `n` and `t ∈ T` (Casselman's 4.4.5).

**Integration.** `Langlands.cartanLatticeL2` combines the cover, the unitary
central character, the coefficient bounds and the volume bounds, with weights
`w_a = δ_a(z_a)⁻¹`. The quotient is covered by the images of the cells
`K0 ϖ^(Σ n_a gen_a) t K0`; on the cells of index `n` the squared coefficient is
at most `C² ∏ r_a^(2 n_a)` and their total measure is at most
`|T| · D · ∏ w_a^(n_a)`, so the squared integral is bounded by a constant times
`∏_a Σ_n (r_a² w_a)^n`, a product of convergent geometric series because
`r_a² w_a < 1`. Its proof applies `finiteLatticeCellL2`. The conclusion is
`IsSquareIntegrableModCenter` for the given representation and measure.

When there are no simple roots the same proof applies: the lattice has one
tuple, all products are one, and the cover and volume bounds still hold.

## Declaration-level dependencies

The inventory follows constants in both the types and the values of reached
declarations using `Lean.ConstantInfo.getUsedConstantsAsSet`. The closure of
`rationalStrictJacquetSquareIntegrabilityReduction` has 77,320 constants and
that of `jointSpecialCompactBasisExistence` has 213,404. The classification
theorems and character-independence results below enter through the joint
witness, including its building, Iwasawa and Cartan constructions.

### Classification

- `Langlands.GroupScheme.splitHighestWeightClassification` applies to
  finite-dimensional algebraic matrix representations of an affine group
  with a supplied split pinning over an arbitrary field. Dominant weights
  occur as highest weights, highest-weight representations are isomorphic
  exactly when their weights agree, and each irreducible representation has
  a unique dominant highest weight. In `Langlands.GroupScheme`,
  `GaloisPinningData.dominantTitsClass`,
  `GaloisPinningData.exists_intertwiner_galoisTwist`,
  `GaloisPinningData.titsCSAOf_isBrauerEquivalent` and
  `GaloisPinningData.titsObstructionValue_transfer_of_isDominantWeight`
  use this theorem in the construction and comparison of Tits obstructions.
  `SplitPinning.HighestSubquotientData.isDominantWeight_of_maximal` also
  uses it for irreducible highest subquotients. The exclusions
  `TitsIndexData.not_hasRankOneE6BranchIndex` and
  `TitsIndexData.not_hasRankOneD4InnerOrNoFixedLeafIndex` bring the Tits
  obstruction into `localRankOneTitsIndex`.
  The `D₄` proof computes the corestriction of the degree-two division
  algebra class by
  `Langlands.ClassFieldTheory.Local.localBrauerInvariant_corestriction` and
  `Langlands.ClassFieldTheory.Local.localBrauerInvariant_division_degree_two`.
  These use `Langlands.ClassFieldTheory.Local.localBrauerInvariant`, the
  classification of Brauer classes of a nonarchimedean local field by
  \(\mathbb{Q}/\mathbb{Z}\).
- `Langlands.GroupScheme.localRankOneClassification` applies
  `localRankOneTitsIndex` and `localRankOneClassification_of_indexStatements`
  to obtain the Prasad–Raghunathan list for simply connected absolutely almost
  simple groups of relative rank one over nonarchimedean local fields.
  `Langlands.Geometry.Building.affineIwahoriTits` uses this classification
  and the local Kneser–Tits theorem. The latter uses the rank-one list through
  `Langlands.GroupScheme.localKneserTits_of_rankOneLeviFactors_of_classification`
  and
  `Langlands.GroupScheme.localAbsolutelyAlmostSimpleRankOneKneserTits_of_classification`.
  In the index argument,
  `Langlands.GroupScheme.localRankOneTitsIndex_or_E6_or_residual_of_componentFactor`
  uses `Langlands.GroupScheme.absolutelyAlmostSimpleCartanClassification`.
  For an absolutely almost simple group over any field with a supplied Tits
  index, this gives a numbering of the absolute vertices by one of the
  irreducible finite Cartan matrices, matching all Cartan entries. Its proof
  uses `Langlands.LinearAlgebra.finiteCartanClassification`,
  `Langlands.LinearAlgebra.FiniteCartanMatrix.classification_of_connected` and
  `Langlands.LinearAlgebra.FiniteCartanMatrix.classification_from_leaf`.
- In `Langlands.GroupScheme`, `innerTypeANormOne` identifies simply connected
  absolutely almost simple groups of inner type `A` over a field with
  reduced-norm-one groups of central simple algebras, using
  `specialLinearInnerFormNormOne` for inner forms of split special linear
  groups. `outerTypeARankOneHermitian` identifies the outer `A₂` and `A₃`
  rank-one cases with Witt-index-one special unitary groups over separable
  quadratic extensions. Its input `outerTypeAHermitianPresentation` gives
  determinant-one isometry models on all scheme tests for outer `Aₙ`
  with the reversal star action and both endpoints distinguished.
- `Langlands.GroupScheme.typeCRankOneQuaternionic` identifies the type `C₂`
  and `C₃` rank-one cases with Witt-index-one groups of antihermitian
  forms over central quaternion division algebras. It uses
  `typeCDivisionForm` for simply connected absolutely almost simple groups
  of type `Cₙ` for `n ≥ 2`. This gives a matrix antihermitian form over
  a central division algebra, its Witt index and its distinguished
  vertices, via `typeCQuasiSplitInnerForm` (the split symplectic inner model)
  and `symplecticInnerFormAntihermitian` (the division-algebra presentation
  of forms of that model).
- `Langlands.GroupScheme.typeDRankOneSpin_of_classicalTypeDSpinPresentation`
  identifies the outer `D₄` and inner `D₅` rank-one cases with quaternionic
  spin covers of Witt index one. Its input `classicalTypeDSpinPresentation`
  gives the spin-cover presentation and Witt index for simply connected
  absolutely almost simple groups of type `Dₙ` for `n ≥ 4` whose star action
  fixes all nonfork vertices. `classicalTypeDAlignedSpinCover` supplies a
  cover whose kernel is killed by the first fundamental weight on the
  pinning torus over a separable closure. `alignedSpinCoverTitsIndex`
  compares its Witt index with the split rank and describes the nonfork
  distinguished vertices.
- In the index enumeration, `Langlands.GroupScheme.localRankOneTitsIndexReduction` uses
  `typeG2CayleyPresentation`, the realization of simply connected
  absolutely almost simple groups of type `G₂` as automorphism groups of
  Cayley algebras, to rule out the rank-one `G₂` case over local fields.
- `Langlands.GroupScheme.RelativeRoot.commutativeVectorClassification`
  identifies smooth connected commutative affine groups over an algebraically
  closed field as vector groups in two cases. The group is unipotent in
  characteristic zero, or multiplication by `p` is trivial on all test
  points in characteristic `p`. The Iwasawa proof `availableIwasawa` reaches
  this result through `RelativeRoot.unipotentSemigroupOrderedProduct` and
  `RelativeRoot.centralStableVectorSubgroup`.
- `Langlands.GroupScheme.perfectFieldOneDimensionalUnipotent` identifies
  smooth connected affine unipotent groups of dimension one over a perfect
  field with the additive vector group on all scheme tests. The construction
  of `unramifiedFacetRootDatum` uses it through `integralOppositeFactors`,
  `IsMaximalSplitTorus.comp_iff_of_perfect_field_unipotent_kernel` and
  `perfectFieldUnipotentSplit`.
- The split root datum inputs in `Langlands.GroupScheme` include
  `splitReductiveExistence` for realization, `splitCentralIsogenyExistence`
  for lifting central root datum isogenies and `splitSemisimpleRootDatum`
  for the semisimplicity criterion. In the Cartan comparison,
  `ZeroSubgroupDatum.coverImageCentralizerNormKernel` uses
  `isSimplyConnectedFieldExtension`, which applies `splitCentralIsogenyExistence`.
  That theorem passes `splitCommonTorusIsomorphism` to
  `splitCentralIsogenyExistence_of_commonTorusIsomorphism` to identify the
  constructed central quotient with the target. Over any field,
  `Langlands.GroupScheme.splitCommonTorusIsomorphism` gives an isomorphism
  of connected reductive groups with a common split maximal torus and
  indexed roots and coroots that match under a reindexing. The isomorphism
  commutes with the two torus embeddings. The proof combines
  `splitRankOneCommonTorusIsomorphism` for semisimple rank at most one with
  `splitCommonTorusLeviGluing`, which uses matching rank-at-most-one
  centralizer Levis to construct the comparison over an algebraic closure
  and descends the resulting isomorphism. The same
  common-torus theorem also enters `Langlands.GroupScheme.pinnedIsomorphism`
  in the proof of `innerTypeANormOne`. Over any field, `pinnedIsomorphism`
  uniquely lifts a based equivalence of the full root data of two split
  pinnings to an isomorphism of the pinnings with the specified lattice
  and root-index maps.
- The local Kneser–Tits inputs reach Mathlib's
  `IsSimpleRing.exists_algEquiv_matrix_divisionRing_finite`, the
  Artin–Wedderburn matrix presentation for finite-dimensional simple
  algebras, through `IsSimpleRing.exists_algEquiv_matrix_of_isAlgClosed`
  in `Langlands.CentralSimple.exists_matrix_chart`. The latter uses the
  full matrix presentation over an algebraically closed extension.
  Mathlib's `littleWedderburn` identifies a finite division ring as a
  field and supplies commutativity of the residue division ring in the
  local division-algebra argument `Langlands.CentralDivision.localSK1`.
- The field comparison `Langlands.Algebra.axGrothendieck_algHom` uses Mathlib's
  classification results `IsAlgClosed.ringEquiv_of_equiv_of_char_eq`,
  `IsAlgClosed.ringEquiv_of_equiv_of_charZero` and
  `IsAlgClosed.equivOfTranscendenceBasis` to compare algebraically closed
  fields by characteristic and transcendence basis.

Both branches reach the predicates
`Langlands.Plancherel.RenardCartan.HasSpecialCompactValuationClassification`
and `Langlands.Plancherel.RenardCartan.HasSameCompactLeviClassification`.
Here `Z` represents the centralizer of the actual maximal split torus.
The ambient predicate says that two dominant points `z, z' ∈ Z(k)` give
the same `K0` double coset in `G(k)` exactly when
`z' * z⁻¹ ∈ rationalCommonNormKernel Z`. The Levi predicate uses the same
kernel condition for double cosets in the corresponding actual standard
Levi, with dominance defined by the Levi's own positive relative roots
and the compact subgroup given by the preimage of `K0`. The strict exponent
test still uses the torus-image points in the full center of the Levi.
The closure contains no classification theorem for smooth representations
of a local group.

### Character and weight independence

- Mathlib's `linearIndependent_monoidHom` is Dedekind–Artin independence
  for multiplicative maps preserving one into a commutative domain. It
  enters the unit-evaluation arguments via
  `Langlands.Geometry.Building.SplitTorusUnitDetection.eq_zero_of_evaluateUnits_eq_zero`,
  `Langlands.GroupScheme.splitTorus.eq_zero_of_evaluateUnits_eq_zero` and
  `Langlands.Algebra.HopfPointIntegralClosure.eq_zero_of_forall_evalUnits_eq_zero`.
  `Langlands.GroupScheme.TorusDensity.exists_lev_conjFamily_ne_zero` applies
  it to characters on a product of multiplicative groups.
  `Langlands.BruhatTits.RationalPoints.CentralNormKernel.eq_zero_of_sum_mul_pow_eq_zero`
  applies it to powers of distinct field elements. The direct uses for
  field embeddings and Galois actions include
  `Langlands.GroupScheme.exists_stabilizer_sum_ne_zero`,
  `Langlands.GroupScheme.GaloisRingCover.tensorHom_bijective`,
  `Langlands.GroupScheme.Descent.galoisFunctions_linearIndependent`,
  `Langlands.CyclicNorm.exists_weightedTrace_ne_zero` and
  `Langlands.LinearAlgebra.GaloisFixedBasis.linearIndependent_automorphisms`.
  The Mathlib field-theory routes
  pass through `linearIndependent_algHom_toLinearMap`,
  `linearIndependent_toLinearMap`, `finrank_algHom`,
  `FixedPoints.rank_le_card` and `groupCohomology.Hilbert90.aux_ne_zero`.
  `FixedPoints.rank_le_card` uses
  `FixedPoints.linearIndependent_smul_of_linearIndependent`, which sends a
  finite family of field elements independent over the fixed field to
  independent functions on the acting group by taking their translates.
  Among the downstream declarations are
  `Langlands.GroupScheme.GaloisVectorDescent.coeff_eq_zero_of_sum_eq_zero`,
  `Langlands.GroupScheme.GaloisDescent.galMatrix_isUnit`,
  `Langlands.GroupScheme.GaloisLineDescent.exists_coboundary` and
  `Langlands.GroupScheme.WeilGm.isTorus_of_finite_separable`. They use
  field-homomorphism independence in descent and the arithmetic of tori.
- Mathlib's `linearIndepOn_isGroupLikeElem` and `linearIndep_groupLikeVal`
  express independence of group-like elements of torsion-free coalgebras
  over a domain.
  They enter the base-change and basis constructions
  `Langlands.GroupLike.baseChange_bijective`,
  `Langlands.GroupLike.domainBaseChange_bijective`,
  `Langlands.GroupLike.basisOfSpan` and
  `Langlands.GroupScheme.Unipotent.groupLikeBasis`, and the reconstruction
  results `Langlands.MonoidAlgebra.liftGroupLikeBialgHom_injective` and
  `Langlands.MonoidAlgebra.monomialGroupLikeEquiv`.
  In `Langlands.GroupScheme.Diagonalizable`,
  `groupLike_mem_of_span_eq_top` and `closedSubgroupPresentation` identify
  the group-like basis in diagonalizable subgroup presentations.
  `Langlands.CoalgebraDescent.subcoalgebra_groupLike_spanning` and
  `Langlands.CoalgebraDescent.exists_finite_convolutionDualEquivPi` use
  group-like coordinates for coalgebra descent.
  `Langlands.CommutativeAlgebra.DiagonalIsomorphismLocus.characterEquiv`
  and `Langlands.CentralTorusExtensionHopf.exists_map_eq_single` use
  independence for character lattices of diagonalizable groups and for
  images in the coordinate algebra of a central torus, respectively.
- `Langlands.GroupScheme.CharacterLattice.linearIndepOn_of_comul` gives
  independence of nonzero elements whose comultiplication is their tensor
  square. It proves `Langlands.GroupScheme.CharacterUnits.linearIndependent_unit`,
  the independence of the coordinate functions of distinct rational
  characters of an affine group over a field. In `Langlands.GroupScheme`,
  `MatrixRepresentation.exists_characterCoefficient` uses it to separate
  those functions by linear functionals on the coordinate algebra. The
  resulting `MatrixRepresentation.characterCoefficient` and
  `MatrixRepresentation.characterProjector` give
  `MatrixRepresentation.characterSpace_iSupIndep`, used by
  `SplitPinning.iSupIndep_representationWeightSpace` for weights of
  algebraic representations. On the coordinate side
  `CoordinateWeights.exists_characterCoefficient` likewise gives
  `CoordinateWeights.cotangentWeightSpace_iSupIndep` for the coordinate
  weight decomposition. `SplitTorusQuotientFactor.coordMap_injective` and
  `SplitTorusQuotientFactor.free_finite` use the same independence of
  character functions for split torus quotients.
- `Langlands.GroupScheme.rationalCharacterLattice` embeds the character
  functions of a connected reductive group over a field `k` in the fraction
  field of its coordinate algebra. It carries their `k`-linear independence
  into that field and applies `Langlands.GroupScheme.CharacterLattice.free_and_finite`.
  The algebraic argument takes a multiplicative map `w` from an abelian
  group `M` into `L` for a field extension `L/k`, with `k`-linearly
  independent values. For a subgroup `P` of `M`,
  `Langlands.GroupScheme.CharacterLattice.linearIndependent_out_adjoin`
  proves independence of the values on representatives of distinct cosets
  in `M/P` over the `k`-subalgebra generated by `w(P)`. Expanding each scalar
  in the `k`-span of `w(P)` gives a relation over `k` supported in the
  distinct cosets. `Langlands.GroupScheme.CharacterLattice.linearIndependent_out_field`
  proves the same independence over the intermediate field generated by
  `w(P)` via Mathlib's `LinearIndependent.iff_fractionRing`.
  `Langlands.GroupScheme.CharacterLattice.finite_quotient` uses the field
  version when `M/P` is torsion and the values lie in a finitely generated
  `k`-subalgebra. The representatives' values are algebraic over the enlarged
  field, and their span injects into a finite-dimensional residue field
  of the algebra generated by the same generators over that field.
  `free_and_finite` takes `P` to be the integral span of a maximal independent
  family. It proves that family is finite by
  `Langlands.GroupScheme.CharacterLattice.finite_of_linearIndepOn`, which
  uses algebraic independence of the corresponding values, and uses
  `Langlands.GroupScheme.CharacterLattice.isAddTorsionFree` for freeness.
  The building input
  `Langlands.BruhatTits.IntegralModels.UnramifiedTorusNeutralFiniteGeneration.characterDual_finite`
  applies `rationalCharacterLattice` to the character group of a torus in the
  unramified integral model argument.
- `Langlands.LieKolchin.iSupIndep_weightSpace` gives independence of the
  weight spaces for a linear action, used in
  `Langlands.LieKolchin.exists_common_eigenvector_derivedSeries`.
  `Langlands.GroupScheme.RelativeRoot.iSupIndep_actionWeightSpace` and
  `Langlands.GroupScheme.PointedCoordinateWeights.tensorWeightSpace_iSupIndep`
  give directness of split-torus weight spaces for actions and for tensors
  of pointed coordinate algebras, respectively.
  `Langlands.GroupScheme.RelativeRoot.HomogeneousVectorCoordinates.independent_weightSpaces`
  gives directness from finite homogeneous coordinates for the split-torus
  action on a vector group.
  `Langlands.GroupScheme.GeneralLinear.CocharacterDiagonal.iSupIndep_weightColumns`
  separates the character columns of a split-torus representation over a
  commutative ring by its universal Laurent coefficients.
  `Langlands.GroupScheme.FiniteMatrixAlgebraTorusWeights.rowWeightSpace_iSupIndep`
  uses the projections of a split torus in the units of a matrix algebra
  over a division algebra to give independent row weight spaces over the
  division algebra. Mathlib's
  `Module.End.independent_genEigenspace`, `Module.End.independent_maxGenEigenspace`
  and `Module.End.eigenspaces_iSupIndep` enter through the structural gradings
  `Langlands.Algebra.SemisimpleDerivation.eigenGrading` and
  `Langlands.GroupScheme.CentralSurjectionImage.EigenGrading.isInternal_eig`.
  The coprime-order independence theorem `Subgroup.independent_of_coprime_order`
  enters via `Sylow.directProductOfNormal` in the group-theoretic inputs to
  `Langlands.ClassFieldTheory.Local.finitePGroupNormH2Vanishing`.

In the coefficient argument, the strict bound holds immediately for a zero
eigenvalue. For a nonzero compression eigenvalue, the Jacquet quotient map
sends the eigenvector to a nonzero eigenvector of the normalized Levi action.
There `Langlands.exists_centralExponent_of_generalized_eigenvector` uses
`EndomorphismBound.exists_common_eigenvector` on a finite-dimensional space
of fixed vectors to detect a full-center exponent. The common eigenvector
gives the uniform generalized-character condition with power one.
`Langlands.StrictCartanBound.exists_eigenvalue_bound_lt` then applies the
strict exponent bound in finite dimension. That lemma and
`Langlands.StrictCartanBound.dual_apply_eq_compressedAction` are the
arbitrary finite-dimensional lemmas used from
`Langlands.Representation.Exponents.StrictCartanCoefficientBoundProof`.

### Adjointness, the geometric lemma and cuspidal support

- Mathlib's `Rep.resCoindAdjunction` for ordinary linear representations
  makes restriction along a monoid homomorphism left adjoint to algebraic
  coinduction. In the joint witness it enters the cohomology for
  `Langlands.GroupScheme.dimensionLEOneTorusCocycleVanishing` and unramified
  integral models. In particular `Langlands.Tate.coinduced_tate_neg` uses
  `groupHomology.indIso`, whose argument uses preservation of projectives
  by subgroup restriction via that adjunction.
- `Langlands.AlgebraicGeometry.FaithfullyFlatCoalgebraDescent.coinvariantsAdjunction`
  relates the descent comparison functor to coalgebra coinvariants, with
  counit `descentMap`. Here `ModuleCat.extendRestrictScalarsAdj` supplies
  the comonad via extension and restriction of scalars. The faithfully
  flat case is used in affine descent for the simply connected cover.
  Both branches use
  `Langlands.GroupScheme.Corepresented.adjunctionPointsEquiv`, the
  multiplicative point comparison from the relative global-sections and
  spectrum adjunction `algΓAlgSpecAdjunction`. For instance,
  `Langlands.GroupScheme.Standard.isRepresentedBy_leviHom` uses it for
  the represented intersections that define standard Levis.
  `Langlands.GroupScheme.AffineWeil.counitTrans` and
  `Langlands.GroupScheme.AffineWeil.unitTrans` implement the comparison
  of diagonalizable lattice functors with the affine Weil restriction
  point functor. They enter through `Langlands.GroupScheme.affineWeilSplitRank`
  in the building proof.
- The underlying scheme and module arguments also reach
  `AlgebraicGeometry.ΓSpec.adjunction` for global sections and spectrum,
  `PresheafOfModules.sheafificationAdjunction` for sheafification, and
  `AlgebraicGeometry.Scheme.Modules.pullbackPushforwardAdjunction` for
  pullback and pushforward of sheaves of modules.
- The closure contains no declaration of parabolic Frobenius reciprocity,
  second adjointness or the Bernstein–Zelevinsky geometric lemma. The
  geometric irreducibility and connectedness results concern schemes.
  Frobenius endomorphisms and elements occur in the arithmetic inputs, and
  `classifyingSpaceUniversalCover` enters through homological resolutions
  of ordinary representations.
- The declarations reached from `Langlands/Representation/CuspidalSupport`
  are `Langlands.Compact.dual_averageMap_eq_of_mem_fixedVectors`, for
  compact-open averaging on the smooth dual, and
  `Langlands.GroupScheme.SplitTorusValuation.tendsto_uniformizerUnit_pow_zero`,
  for convergence of uniformizer powers to zero. The closure contains no
  cuspidal-support theorem.
