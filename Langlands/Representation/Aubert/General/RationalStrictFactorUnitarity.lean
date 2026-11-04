import Langlands.Representation.Aubert.General.RationalUnitaryAssociatedJacquetSupport
import Langlands.Representation.Aubert.General.TwoJacquetSchurCharacters
import Langlands.Representation.Aubert.General.RationalCentralTorusValuations
import Langlands.Representation.Filtration.CoarseJacquetFactorization
import Langlands.Representation.Unitary.CentralQuotientForm
import Langlands.Representation.Unramified.SphericalConstituentExistenceProof

/-! # Strict exponents contradict asymmetric actual associated Jacquet factors -/

noncomputable section

set_option maxHeartbeats 800000

universe u v

open CategoryTheory AlgebraicGeometry MeasureTheory
open scoped CategoryTheory.MonObj

namespace Langlands.Aubert.General.RationalPointFamily

open GroupScheme Group.RelativeWeylIndexing SmoothRep
open Langlands.AlgebraicGeometry.PointTopology

variable {k : Type u} [Field k] [ValuativeRel k] [TopologicalSpace k]
  [IsNonarchimedeanLocalField k]
  {T : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
  (i : T.toGrp ⟶ G) (ν : cocharacterLattice T)
  (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
  (hν : IsGenericCocharacter i ν) (hStandard : StandardCocharacterStatement.{u})

local instance instRationalStrictFactorUnitarity1 : TopologicalSpace (RationalPoint k G.X) := pointTopology

variable [LocallyCompactSpace (RationalPoint k G.X)]
  [NonarchimedeanGroup (RationalPoint k G.X)] [T2Space (RationalPoint k G.X)]
  (hU : ∀ I, IsClosed (unipotent i ν I : Set (RationalPoint k G.X)))

/-- Strict normalized Jacquet exponents give an actual positive form under
sufficiency of the strict square-integrability criterion and ambient unimodularity. -/
def strictJacquetPositiveForm
    (hsq : RationalStrictJacquetSquareIntegrabilityStatement.{u, v})
    (hunimod : ∀ g : RationalPoint k G.X, Measure.modularCharacter g = 1)
    (A : SmoothRep.{0, u, max (u + 1) v} ℂ (RationalPoint k G.X))
    (ha : A.IsAdmissible) (hirr : A.IsIrreducible)
    (hc : Nonempty (UnitaryCentralCharacter A.representation))
    (hstrict : HasStrictNormalizedJacquetExponents i ν (isSemidirectDecomposition_of_standardCocharacterStatement i ν hStandard hG hi hν) hU A) :
    InvariantPositiveForm A.representation := by
  classical
  apply Classical.choice
  have := hG.smooth
  let : MeasurableSpace (RationalPoint k G.X ⧸ Subgroup.center (RationalPoint k G.X)) :=
    borel _
  have : BorelSpace (RationalPoint k G.X ⧸ Subgroup.center (RationalPoint k G.X)) := ⟨rfl⟩
  let measure : Measure (RationalPoint k G.X ⧸ Subgroup.center (RationalPoint k G.X)) :=
    Measure.haar
  obtain ⟨_, c, hL2⟩ := hsq k G hG T i hi ν hν hStandard hU A ha hc hstrict measure
  obtain ⟨ℓ, hℓ⟩ := exists_nonzero_smoothDual_of_irreducible_compact_cofinal
    (compactOpenCofinal_of_nonarchimedean _) A.representation A.isSmooth hirr
  exact ⟨c.unimodularCoefficientProductForm hunimod A.isSmooth hirr ℓ.1 hℓ measure (hL2 ℓ)⟩

variable [Mono i.hom.hom.left]
  (hN : HasPointNormalizerComparison i) (hZ : HasPointCentralizerComparison i)
  [Fintype (SimpleRoot i ν)] [Fintype (Weyl i)]
  {CM : CoxeterMatrix (SimpleRoot i ν)}
  (cs : ActualCoxeterSystem (torusPoints i) CM)
  (hLength : RootLengthComparison i ν hN hZ cs)
  (hSimple : PositiveSimpleReflectionComparison i ν hN hZ cs)
  (hMin : minimalityLengthCriterion cs) (hAssoc : associatedSubsetLaws cs)
  (hRoots : HasRelativeRootSystem i)
  (I : Finset (SimpleRoot i ν))
  (n : Group.RelativeWeyl.normalizer (torusPoints i))
  (hn : QuotientGroup.mk n = longestRep cs I)
  (ζ : cocharacterLattice T) (hζ : IsStandardCocharacter i ν (rootSet i ν I) ζ)
  (hsq : RationalStrictJacquetSquareIntegrabilityStatement.{u, v})
  (hHaar : RationalOppositeHaarReciprocityStatement.{u})
  (hunimod : ∀ g : RationalPoint k G.X, Measure.modularCharacter g = 1)
  (σ : SmoothRep.{0, u, max (u + 1) v} ℂ (levi i ν I))
  (F : InductionTwoJacquetFactors ((isSemidirectDecomposition_of_standardCocharacterStatement i ν hStandard hG hi hν) I) (hU I)
    ((isSemidirectDecomposition_of_standardCocharacterStatement i ν hStandard hG hi hν) (associatedSubset cs I)) (hU (associatedSubset cs I)) σ)
  (C : InductionTwoJacquetScalarCharacters ((isSemidirectDecomposition_of_standardCocharacterStatement i ν hStandard hG hi hν) I) (hU I)
    ((isSemidirectDecomposition_of_standardCocharacterStatement i ν hStandard hG hi hν) (associatedSubset cs I)) (hU (associatedSubset cs I)) σ)
  (ha : ((normalizedInductionFunctor ((isSemidirectDecomposition_of_standardCocharacterStatement i ν hStandard hG hi hν) I) (hU I)).obj σ).IsAdmissible)
  (c : UnitaryCentralCharacter
    ((normalizedInductionFunctor ((isSemidirectDecomposition_of_standardCocharacterStatement i ν hStandard hG hi hν) I) (hU I)).obj σ).representation)
  (hzero : ∀ K : Finset (SimpleRoot i ν),
    K ≠ I → K ≠ associatedSubset cs I → K ≠ Finset.univ →
      Subsingleton ((jacquetFunctor ((isSemidirectDecomposition_of_standardCocharacterStatement i ν hStandard hG hi hν) K) (hU K)).obj
        ((normalizedInductionFunctor ((isSemidirectDecomposition_of_standardCocharacterStatement i ν hStandard hG hi hν) I) (hU I)).obj σ)))

include F hLength hSimple hMin hAssoc hRoots hn hζ hsq hHaar hunimod ha c hzero in
/-- The first scalar character cannot be strictly decreasing on every
negative noncentral central-torus test: the actual subspace factor would be
unitary despite its asymmetric associated Jacquet support. -/
theorem InductionTwoJacquetFactors.not_first_strict_bound
    (hσ : σ.IsIrreducible) :
    ¬ (∀ (t : RationalPoint k T.X) (z : Subgroup.center (levi i ν I)),
      ((z : levi i ν I) : RationalPoint k G.X) = t ≫ i.hom.hom →
      IsNoncentralNegativeTorusPoint i ν t → ‖(C.first z : ℂ)‖ < 1) := by
  intro hbound
  let A := (normalizedInductionFunctor ((isSemidirectDecomposition_of_standardCocharacterStatement i ν hStandard hG hi hν) I) (hU I)).obj σ
  let B := subrepresentation A F.subspace
  have hB : B.IsAdmissible :=
    isAdmissible_of_injective (hom (subtype A F.subspace))
      (subtype_injective A F.subspace) ha
  have hstrict : HasStrictNormalizedJacquetExponents i ν (isSemidirectDecomposition_of_standardCocharacterStatement i ν hStandard hG hi hν) hU B :=
    Langlands.Aubert.General.RationalPointFamily.InductionTwoJacquetFactors.subspace_hasStrictNormalizedJacquetExponents F
      (fun K => standardUnipotent_isLimitOfCompactSubgroups_of_standardCocharacterStatement
        i ν hStandard hG hi hν K) hzero
      (not_isNoncentralNegativeTorusPoint_of_fullIndex_center
        i ν hStandard hG hi hν hRoots) C hbound
  have hunitary : IsUnitarizable B.representation :=
    ⟨strictJacquetPositiveForm i ν hG hi hν hStandard hU hsq hunimod
      B hB F.subspace_irreducible ⟨c.restrictSubrepresentation F.subspace⟩ hstrict⟩
  let : Nontrivial σ := repLength_pos_iff.mp (by
    rw [repLength_eq_one_iff.mpr hσ]
    exact zero_lt_one)
  have hnonzero : Nontrivial ((jacquetFunctor ((isSemidirectDecomposition_of_standardCocharacterStatement i ν hStandard hG hi hν) I) (hU I)).obj B) :=
    F.inducing_equiv.symm.injective.nontrivial
  exact not_isUnitarizable_of_associatedJacquet_asymmetry
    i ν hN hZ cs hLength hSimple hMin hAssoc hG hi hν hRoots hStandard
    hU I n hn ζ hζ hHaar B hB hnonzero F.second_subspace_zero hunitary

include F hLength hSimple hMin hAssoc hRoots hn hζ hsq hHaar hunimod ha c hzero in
/-- The second scalar character cannot be strictly decreasing on every
negative noncentral central-torus test: the literal quotient would be
unitary despite the reverse associated Jacquet support asymmetry. -/
theorem InductionTwoJacquetFactors.not_second_strict_bound
    (hsecond : Nontrivial ((jacquetFunctor
      ((isSemidirectDecomposition_of_standardCocharacterStatement i ν hStandard hG hi hν) (associatedSubset cs I)) (hU (associatedSubset cs I))).obj
        ((normalizedInductionFunctor ((isSemidirectDecomposition_of_standardCocharacterStatement i ν hStandard hG hi hν) I) (hU I)).obj σ))) :
    ¬ (∀ (t : RationalPoint k T.X)
      (z : Subgroup.center (levi i ν (associatedSubset cs I))),
      ((z : levi i ν (associatedSubset cs I)) : RationalPoint k G.X) = t ≫ i.hom.hom →
      IsNoncentralNegativeTorusPoint i ν t → ‖(C.second z : ℂ)‖ < 1) := by
  intro hbound
  let A := (normalizedInductionFunctor ((isSemidirectDecomposition_of_standardCocharacterStatement i ν hStandard hG hi hν) I) (hU I)).obj σ
  let B := quotient A F.subspace
  have hB : B.IsAdmissible :=
    Unramified.SphericalExistence.isAdmissible_of_surjective
      (compactOpenCofinal_of_nonarchimedean _) (hom (mkQ A F.subspace))
      (mkQ_surjective A F.subspace) ha
  have hstrict : HasStrictNormalizedJacquetExponents i ν (isSemidirectDecomposition_of_standardCocharacterStatement i ν hStandard hG hi hν) hU B :=
    Langlands.Aubert.General.RationalPointFamily.InductionTwoJacquetFactors.quotient_hasStrictNormalizedJacquetExponents F
      (fun K => standardUnipotent_isLimitOfCompactSubgroups_of_standardCocharacterStatement
        i ν hStandard hG hi hν K) hzero
      (not_isNoncentralNegativeTorusPoint_of_fullIndex_center
        i ν hStandard hG hi hν hRoots) C hbound
  have hunitary : IsUnitarizable B.representation :=
    ⟨strictJacquetPositiveForm i ν hG hi hν hStandard hU hsq hunimod
      B hB F.quotient_irreducible ⟨c.descendQuotient F.subspace⟩ hstrict⟩
  let := hsecond
  have hnonzero : Nontrivial ((jacquetFunctor
      ((isSemidirectDecomposition_of_standardCocharacterStatement i ν hStandard hG hi hν) (associatedSubset cs I)) (hU (associatedSubset cs I))).obj B) :=
    F.second_quotient_equiv.injective.nontrivial
  exact not_isUnitarizable_of_associatedJacquet_reverse_asymmetry
    i ν hN hZ cs hLength hSimple hMin hAssoc hG hi hν hRoots hStandard
    hU I n hn ζ hζ hHaar B hB F.first_quotient_zero hnonzero hunitary

end Langlands.Aubert.General.RationalPointFamily
