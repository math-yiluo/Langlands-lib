import Langlands.Representation.Aubert.General.RationalGeometricFiltrationCollapse
import Langlands.Representation.Aubert.General.RationalAssociatedCentralCharacterSigns
import Langlands.Representation.Aubert.General.TwoJacquetSchurCharacters
import Langlands.Representation.Smooth.Admissibility.EquivalenceProof
import Langlands.Representation.CuspidalSupport.GroupTransport

/-! # Schur characters from the actual associated Jacquet isomorphism -/

noncomputable section

set_option maxHeartbeats 800000

universe uG uH uV u v

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Aubert.General

/-- Admissibility transports along an actual smooth isomorphism to a
continuous group-equivalence pullback, including smoothness. -/
theorem smooth_isAdmissible_of_iso_pullback
    {H : Type uG} [Group H] [TopologicalSpace H]
    {K : Type uH} [Group K] [TopologicalSpace K]
    (e : H ≃ₜ* K) (A : SmoothRep.{0, uH, uV} ℂ K)
    (B : SmoothRep.{0, uG, uV} ℂ H)
    (E : B ≅ (SmoothRep.pullbackFunctor e).obj A)
    (ha : A.IsAdmissible) : B.IsAdmissible :=
  Langlands.isAdmissible_of_equiv (SmoothRep.equivOfIso E).symm
    (Langlands.isAdmissible_comp_continuousMulEquiv A.representation e ha)

/-- Scalar characters on nonzero smooth objects are compatible with an
actual isomorphism to a continuous group-equivalence pullback. -/
theorem smooth_scalarCharacters_eq_of_iso_pullback
    {H : Type uG} [Group H] [TopologicalSpace H]
    {K : Type uH} [Group K] [TopologicalSpace K]
    (e : H ≃ₜ* K) (A : SmoothRep.{0, uH, uV} ℂ K)
    (B : SmoothRep.{0, uG, uV} ℂ H)
    (E : B ≅ (SmoothRep.pullbackFunctor e).obj A)
    (hn : Nontrivial A)
    (χB : Subgroup.center H →* ℂˣ) (χA : Subgroup.center K →* ℂˣ)
    (hB : B.HasCentralCharacter χB) (hA : A.HasCentralCharacter χA) :
    χB = χA.comp (Subgroup.centerCongr e.toMulEquiv).toMonoidHom := by
  let : Nontrivial ((SmoothRep.pullbackFunctor e).obj A) := hn
  let : Nontrivial B := (SmoothRep.equivOfIso E).symm.injective.nontrivial
  apply MonoidHom.ext
  intro z
  exact scalarCharacter_eq_of_pullback_equiv e.toMulEquiv
    B.representation A.representation (SmoothRep.equivOfIso E) χB χA hB hA z

namespace RationalPointFamily

open GroupScheme Group.RelativeWeylIndexing SmoothRep
open Langlands.AlgebraicGeometry.PointTopology

variable {k : Type u} [Field k] [TopologicalSpace k]
  {T : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
  (i : T.toGrp ⟶ G) [Mono i.hom.hom.left] (ν : cocharacterLattice T)
  (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
  (hν : IsGenericCocharacter i ν) (hStandard : StandardCocharacterStatement.{u})

local instance instRationalAssociatedJacquetSchurCharacters1 : TopologicalSpace (RationalPoint k G.X) := pointTopology

variable [LocallyCompactSpace (RationalPoint k G.X)]
  [NonarchimedeanGroup (RationalPoint k G.X)]
  (hU : ∀ J, IsClosed (unipotent i ν J : Set (RationalPoint k G.X)))
  (hConj : StandardLeviConjugationStatement.{u})
  (hN : HasPointNormalizerComparison i) (hZ : HasPointCentralizerComparison i)
  [Fintype (SimpleRoot i ν)] [Fintype (Weyl i)]
  {CM : CoxeterMatrix (SimpleRoot i ν)}
  (cs : ActualCoxeterSystem (torusPoints i) CM)
  (hLength : RootLengthComparison i ν hN hZ cs)
  (hSimple : PositiveSimpleReflectionComparison i ν hN hZ cs)
  (hMin : minimalityLengthCriterion cs) (hAssoc : associatedSubsetLaws cs)
  (I : Finset (SimpleRoot i ν))
  (n : Group.RelativeWeyl.normalizer (torusPoints i))
  (hn : QuotientGroup.mk n = longestRep cs I)
  (σ : SmoothRep.{0, u, max (u + 1) v} ℂ (levi i ν I))
  (E : pointInducedJacquetObject i ν hG hi hν hStandard hU
      (associatedSubset cs I) I σ ≅
    (pullbackFunctor (associatedLeviConjugationEquiv i ν hG hi hν hConj
      hN hZ cs hLength hSimple hMin hAssoc I n hn).symm).obj σ)

include E in
/-- The actual associated Jacquet isomorphism supplies admissibility from
admissibility of the inducing object. -/
theorem pointAssociatedJacquet_isAdmissible_of_iso (haσ : σ.IsAdmissible) :
    (pointInducedJacquetObject i ν hG hi hν hStandard hU
      (associatedSubset cs I) I σ).IsAdmissible :=
  smooth_isAdmissible_of_iso_pullback
    (associatedLeviConjugationEquiv i ν hG hi hν hConj
      hN hZ cs hLength hSimple hMin hAssoc I n hn).symm σ _ E haσ

include E in
/-- Every scalar-character pair for these actual Jacquet objects has the
specified full-center conjugation law. -/
theorem InductionTwoJacquetScalarCharacters.second_eq_associated_of_iso
    (hσ : σ.IsIrreducible)
    (C : InductionTwoJacquetScalarCharacters
      (isSemidirectDecomposition_of_standardCocharacterStatement
        i ν hStandard hG hi hν I) (hU I)
      (isSemidirectDecomposition_of_standardCocharacterStatement
        i ν hStandard hG hi hν (associatedSubset cs I))
      (hU (associatedSubset cs I)) σ) :
    C.second = associatedLeviCentralCharacter i ν hG hi hν hConj
      hN hZ cs hLength hSimple hMin hAssoc I n hn C.first := by
  have hnσ : Nontrivial σ := repLength_pos_iff.mp (by
    rw [repLength_eq_one_iff.mpr hσ]
    exact zero_lt_one)
  exact smooth_scalarCharacters_eq_of_iso_pullback
    (associatedLeviConjugationEquiv i ν hG hi hν hConj
      hN hZ cs hLength hSimple hMin hAssoc I n hn).symm σ
    (pointInducedJacquetObject i ν hG hi hν hStandard hU
      (associatedSubset cs I) I σ) E hnσ
    C.second C.first C.second_scalar C.first_scalar

include E in
/-- Construct the actual admissible-Schur scalar characters together with
their full-center associated-Levi conjugation identity. -/
def associatedJacquetScalarCharactersOfIso
    (hσ : σ.IsIrreducible) (haσ : σ.IsAdmissible) :
    { C : InductionTwoJacquetScalarCharacters
        (isSemidirectDecomposition_of_standardCocharacterStatement
          i ν hStandard hG hi hν I) (hU I)
        (isSemidirectDecomposition_of_standardCocharacterStatement
          i ν hStandard hG hi hν (associatedSubset cs I))
        (hU (associatedSubset cs I)) σ //
      C.second = associatedLeviCentralCharacter i ν hG hi hν hConj
        hN hZ cs hLength hSimple hMin hAssoc I n hn C.first } := by
  have hJac := smooth_isIrreducible_of_iso_pullback
    (associatedLeviConjugationEquiv i ν hG hi hν hConj
      hN hZ cs hLength hSimple hMin hAssoc I n hn).symm σ _ E hσ
  have haJac := pointAssociatedJacquet_isAdmissible_of_iso
    i ν hG hi hν hStandard hU hConj hN hZ cs hLength hSimple hMin hAssoc
    I n hn σ E haσ
  let C := inductionTwoJacquetScalarCharactersOfSchur
    (isSemidirectDecomposition_of_standardCocharacterStatement
      i ν hStandard hG hi hν I) (hU I)
    (isSemidirectDecomposition_of_standardCocharacterStatement
      i ν hStandard hG hi hν (associatedSubset cs I))
    (hU (associatedSubset cs I)) σ hσ haσ hJac haJac
  exact ⟨C, InductionTwoJacquetScalarCharacters.second_eq_associated_of_iso
    i ν hG hi hν hStandard hU hConj hN hZ cs hLength hSimple hMin hAssoc
    I n hn σ E hσ C⟩

end RationalPointFamily

end Langlands.Aubert.General
