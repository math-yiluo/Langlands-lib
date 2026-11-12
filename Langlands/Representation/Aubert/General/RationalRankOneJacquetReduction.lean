import Langlands.Representation.Aubert.General.RationalRankOneJacquetAssembly
import Langlands.Representation.Aubert.General.RationalCorollaryTargets
import Langlands.Representation.Aubert.General.RationalIrreducibleJacquetFactorDetection

/-! # Reduction of the rational rank-one Jacquet pattern to named statements -/

noncomputable section

universe u v

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Aubert.General

/-- A maximal standard subset is proper. -/
theorem IsMaximalStandard.ne_univ {B : Type*} [Fintype B] [DecidableEq B]
    {J : Finset B} (hJ : IsMaximalStandard J) : J ≠ Finset.univ := by
  obtain ⟨α, rfl⟩ := hJ
  intro h
  have hα : α ∈ Finset.univ.erase α := by
    rw [h]
    exact Finset.mem_univ α
  simp at hα

namespace RationalPointFamily

open GroupScheme SmoothRep Group.RelativeWeylIndexing
open Langlands.AlgebraicGeometry.PointTopology

/-- The geometric input of the rank-one Jacquet pattern on the actual
rational-point families. For a maximal standard subset `J`, an actual
inside-Levi cuspidal `σ` and every lift `n` of the specified longest
representative that normalizes `L_J`, the actual normalized Jacquet module
`r_J(i_J σ)` is an extension of `σ` by `Ad(n⁻¹) σ`, and `r_K(i_J σ)` is zero
for every other proper standard subset `K`. No proof is supplied. -/
def RationalRankOneGeometricJacquetStatement : Prop :=
  ∀ (k : Type u) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k]
    (G : GroupScheme (Spec (CommRingCat.of k))) (hG : IsConnectedReductive G)
    (T : CommGroupScheme (Spec (CommRingCat.of k))) (i : T.toGrp ⟶ G)
    (hi : IsMaximalSplitTorus i),
    haveI := hG.isAffineHom
    haveI := hi.isSplitSubtorus.mono
    letI : TopologicalSpace (RationalPoint k G.X) := pointTopology
    ∀ [LocallyCompactSpace (RationalPoint k G.X)]
      [NonarchimedeanGroup (RationalPoint k G.X)] [T2Space (RationalPoint k G.X)]
      (ν : cocharacterLattice T) (hν : IsGenericCocharacter i ν)
      (hStandard : StandardCocharacterStatement.{u})
      (hInter : StandardLeviIntersectionStatement.{u}) (hRoots : HasRelativeRootSystem i)
      (hU : ∀ I, IsClosed (unipotent i ν I : Set (RationalPoint k G.X)))
      (hM : ∀ J, IsClosed (levi i ν J : Set (RationalPoint k G.X))),
      letI := simpleRelativeRootFintype i hRoots hi.isSplitSubtorus.1 ν
      letI : DecidableEq (SimpleRoot i ν) := Classical.decEq _
      ∀ [Fintype (Weyl i)]
        (hN : HasPointNormalizerComparison i) (hZ : HasPointCentralizerComparison i)
        (C : CoxeterMatrix (SimpleRoot i ν))
        (actual : ActualCoxeterSystem (torusPoints i) C),
        RootLengthComparison i ν hN hZ actual →
        PositiveSimpleReflectionComparison i ν hN hZ actual →
        actualLeviWeylIdentification (torusPoints i) (levi i ν) actual →
        minimalityLengthCriterion actual → associatedSubsetLaws actual →
        ∀ (J : Finset (SimpleRoot i ν)), IsMaximalStandard J →
          ∀ (σ : SmoothRep.{0, u, max (u + 1) v} ℂ (levi i ν J)),
            IsCorollaryLeviCuspidal.{u, u, max (u + 1) v}
              (parabolic i ν) (levi i ν) (unipotent i ν) J (hM J)
              (isSemidirectDecomposition_in_levi i ν hInter hG hi hν J) hU σ →
            ∀ (n : Langlands.Group.RelativeWeyl.normalizer (torusPoints i)),
              QuotientGroup.mk n = longestRep actual J →
              ∀ hself : (∀ x : RationalPoint k G.X,
                x ∈ levi i ν J ↔
                  (n : RationalPoint k G.X) * x * (n : RationalPoint k G.X)⁻¹ ∈ levi i ν J),
                HasRankOneJacquetMiddleSequence.{u, u, max (u + 1) v}
                    (h := isSemidirectDecomposition_of_standardCocharacterStatement
                      i ν hStandard hG hi hν)
                    (hU := hU) J σ n hself ∧
                  ∀ K : Finset (SimpleRoot i ν), K ≠ Finset.univ → K ≠ J →
                    IsZero ((jacquetFunctor
                      (isSemidirectDecomposition_of_standardCocharacterStatement
                        i ν hStandard hG hi hν K) (hU K)).obj
                      ((normalizedInductionFunctor
                        (isSemidirectDecomposition_of_standardCocharacterStatement
                          i ν hStandard hG hi hν J) (hU J)).obj σ))

/-- Length two, irreducible support-category Jacquet detection and the
geometric input together imply the exact rational rank-one Jacquet target. -/
def RationalRankOneJacquetModulesAssemblyStatement : Prop :=
  RationalRankOneLengthTwoStatement.{u, v} →
    RationalSupportCategoryIrreducibleJacquetDetectionStatement.{u, v} →
      RationalRankOneGeometricJacquetStatement.{u, v} →
        RationalRankOneJacquetModulesStatement.{u, v}

/-- Length two, irreducible Jacquet detection and the geometric input together
prove the exact rational rank-one Jacquet target. -/
theorem rationalRankOneJacquetModules_of_lengthTwo_detection_geometry
    (hLen : RationalRankOneLengthTwoStatement.{u, v})
    (hdet : RationalSupportCategoryIrreducibleJacquetDetectionStatement.{u, v})
    (hGeom : RationalRankOneGeometricJacquetStatement.{u, v}) :
    RationalRankOneJacquetModulesStatement.{u, v} := by
  intro k _ _ _ _ G hG T i hi
  have := hG.isAffineHom
  have := hi.isSplitSubtorus.mono
  let : TopologicalSpace (RationalPoint k G.X) := pointTopology
  intro _ _ _ ν hν hStandard hInter hRoots hU hM
  let := simpleRelativeRootFintype i hRoots hi.isSplitSubtorus.1 ν
  let : DecidableEq (SimpleRoot i ν) := Classical.decEq _
  intro _ hN hZ C actual hLength hSimple hIdent hMin hAssoc J hJ σ hσ hcusp hred n hn hself
  obtain ⟨A, B, hseries⟩ :=
    hLen k G hG T i hi ν hν hStandard hInter hRoots hU hM J hJ σ hσ hcusp hred
  obtain ⟨hgeometry, hvanish⟩ :=
    hGeom k G hG T i hi ν hν hStandard hInter hRoots hU hM
      hN hZ C actual hLength hSimple hIdent hMin hAssoc J hJ σ.val hcusp n hn hself
  obtain ⟨ρ, hρ⟩ :=
    rankOneJacquetConstituentsOfRationalSupportDetection.{u, v} hdet
      k G hG T i hi ν hν hStandard hInter hRoots hN hZ hU hM J (IsMaximalStandard.ne_univ hJ)
      σ.val hσ hcusp n hself A B hseries hgeometry hvanish
  exact ⟨ρ.1, ρ.2, hρ⟩

/-- The named assembly implication holds. -/
theorem rationalRankOneJacquetModulesAssembly :
    RationalRankOneJacquetModulesAssemblyStatement.{u, v} :=
  rationalRankOneJacquetModules_of_lengthTwo_detection_geometry

/-- The same assembly with the support detector replaced by the published
rational cuspidal Jacquet-factor extraction proposition. -/
theorem rationalRankOneJacquetModules_of_lengthTwo_extraction_geometry
    (hLen : RationalRankOneLengthTwoStatement.{u, v})
    (hextract : RationalCuspidalJacquetFactorExtractionStatement.{u, v})
    (hGeom : RationalRankOneGeometricJacquetStatement.{u, v}) :
    RationalRankOneJacquetModulesStatement.{u, v} :=
  rationalRankOneJacquetModules_of_lengthTwo_detection_geometry hLen
    (rationalSupportCategoryIrreducibleJacquetDetection_of_cuspidalFactors hextract) hGeom

end RationalPointFamily

end Langlands.Aubert.General
