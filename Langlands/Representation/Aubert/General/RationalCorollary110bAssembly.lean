import Langlands.Representation.Aubert.General.RationalCorollaryTargets
import Langlands.Representation.Aubert.General.CorollaryExchangeAssembly
import Langlands.Representation.Aubert.General.RationalEndpoint
import Langlands.Representation.Aubert.General.RationalRootSpanCoxeterComparisons
import Langlands.Representation.Aubert.General.RationalSuppliedCoxeterComparisons
import Langlands.Representation.Aubert.General.RationalWeylComparisonProof
import Langlands.Representation.Aubert.General.InducedWeylClassComparison
import Langlands.Group.RelativeWeylMinimalityProof
import Langlands.Group.RelativeWeylAssociatedSubsetProof

/-! # Rational Corollary 1.10(b) from the rank-one and induced-Weyl targets -/

noncomputable section

universe u v

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Aubert.General.RationalPointFamily

open GroupScheme SmoothRep Group.RelativeWeylIndexing
open Langlands.AlgebraicGeometry.PointTopology

/-- The three separately published representation-theoretic targets
(self-association, the Jacquet pattern and induced K0 Weyl conjugacy) together
imply the exact Corollary 1.10(b) target. None of the three is proved here. -/
def RationalCorollary110bFromRankOneInputsStatement : Prop :=
  RationalRankOneSelfAssociationStatement.{u, v} →
    RationalRankOneJacquetModulesStatement.{u, v} →
    RationalInducedK0WeylConjugacyStatement.{u, v} →
    RationalCorollary110bStatement.{u, v}

/-- The implication holds. The Coxeter, root and quotient comparisons required
by the two rank-one targets are derived from the corollary's own premises. -/
theorem rationalCorollary110bFromRankOneInputs :
    RationalCorollary110bFromRankOneInputsStatement.{u, v} := by
  intro hSelf hJacquet hWeylK0
  have hWeyl := rationalInducedClassWeylConjugacy_of_inducedK0WeylConjugacy hWeylK0
  intro k _ _ _ _ G hG T i hi
  let _ := hG.isAffineHom
  let _ := hi.isSplitSubtorus.mono
  let _ : TopologicalSpace (RationalPoint k G.X) := pointTopology
  intro _ _ _ ν hν hStandard hInter hRoots hU hM hP hproj hUc hiFl hrFl
  let _ := simpleRelativeRootFintype i hRoots hi.isSplitSubtorus.1 ν
  let _ : DecidableEq (SimpleRoot i ν) := Classical.decEq _
  obtain ⟨hN, hZ⟩ := rationalWeylComparison k G hG T i hi
  let c := rootSpanPointCoxeterData i ν hN hZ hG hi hRoots hν
  let _ : Finite (Weyl i) := c.finiteWeyl
  let _ : Fintype (Weyl i) := Fintype.ofFinite _
  have hPos := positiveSimpleReflectionComparison_of_rootLength
    i ν hN hZ c.system hi.isSplitSubtorus.1 hRoots hν c.rootLength
  have hMin := minimalityLengthCriterion_proof c.system
  have hAssoc := associatedSubsetLaws_proof c.system
  have hS := hSelf k G hG T i hi ν hν hStandard hInter hRoots hU hM hN hZ
    c.matrix c.system c.rootLength hPos c.leviWeyl hMin hAssoc
  have hJ := hJacquet k G hG T i hi ν hν hStandard hInter hRoots hU hM hN hZ
    c.matrix c.system c.rootLength hPos c.leviWeyl hMin hAssoc
  have hW := hWeyl k G hG T i hi ν hν hStandard hU hP hproj hUc hiFl hrFl
  have htop := alternatingTerm_univ_eq_id.{u, v}
    i ν hStandard hG hi hν hU hP hproj hUc hiFl hrFl
  intro J hJmax σ hσ hcusp hred
  obtain ⟨n, hn⟩ := QuotientGroup.mk_surjective (longestRep c.system J)
  have hself := (hS J hJmax σ hσ hcusp hred).2 n hn
  obtain ⟨ρplus, ρminus, hseq, hpattern⟩ :=
    hJ J hJmax σ hσ hcusp hred n hn hself
  refine ⟨ρplus, ρminus, hseq, ?_⟩
  exact constituentExchange_of_jacquet_pattern _ _ _ _ _ _ (torusPoints i)
    J hJmax σ ρplus ρminus n hself hseq hpattern hW
    (LinearMap.congr_fun htop _) (LinearMap.congr_fun htop _)

end Langlands.Aubert.General.RationalPointFamily
