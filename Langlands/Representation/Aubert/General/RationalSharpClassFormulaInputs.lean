import Langlands.Representation.Aubert.General.RationalSharpConsequenceTargets
import Langlands.Representation.Aubert.General.RationalSupportCategoryTargets
import Langlands.Representation.Aubert.General.RootAssociationLaws
import Langlands.Representation.Aubert.General.RationalCorrectedExactnessReduction
import Langlands.Representation.Aubert.General.SharpClassFormulaReduction
import Langlands.Representation.Aubert.General.RationalJacquetVanishingFromDynamicCompactness
import Langlands.GroupScheme.Rational.RationalBruhatProof
import Langlands.BruhatTits.Parabolic.QuotientCompactProof
import Langlands.Representation.Aubert.General.RationalCorrectedGradedTransitionProof
import Langlands.Representation.Aubert.General.RationalSharpReductionStatements

/-! # Inputs for the signed class formula on the actual rational points -/

noncomputable section

set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry

namespace Langlands.Aubert.General

universe uI uG uV

section Vanishing

variable {G : Type uG} [Group G] [TopologicalSpace G] [LocallyCompactSpace G]
  [NonarchimedeanGroup G]
variable {ι : Type uI}
variable {P M U : Finset ι → Subgroup G}
  {h : ∀ I, IsSemidirectDecomposition (P I) (M I) (U I)}
  {hU : ∀ I, IsClosed (U I : Set G)}
  {hM : ∀ I, IsClosed (M I : Set G)}
  {hL : ∀ (I : Finset ι) (K : Finset I),
    IsSemidirectDecomposition ((P (leviIndex I K)).subgroupOf (M I))
      ((M (leviIndex I K)).subgroupOf (M I)) ((U (leviIndex I K)).subgroupOf (M I))}
  {IsAssociate : Finset ι → Finset ι → G → Prop}

/-- If association preserves the number of labels, the support Jacquet vanishing
target kills the Jacquet module along every `L_K` with fewer labels than `I`. -/
theorem jacquet_subsingleton_of_card_lt
    (hcard : ∀ (I J : Finset ι) (n : G), IsAssociate I J n → I.card = J.card)
    (hvan : SupportCategoryJacquetVanishingTarget.{uI, uG, uV}
      P M U h hU hM hL IsAssociate)
    {I K : Finset ι} (hK : K.card < I.card)
    (E : SmoothRep.{0, uG, max uG uV} ℂ G)
    (hE : IsInSupportCategory P M U h hU IsAssociate I (hM I) (hL I) E) :
    Subsingleton ((jacquetFunctor.{uG, max uG uV} (h K) (hU K)).obj E) := by
  refine hvan I K (fun J n hJK hIJ _ => ?_) E hE
  have h₁ := hcard I J n hIJ
  have h₂ := Finset.card_le_card hJK
  omega

end Vanishing

namespace RationalPointFamily

universe u v

open scoped CategoryTheory.MonObj
open GroupScheme
open Langlands.AlgebraicGeometry.PointTopology

/-- Conditional assembly: the signed class formula on the actual families from
the five published corrected-exactness inputs and support Jacquet vanishing. -/
theorem rationalSharpClassFormula_of_inputs
    (H : RationalCorrectedExactnessInputs.{u, v})
    (hvan : RationalSupportCategoryJacquetVanishingStatement.{u, v}) :
    RationalSharpClassFormulaStatement.{u, v} := by
  intro k _ _ _ _ G hG T i hi _ _ _ ν hν hStandard hOrder hInter hRoots hN hZ hU hM hUc
    _ hfl I E hEI hE hE'
  have := hG.isAffineHom
  have := hi.isSplitSubtorus.mono
  let _ : TopologicalSpace (RationalPoint k G.X) := pointTopology
  let _ := simpleRelativeRootFintype i hRoots hi.isSplitSubtorus.1 ν
  have hexact := rationalIsExactBeforeTerminal_of_inputs H k G hG T i hi ν hν hStandard
    hOrder hInter hRoots hN hZ hU hM hUc I E hEI
  have hvan' := fun (K : Finset (SimpleRoot i ν)) (hK : K.card < I.card) =>
    jacquet_subsingleton_of_card_lt
      (fun _ _ _ hIJ => rootAssociation_card_eq i ν hN hZ hIJ)
      (hvan k G hG T i hi ν hν hStandard hInter hRoots hN hZ hU hM) hK E hEI
  exact SharpClassFormula.class_formula_of_exact.{u, u, max (u + 1) v}
    _ _ _ _ _ _ _ _ hfl I E hE hE' hexact hvan'

/-- Conditional assembly with the published rational Bruhat decomposition
discharged: four corrected-exactness inputs and support Jacquet vanishing. -/
theorem rationalSharpClassFormula_of_remaining
    (hgv : RationalCorrectedGradedVanishingStatement.{u, v})
    (hgt : RationalCorrectedGradedTransitionStatement.{u, v})
    (hind : RationalSupportCategoryInductionJacquetStatement.{u, v})
    (hdet : RationalSupportCategoryExactnessDetectionStatement.{u, v})
    (hvan : RationalSupportCategoryJacquetVanishingStatement.{u, v}) :
    RationalSharpClassFormulaStatement.{u, v} :=
  rationalSharpClassFormula_of_inputs
    ⟨Langlands.GroupScheme.rationalBruhat.{u}, hgv, hgt, hind, hdet⟩ hvan

/-- Conditional assembly with the published rational Bruhat decomposition and
the published surviving graded transitions discharged: three corrected-exactness
inputs and support Jacquet vanishing. -/
theorem rationalSharpClassFormula_of_open
    (hgv : RationalCorrectedGradedVanishingStatement.{u, v})
    (hind : RationalSupportCategoryInductionJacquetStatement.{u, v})
    (hdet : RationalSupportCategoryExactnessDetectionStatement.{u, v})
    (hvan : RationalSupportCategoryJacquetVanishingStatement.{u, v}) :
    RationalSharpClassFormulaStatement.{u, v} :=
  rationalSharpClassFormula_of_remaining hgv rationalCorrectedGradedTransitionStatement.{u, v}
    hind hdet hvan

/-- Conditional assembly with support Jacquet vanishing replaced by actual
cuspidal-support association, using the published compactness of the actual
dynamic-parabolic quotients. -/
theorem rationalSharpClassFormula_of_association
    (hgv : RationalCorrectedGradedVanishingStatement.{u, v})
    (hind : RationalSupportCategoryInductionJacquetStatement.{u, v})
    (hdet : RationalSupportCategoryExactnessDetectionStatement.{u, v})
    (hAssoc : RationalCuspidalSupportAssociationStatement.{u, v}) :
    RationalSharpClassFormulaStatement.{u, v} :=
  rationalSharpClassFormula_of_open hgv hind hdet
    (rationalSupportCategoryJacquetVanishing_of_dynamicCompact_and_association
      Langlands.BruhatTits.dynamicParabolicQuotientCompact.{u} hAssoc)

/-- The published reduction statement holds, by
`rationalSharpClassFormula_of_open`. -/
theorem rationalSharpClassFormulaReduction :
    RationalSharpClassFormulaReductionStatement.{u, v} :=
  fun hgv hind hdet hvan => rationalSharpClassFormula_of_open hgv hind hdet hvan

end RationalPointFamily

end Langlands.Aubert.General
