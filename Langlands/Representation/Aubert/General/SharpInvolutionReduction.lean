import Langlands.Representation.Aubert.General.SharpConsequenceStatements
import Langlands.Representation.Aubert.General.RationalSharpConsequenceTargets
import Langlands.Representation.Aubert.General.RationalInvolutivityTarget
import Langlands.Representation.Aubert.General.RootAssociationLaws
import Langlands.Representation.Aubert.General.RationalWeylComparisonProof
import Langlands.Representation.Smooth.IrreducibleClassDetection
import Langlands.Representation.Smooth.IrreducibleRealization
import Langlands.Representation.Aubert.General.RationalStandardParabolicTransport

/-!
# Reduction of the double-sharp isomorphism to the class formula and involutivity
-/

noncomputable section

open CategoryTheory

namespace Langlands.Aubert.General

universe uI uG uV

variable {ι : Type uI} [LinearOrder ι] [Fintype ι]
variable {G : Type uG} [Group G] [TopologicalSpace G] [LocallyCompactSpace G]
  [NonarchimedeanGroup G]
variable (P M U : Finset ι → Subgroup G)
  (h : ∀ J, IsSemidirectDecomposition (P J) (M J) (U J))
  (hclosed : ∀ J, IsClosed (U J : Set G))
  (hδ : ∀ J, IsUnimodularModulus (U J) (hclosed J))
  (hP : Monotone P) (hU : Antitone U)
  (hM : ∀ I, IsClosed (M I : Set G))
  (hL : ∀ (I : Finset ι) (K : Finset I),
    IsSemidirectDecomposition ((P (leviIndex I K)).subgroupOf (M I))
      ((M (leviIndex I K)).subgroupOf (M I)) ((U (leviIndex I K)).subgroupOf (M I)))
  (IsAssociate : Finset ι → Finset ι → G → Prop)

/-- The double terminal cokernel `(E#)#`, both cokernels taken at the index `I`,
that is at the degree `|S| - |I|`. -/
def doubleSharpObject (E : SmoothRep.{0, uG, max uI uG uV} ℂ G) (I : Finset ι) :
    SmoothRep.{0, uG, max uI uG uV} ℂ G :=
  StandardComplex.sharpObject.{uI, uG, max uI uV} P M U h hclosed hδ hP hU
    (StandardComplex.sharpObject.{uI, uG, max uI uV} P M U h hclosed hδ hP hU E I) I

/-- The terminal cokernel depends on the index only through its cardinality. -/
theorem sharpObject_eq_of_card_eq (A : SmoothRep.{0, uG, max uI uG uV} ℂ G)
    {I J : Finset ι} (hIJ : I.card = J.card) :
    StandardComplex.sharpObject.{uI, uG, max uI uV} P M U h hclosed hδ hP hU A I =
      StandardComplex.sharpObject.{uI, uG, max uI uV} P M U h hclosed hδ hP hU A J := by
  simp only [StandardComplex.sharpObject, Complex.sharpObject, Complex.terminalDegree, hIJ]

/-- Corollaire 3.9 (c) from the class formula, cuspidal-series retention and
involutivity of `D_G` for one finite-length proof. Irreducibility of `E#` and of
`(E#)#` comes from cuspidal-series retention, applied to `E` and to `E#`. -/
theorem sharpInvolutionTarget_of_classFormula
    (hfl : ∀ J, ParabolicFiniteLength.{uG, max uG (max uI uV)} (h J) (hclosed J))
    (hinv : (alternatingOperator.{uI, uG, max uI uV} P M U h hclosed hfl).comp
        (alternatingOperator.{uI, uG, max uI uV} P M U h hclosed hfl) = LinearMap.id)
    (hrefl : ∀ I, IsAssociate I I 1)
    (hcard : ∀ I J n, IsAssociate I J n → I.card = J.card)
    (hCF : SharpClassFormulaTarget.{uI, uG, uV} P M U h hclosed hδ hP hU hM hL IsAssociate)
    (hCS : SharpCuspidalSeriesTarget.{uI, uG, uV} P M U h hclosed hδ hP hU hM hL IsAssociate) :
    SharpInvolutionTarget.{uI, uG, uV} P M U h hclosed hδ hP hU hM hL := by
  intro I E hE
  obtain ⟨I', n, hassoc, -, hE'⟩ := hCS I E hE
  have hcardI : I.card = I'.card := hcard I I' n hassoc
  have hEq := sharpObject_eq_of_card_eq P M U h hclosed hδ hP hU
    (StandardComplex.sharpObject.{uI, uG, max uI uV} P M U h hclosed hδ hP hU E I) hcardI
  obtain ⟨_, _, -, -, hE''⟩ := hCS I' _ hE'
  have hE1irr := hE'.1
  have hE2irr := hE''.1
  have hEfl := SmoothRep.hasFiniteLength_of_isIrreducible hE.1
  have hE1fl := SmoothRep.hasFiniteLength_of_isIrreducible hE1irr
  have hE2fl := SmoothRep.hasFiniteLength_of_isIrreducible hE2irr
  have h1 := hCF hfl I E
    (IsInCuspidalSeries.isInSupportCategory (IsAssociate := IsAssociate) (hrefl I) hE)
    hEfl hE1fl
  have h2 := hCF hfl I' _
    (IsInCuspidalSeries.isInSupportCategory (IsAssociate := IsAssociate) (hrefl I') hE')
    hE1fl hE2fl
  have h3 := LinearMap.congr_fun hinv
    (SmoothRep.FiniteLengthGrothendieckGroup.ofRepresentation E hEfl)
  rw [LinearMap.comp_apply, h1, map_zsmul, h2, smul_smul, ← hcardI, ← pow_add,
    ← two_mul, pow_mul, neg_one_sq, one_pow, one_smul, LinearMap.id_apply] at h3
  obtain ⟨e⟩ := (SmoothRep.ofRepresentation_eq_irreducible_iff _ E hE2fl hE.1 hEfl).mp h3
  exact ⟨eqToIso hEq ≪≫ SmoothRep.mkIso e⟩

namespace RationalPointFamily

universe u v

open _root_.AlgebraicGeometry GroupScheme SmoothRep
open scoped CategoryTheory.MonObj
open Langlands.AlgebraicGeometry.PointTopology

/-- Corollaire 3.9 (c) on the actual families from the two dynamic finite-length
statements (Renard VI.6.2, VI.6.4), involutivity of `D_G` (Theorem 1.7 (3)), the
class formula (Corollaire 3.9 (a)) and cuspidal-series retention. The association
hypotheses `hN`, `hZ` are supplied by `rationalWeylComparison`; closedness and
finite-length preservation for the standard family come from
`RationalStandardParabolicTransport`, and continuity of the standard projections
from `continuous_standard_projection`. -/
theorem rationalSharpInvolutionStatement_of_inputs
    (hiDyn : DynamicInductionFiniteLengthStatement.{u, max (u + 1) v})
    (hrDyn : DynamicJacquetFiniteLengthStatement.{u, max (u + 1) v})
    (hInv : RationalInvolutivityStatement.{u, v})
    (hCF : RationalSharpClassFormulaStatement.{u, v})
    (hCS : RationalSharpCuspidalSeriesStatement.{u, v}) :
    RationalSharpInvolutionStatement.{u, v} := by
  intro k _ _ _ _ G hG T i hi
  have := hG.isAffineHom
  have := hi.isSplitSubtorus.mono
  let _ : TopologicalSpace (RationalPoint k G.X) := pointTopology
  intro _ _ _ ν hν hStandard hOrder hInter hRoots hU hM hUc
  let _ := simpleRelativeRootFintype i hRoots hi.isSplitSubtorus.1 ν
  intro _
  obtain ⟨hN, hZ⟩ := rationalWeylComparison k G hG T i hi
  have hP := isClosed_standard_parabolic i ν hStandard hG hi hν
  have hproj := continuous_standard_projection i ν hStandard hG hi hν
  have hiFl := fun I =>
    standard_induction_preservesFiniteLength i ν hStandard hG hi hν hiDyn I (hU I)
  have hrFl := fun I =>
    standard_jacquet_preservesFiniteLength i ν hStandard hG hi hν hrDyn I (hU I)
  exact sharpInvolutionTarget_of_classFormula _ _ _ _ _ _ _ _ _ _ (rootAssociation i ν hN hZ)
    (standardParabolicFiniteLength i ν hStandard hG hi hν hU hP hproj hUc hiFl hrFl)
    (hInv k G hG T i hi ν hν hStandard hRoots hU hP hproj hUc hiFl hrFl)
    (rootAssociation_one i ν hN hZ)
    (fun _ _ _ hIJ => rootAssociation_card_eq i ν hN hZ hIJ)
    (hCF k G hG T i hi ν hν hStandard hOrder hInter hRoots hN hZ hU hM hUc)
    (hCS k G hG T i hi ν hν hStandard hOrder hInter hRoots hN hZ hU hM hUc)

end RationalPointFamily

end Langlands.Aubert.General
