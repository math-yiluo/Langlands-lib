import Langlands.Representation.Aubert.General.IrreducibleJacquetFactorDetectionReduction
import Langlands.Representation.Aubert.General.RationalCuspidalJacquetSubquotient
import Langlands.Representation.Aubert.General.RationalSupportAssociationInvariance

/-! # Rational irreducible Jacquet detection conditional on factor extraction -/

noncomputable section

set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency.types false

universe u v

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Aubert.General.RationalPointFamily

open GroupScheme
open Langlands.AlgebraicGeometry.PointTopology

section Witness

variable {k : Type u} [Field k] [ValuativeRel k] [TopologicalSpace k]
  [IsNonarchimedeanLocalField k]
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
  {T : CommGroupScheme (Spec (CommRingCat.of k))}

local instance instRationalIrreducibleJacquetFactorDetection1 : TopologicalSpace (RationalPoint k G.X) := pointTopology

variable [LocallyCompactSpace (RationalPoint k G.X)]
  [NonarchimedeanGroup (RationalPoint k G.X)]
  (i : T.toGrp ⟶ G) [Mono i.hom.hom.left] (ν : cocharacterLattice T)
  (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
  (hν : IsGenericCocharacter i ν)
  (hStandard : StandardCocharacterStatement.{u})
  (hInter : StandardLeviIntersectionStatement.{u})
  (hRoots : HasRelativeRootSystem i)
  (hN : HasPointNormalizerComparison i) (hZ : HasPointCentralizerComparison i)
  (hU : ∀ I, IsClosed (unipotent i ν I : Set (RationalPoint k G.X)))
  (hM : ∀ I, IsClosed (levi i ν I : Set (RationalPoint k G.X)))

local notation "h" =>
  isSemidirectDecomposition_of_standardCocharacterStatement i ν hStandard hG hi hν
local notation "hL" => isSemidirectDecomposition_in_levi i ν hInter hG hi hν

/-- At the actual rational-point data, factor extraction is the only
additional input to the associated nonzero Jacquet witness construction. -/
def rationalAssociatedJacquetWitnessOfCuspidalFactors
    (hextract : CuspidalJacquetFactorExtractionTarget.{u, u, max (u + 1) v}
      (parabolic i ν) (levi i ν) (unipotent i ν) h hU hM hL
      (rootAssociation i ν hN hZ))
    (I : Finset (SimpleRoot i ν))
    (π : SmoothRep.{0, u, max (u + 1) v} ℂ (RationalPoint k G.X))
    (hπ : π.IsIrreducible)
    (hπI : IsInSupportCategory.{u, u, max (u + 1) v}
      (parabolic i ν) (levi i ν) (unipotent i ν)
      h hU (rootAssociation i ν hN hZ) I (hM I) (hL I) π) :
    {p : Finset (SimpleRoot i ν) × RationalPoint k G.X //
      rootAssociation i ν hN hZ I p.1 p.2 ∧
      (∀ x, x ∈ levi i ν p.1 ↔ p.2⁻¹ * x * p.2 ∈ levi i ν I) ∧
      Nontrivial ((jacquetFunctor.{u, max (u + 1) v} (h p.1) (hU p.1)).obj π)} := by
  apply associatedJacquetWitnessOfCuspidalFactors.{u, u, max (u + 1) v}
    (P := parabolic i ν) (M := levi i ν) (U := unipotent i ν)
    (hU := hU) (hM := hM)
    (IsAssociate := rootAssociation i ν hN hZ)
    (hfactor := ?_) (hextract := hextract) (hconjCusp := ?_) (hcomp := ?_) I π hπ hπI
  · intro A hA
    let : A.representation.IsIrreducible := hA
    let : Nontrivial A :=
      IsSimpleModule.nontrivial (MonoidAlgebra ℂ (RationalPoint k G.X))
        A.representation.asModule
    exact exists_irreducible_cuspidal_jacquet_subquotient
      i ν hStandard hInter hRoots hG hi hν hU hM A
  · intro K J n hn hKJ σ hc
    exact isLeviCuspidal_conjugation
      i ν hG hi hν hStandard hInter hRoots hN hZ hU hM hn hKJ σ hc
  · intro K L J n m hKL hLJ
    exact rootAssociation_mul i ν hN hZ hKL hLJ

end Witness

/-- The full rational detection target follows from the full rational
factor-extraction proposition. This theorem does not prove that premise. -/
theorem rationalSupportCategoryIrreducibleJacquetDetection_of_cuspidalFactors
    (hextract : RationalCuspidalJacquetFactorExtractionStatement.{u, v}) :
    RationalSupportCategoryIrreducibleJacquetDetectionStatement.{u, v} := by
  intro k _ _ _ _ G hG T i hi
  let := hG.isAffineHom
  let := hi.isSplitSubtorus.mono
  let : TopologicalSpace (RationalPoint k G.X) := pointTopology
  intro _ _ _ ν hν hStandard hInter hRoots hN hZ hU hM
  let := simpleRelativeRootFintype i hRoots hi.isSplitSubtorus.1 ν
  intro I π hπ hπI
  obtain ⟨⟨J, n⟩, hw⟩ := rationalAssociatedJacquetWitnessOfCuspidalFactors
    i ν hG hi hν hStandard hInter hRoots hN hZ hU hM
    (hextract k G hG T i hi ν hν hStandard hInter hRoots hN hZ hU hM) I π hπ hπI
  exact ⟨J, n, hw⟩

end Langlands.Aubert.General.RationalPointFamily
