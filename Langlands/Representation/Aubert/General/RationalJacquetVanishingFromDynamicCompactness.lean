import Langlands.Representation.Aubert.General.RationalJacquetSupportVanishingReduction
import Langlands.Representation.Aubert.General.RationalLeviQuotientCompactness
import Langlands.Representation.Aubert.General.RationalSupportCategoryTargets

/-! # Rational Jacquet vanishing from two uniform prerequisites -/

noncomputable section

set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

universe u v

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Aubert.General.RationalPointFamily

open GroupScheme SmoothRep
open Langlands.AlgebraicGeometry.PointTopology

section Witness

variable
  (hcompact : BruhatTits.DynamicParabolicQuotientCompactStatement.{u})
  (hAssoc : RationalCuspidalSupportAssociationStatement.{u, v})
  {k : Type u} [Field k] [ValuativeRel k] [TopologicalSpace k]
  [IsNonarchimedeanLocalField k]
  {T : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
  (i : T.toGrp ⟶ G) (ν : cocharacterLattice T)
  (hStandard : StandardCocharacterStatement.{u})
  (hInter : StandardLeviIntersectionStatement.{u})
  (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
  (hν : IsGenericCocharacter i ν)

local instance dynamicSupportVanishingPointTopology :
    TopologicalSpace (RationalPoint k G.X) := pointTopology

variable [LocallyCompactSpace (RationalPoint k G.X)]
  [NonarchimedeanGroup (RationalPoint k G.X)]
  [T2Space (RationalPoint k G.X)] [Mono i.hom.hom.left]
  (hRoots : HasRelativeRootSystem i)
  (hN : HasPointNormalizerComparison i) (hZ : HasPointCentralizerComparison i)
  (hU : ∀ I, IsClosed (unipotent i ν I : Set (RationalPoint k G.X)))
  (hM : ∀ I, IsClosed (levi i ν I : Set (RationalPoint k G.X)))

local notation "dec" => isSemidirectDecomposition_of_standardCocharacterStatement
  i ν hStandard hG hi hν

/-- Two uniform prerequisites give an actual associated-subset certificate
for every nonzero Jacquet module of a rational support-category object. -/
def dynamicAssociatedSubsetOfNonzeroJacquet
    (I K : Finset (SimpleRoot i ν))
    (E : SmoothRep.{0, u, max (u + 1) v} ℂ (RationalPoint k G.X))
    (hE : IsInSupportCategory.{u, u, max (u + 1) v}
      (parabolic i ν) (levi i ν) (unipotent i ν)
      dec hU (rootAssociation i ν hN hZ) I (hM I)
      (isSemidirectDecomposition_in_levi i ν hInter hG hi hν I) E)
    (hnonzero : Nontrivial ((jacquetFunctor (dec K) (hU K)).obj E)) :
    {p : Finset (SimpleRoot i ν) × RationalPoint k G.X //
      p.1 ⊆ K ∧ rootAssociation i ν hN hZ I p.1 p.2 ∧
      ∀ x : RationalPoint k G.X,
        x ∈ levi i ν p.1 ↔ p.2⁻¹ * x * p.2 ∈ levi i ν I} :=
  rationalAssociatedSubsetOfNonzeroJacquet.{u, v}
    i ν hStandard hInter hG hi hν hU hM
    (fun K J => compactSpace_leftQuotient_in_levi_of_dynamic
      i ν hInter hG hi hν hStandard hcompact K J)
    hRoots hN hZ
    (fun K => compactSpace_leftQuotient_parabolic
      i ν hcompact hStandard hG hi hν K)
    (hAssoc k G hG T i hi ν hν hStandard hInter hRoots hN hZ hU hM)
    I K E hE hnonzero

end Witness

/-- Conditional assembly of the whole unapplied rational target. The two
uniform prerequisites are retained and are not proved by this theorem. -/
theorem rationalSupportCategoryJacquetVanishing_of_dynamicCompact_and_association
    (hcompact : BruhatTits.DynamicParabolicQuotientCompactStatement.{u})
    (hAssoc : RationalCuspidalSupportAssociationStatement.{u, v}) :
    RationalSupportCategoryJacquetVanishingStatement.{u, v} := by
  intro k _ _ _ _ G hG T i hi
  let := hG.isAffineHom
  let := hi.isSplitSubtorus.mono
  let : TopologicalSpace (RationalPoint k G.X) := pointTopology
  intro _ _ _ ν hν hStandard hInter hRoots hN hZ hU hM
  let := simpleRelativeRootFintype i hRoots hi.isSplitSubtorus.1 ν
  intro I K hno E hE
  by_contra hz
  have hnonzero : Nontrivial
      ((jacquetFunctor
        (isSemidirectDecomposition_of_standardCocharacterStatement
          i ν hStandard hG hi hν K) (hU K)).obj E) :=
    not_subsingleton_iff_nontrivial.mp hz
  obtain ⟨⟨J, n⟩, hJK, hIJ, hn⟩ :=
    dynamicAssociatedSubsetOfNonzeroJacquet.{u, v}
      hcompact hAssoc i ν hStandard hInter hG hi hν
      hRoots hN hZ hU hM I K E hE hnonzero
  exact hno J n hJK hIJ hn

end Langlands.Aubert.General.RationalPointFamily
