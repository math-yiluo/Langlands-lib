import Langlands.Representation.Aubert.General.GeometricFullLeviTerm
import Langlands.Representation.Aubert.General.RationalSupportAssociation
import Langlands.Representation.Aubert.General.RationalCuspidalGeometricTerms
import Langlands.Representation.Aubert.General.MaximalRootAssociationClasses

/-! # Actual rational geometric survivors in the non-self-associated case -/

noncomputable section

universe uI uG uV u v

open Classical
open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Aubert.General

section Inverse

variable {H : Type uG} [Group H] [TopologicalSpace H] [LocallyCompactSpace H]
  [NonarchimedeanGroup H] {Index : Type uI}
  (P M U : Finset Index → Subgroup H)
  (hM : ∀ I, IsClosed (M I : Set H)) (hU : ∀ I, IsClosed (U I : Set H))

/-- Forward transport by an inverse representative is pullback along the
inverse of the original inverse-conjugation equivalence. -/
def geometricTermInverseConjugationIso (I J : Finset Index) (n : H)
    (hs : GeometricSourceDecomposition P M U I J n⁻¹)
    (ht : GeometricTargetDecomposition P M U I J n⁻¹)
    (hConj : ∀ x : H, x ∈ M J ↔ n⁻¹ * x * n ∈ M I)
    (A : SmoothRep.{0, uG, max uG uV} ℂ (M J)) :
    (geometricTermFunctor P M U hM hU I J n⁻¹ hs ht).obj A ≅
      (SmoothRep.pullbackFunctor (conjugationEquiv n hConj).symm).obj A := by
  have hInv : ∀ x : H, x ∈ M I ↔ n⁻¹⁻¹ * x * n⁻¹ ∈ M J := by
    intro x
    simpa [mul_assoc] using (hConj (n * x * n⁻¹)).symm
  refine geometricTermFullLeviIso P M U hM hU I J n⁻¹ hs ht hInv A ≪≫ ?_
  refine SmoothRep.mkIso (Representation.Equiv.mk (LinearEquiv.refl ℂ A) ?_)
  intro m
  ext v
  change A.representation _ v = A.representation _ v
  apply congrArg (fun x => A.representation x v)
  apply Subtype.ext
  change n⁻¹⁻¹ * (m : H) * n⁻¹ = n * (m : H) * n⁻¹
  rw [inv_inv]

end Inverse

namespace RationalPointFamily

open SmoothRep GroupScheme Group.RelativeWeylIndexing
open Langlands.AlgebraicGeometry.PointTopology

variable {k : Type u} [Field k] [TopologicalSpace k]
  {T : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
  (i : T.toGrp ⟶ G) [Mono i.hom.hom.left]
  (ν : cocharacterLattice T)
  (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
  (hν : IsGenericCocharacter i ν)
  (hStandard : StandardCocharacterStatement.{u})
  (hN : HasPointNormalizerComparison i) (hZ : HasPointCentralizerComparison i)

local instance rationalGeometricSurvivorPointTopology :
    TopologicalSpace (RationalPoint k G.X) := pointTopology

variable [LocallyCompactSpace (RationalPoint k G.X)]
  [NonarchimedeanGroup (RationalPoint k G.X)]
  (hM : ∀ A, IsClosed (levi i ν A : Set (RationalPoint k G.X)))
  (hU : ∀ A, IsClosed (unipotent i ν A : Set (RationalPoint k G.X)))

/-- Actual root association identifies a full geometric term with pullback
along the existing actual rational Levi conjugation equivalence. -/
def pointGeometricTermRootAssociationIso
    (I J : Finset (SimpleRoot i ν)) (n : RationalPoint k G.X)
    (hA : rootAssociation i ν hN hZ J I n)
    (hs : GeometricSourceDecomposition
      (parabolic i ν) (levi i ν) (unipotent i ν) I J n)
    (ht : GeometricTargetDecomposition
      (parabolic i ν) (levi i ν) (unipotent i ν) I J n)
    (σ : SmoothRep.{0, u, max (u + 1) v} ℂ (levi i ν J)) :
    (geometricTermFunctor.{u, u, max (u + 1) v}
      (parabolic i ν) (levi i ν) (unipotent i ν) hM hU I J n hs ht).obj σ ≅
      (SmoothRep.pullbackFunctor (rootAssociationLeviConjugationEquiv
        i ν hG hi hν hStandard hN hZ J I n hA)).obj σ :=
  geometricTermFullLeviIso.{u, u, max (u + 1) v}
    (parabolic i ν) (levi i ν) (unipotent i ν) hM hU I J n hs ht
    (conjugationMembership_of_rootAssociation i ν hG hi hν hStandard hN hZ J I n hA) σ

/-- The geometric term at the literal identity lift is the original object. -/
def pointGeometricTermOneIso (J : Finset (SimpleRoot i ν))
    (hs : GeometricSourceDecomposition
      (parabolic i ν) (levi i ν) (unipotent i ν) J J 1)
    (ht : GeometricTargetDecomposition
      (parabolic i ν) (levi i ν) (unipotent i ν) J J 1)
    (σ : SmoothRep.{0, u, max (u + 1) v} ℂ (levi i ν J)) :
    (geometricTermFunctor.{u, u, max (u + 1) v}
      (parabolic i ν) (levi i ν) (unipotent i ν) hM hU J J 1 hs ht).obj σ ≅ σ := by
  have hConj : ∀ x : RationalPoint k G.X,
      x ∈ levi i ν J ↔ (1 : RationalPoint k G.X)⁻¹ * x * 1 ∈ levi i ν J := by
    intro x
    simp only [inv_one, one_mul, mul_one]
  exact geometricTermFullLeviIso.{u, u, max (u + 1) v}
    (parabolic i ν) (levi i ν) (unipotent i ν) hM hU J J 1 hs ht hConj σ ≪≫
      conjugationFunctorOneIso hConj σ

variable [Fintype (SimpleRoot i ν)] [Fintype (Weyl i)]
  {C : CoxeterMatrix (SimpleRoot i ν)}
  (actual : ActualCoxeterSystem (torusPoints i) C)
  (hLength : RootLengthComparison i ν hN hZ actual)
  (hSimple : PositiveSimpleReflectionComparison i ν hN hZ actual)
  (hMin : minimalityLengthCriterion actual)

/-- The associated surviving term at the inverse of a longest lift is
pullback along the inverse of the original associated-Levi equivalence. -/
def pointGeometricTermInverseLongestIso
    (hAssoc : associatedSubsetLaws actual) (J : Finset (SimpleRoot i ν))
    (n : Group.RelativeWeyl.normalizer (torusPoints i))
    (hn : QuotientGroup.mk n = longestRep actual J)
    (hs : GeometricSourceDecomposition (parabolic i ν) (levi i ν) (unipotent i ν)
      (associatedSubset actual J) J (n : RationalPoint k G.X)⁻¹)
    (ht : GeometricTargetDecomposition (parabolic i ν) (levi i ν) (unipotent i ν)
      (associatedSubset actual J) J (n : RationalPoint k G.X)⁻¹)
    (σ : SmoothRep.{0, u, max (u + 1) v} ℂ (levi i ν J)) :
    (geometricTermFunctor.{u, u, max (u + 1) v}
      (parabolic i ν) (levi i ν) (unipotent i ν) hM hU
        (associatedSubset actual J) J (n : RationalPoint k G.X)⁻¹ hs ht).obj σ ≅
      (SmoothRep.pullbackFunctor (associatedLeviConjugationEquiv i ν hG hi hν
        (standardLeviConjugationStatement_of_standardCocharacterStatement hStandard)
        hN hZ actual hLength hSimple hMin hAssoc J n hn).symm).obj σ :=
  geometricTermInverseConjugationIso.{u, u, max (u + 1) v}
    (parabolic i ν) (levi i ν) (unipotent i ν) hM hU
    (associatedSubset actual J) J (n : RationalPoint k G.X) hs ht
    (conjugationMembership_of_map_eq (n : RationalPoint k G.X)
      (associatedLeviConjugation_of_standard i ν hG hi hν
        (standardLeviConjugationStatement_of_standardCocharacterStatement hStandard)
        hN hZ actual hLength hSimple hMin hAssoc J n hn)) σ

variable (hInter : StandardLeviIntersectionStatement.{u})

include hLength hSimple hMin hStandard in
/-- For a maximal subset different from its associate, every self term other
than the identity class vanishes on the original cuspidal object. -/
theorem pointGeometricSelfTerm_subsingleton_of_ne_one
    (J : Finset (SimpleRoot i ν)) (hJ : IsMaximalStandard J)
    (hne : J ≠ associatedSubset actual J) (w : Weyl i)
    (hw : IsMinimal actual J J w) (hwne : w ≠ 1)
    (n : Group.RelativeWeyl.normalizer (torusPoints i)) (hn : QuotientGroup.mk n = w)
    (hs : GeometricSourceDecomposition
      (parabolic i ν) (levi i ν) (unipotent i ν) J J n)
    (ht : GeometricTargetDecomposition
      (parabolic i ν) (levi i ν) (unipotent i ν) J J n)
    (σ : SmoothRep.{0, u, max (u + 1) v} ℂ (levi i ν J))
    (hc : IsCorollaryLeviCuspidal.{u, u, max (u + 1) v}
      (parabolic i ν) (levi i ν) (unipotent i ν) J (hM J)
      (isSemidirectDecomposition_in_levi i ν hInter hG hi hν J) hU σ) :
    Subsingleton ((geometricTermFunctor.{u, u, max (u + 1) v}
      (parabolic i ν) (levi i ν) (unipotent i ν) hM hU J J n hs ht).obj σ) := by
  apply pointCuspidalGeometricTermVanishing_of_rootComparisons
    i ν hN hZ actual hLength hSimple hStandard hInter hG hi hν hM hU
    J J w hw n hn hs ht σ hc
  intro hfull
  exact hwne ((full_self_intersection_iff_eq_one i ν hN hZ actual
    hLength hSimple hMin hJ hne hw).mp hfull)

include hLength hSimple hMin hStandard in
/-- Every term toward the associated Levi other than the inverse longest
class vanishes on a maximal non-self-associated cuspidal source. -/
theorem pointGeometricAssociatedTerm_subsingleton_of_ne_inv_longest
    (J : Finset (SimpleRoot i ν)) (hJ : IsMaximalStandard J)
    (hne : J ≠ associatedSubset actual J) (w : Weyl i)
    (hw : IsMinimal actual (associatedSubset actual J) J w)
    (hwne : w ≠ (longestRep actual J)⁻¹)
    (n : Group.RelativeWeyl.normalizer (torusPoints i)) (hn : QuotientGroup.mk n = w)
    (hs : GeometricSourceDecomposition (parabolic i ν) (levi i ν) (unipotent i ν)
      (associatedSubset actual J) J n)
    (ht : GeometricTargetDecomposition (parabolic i ν) (levi i ν) (unipotent i ν)
      (associatedSubset actual J) J n)
    (σ : SmoothRep.{0, u, max (u + 1) v} ℂ (levi i ν J))
    (hc : IsCorollaryLeviCuspidal.{u, u, max (u + 1) v}
      (parabolic i ν) (levi i ν) (unipotent i ν) J (hM J)
      (isSemidirectDecomposition_in_levi i ν hInter hG hi hν J) hU σ) :
    Subsingleton ((geometricTermFunctor.{u, u, max (u + 1) v}
      (parabolic i ν) (levi i ν) (unipotent i ν) hM hU
      (associatedSubset actual J) J n hs ht).obj σ) := by
  apply pointCuspidalGeometricTermVanishing_of_rootComparisons
    i ν hN hZ actual hLength hSimple hStandard hInter hG hi hν hM hU
    (associatedSubset actual J) J w hw n hn hs ht σ hc
  intro hfull
  exact hwne ((full_associated_intersection_iff_eq_inv_longest i ν hN hZ actual
    hLength hSimple hMin hJ hne hw).mp hfull)

end RationalPointFamily

end Langlands.Aubert.General
