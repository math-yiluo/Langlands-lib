import Langlands.Representation.Aubert.General.RationalJacquetGeometricCommon
import Langlands.Representation.Aubert.General.InducedIntersectionTerm
import Langlands.Representation.Aubert.General.RationalInductionStages
import Langlands.Representation.Aubert.General.RationalInductionTarget
import Langlands.Representation.Aubert.General.RationalSourceJacquet

/-! # Induced geometric terms from point-source intersection identities -/

noncomputable section

open Classical

universe u v

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Aubert.General.RationalPointFamily

open GroupScheme SmoothRep Group.RelativeWeylIndexing
open Langlands.AlgebraicGeometry.PointTopology

variable {k : Type u} [Field k]
  {T : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
  (i : T.toGrp ⟶ G) (ν : cocharacterLattice T) [Fintype (SimpleRoot i ν)]
  {CM : CoxeterMatrix (SimpleRoot i ν)}
  (cs : ActualCoxeterSystem (torusPoints i) CM)
  (hSource : PointSourceIntersectionIdentities i ν cs)

/-- The canonical fine index is the literal simple-image intersection. -/
theorem pointSourceIntersectionIndex
    (I J : Finset (SimpleRoot i ν)) (w : Weyl i) (hw : IsMinimal cs I J w) :
    leviIndex J (intersectionLeviIndex cs I J w) = simpleImage cs w⁻¹ I ∩ J := by
  rw [leviIndex_intersectionLeviIndex, intersectionSubset_eq_simpleImage_inter cs hw]
  ext a
  simp only [Finset.mem_inter]

include hSource in
/-- The structural source and target Levi identities already identify the fine
Levis under inverse conjugation; no separate Levi-conjugation law is needed. -/
theorem pointSourceIntersectionConjugationMembership
    (I J : Finset (SimpleRoot i ν)) (w : Weyl i) (hw : IsMinimal cs I J w)
    (n : Group.RelativeWeyl.normalizer (torusPoints i)) (hn : QuotientGroup.mk n = w) :
    ∀ x : RationalPoint k G.X,
      x ∈ levi i ν (leviIndex I (intersectionLeviIndex cs J I w⁻¹)) ↔
        (n : RationalPoint k G.X)⁻¹ * x * (n : RationalPoint k G.X) ∈
          levi i ν (leviIndex J (intersectionLeviIndex cs I J w)) := by
  have hS := (hSource I J w hw n hn).1
  have hT := (pointTargetIntersectionIdentities i ν cs hSource I J w hw n hn).1
  rw [pointSourceIntersectionIndex i ν cs I J w hw,
    pointSourceIntersectionIndex i ν cs J I w⁻¹ (isMinimal_inv cs hw), inv_inv]
  rw [← hS, ← hT]
  exact geometricIntersectionMembership (levi i ν I) (levi i ν J) n

section Topology

variable [TopologicalSpace k]

local instance rationalPointInducedTermPointTopology :
    TopologicalSpace (RationalPoint k G.X) := pointTopology

variable [LocallyCompactSpace (RationalPoint k G.X)]
  [NonarchimedeanGroup (RationalPoint k G.X)]
  (hInter : StandardLeviIntersectionStatement.{u})
  (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
  (hν : IsGenericCocharacter i ν)
  (hU : ∀ A, IsClosed (unipotent i ν A : Set (RationalPoint k G.X)))
  (hM : ∀ A, IsClosed (levi i ν A : Set (RationalPoint k G.X)))
  (hLfl : ∀ J, letI := (hM J).locallyCompactSpace
    ∀ K : Finset J, ParabolicFiniteLength.{u, max (u + 1) v}
      (isSemidirectDecomposition_in_levi i ν hInter hG hi hν J K)
      ((hU (leviIndex J K)).preimage continuous_subtype_val))

include hSource in
/-- Each actual geometric term is its literal standard term, with conjugation
membership derived solely from the structural source identities. -/
theorem geometricTermK0_eq_standard_of_pointSource
    (I J : Finset (SimpleRoot i ν)) (w : Weyl i) (hw : IsMinimal cs I J w)
    (n : Group.RelativeWeyl.normalizer (torusPoints i)) (hn : QuotientGroup.mk n = w)
    (hs : GeometricSourceDecomposition (parabolic i ν) (levi i ν) (unipotent i ν) I J n)
    (ht : GeometricTargetDecomposition (parabolic i ν) (levi i ν) (unipotent i ν) I J n)
    (hfl : GeometricTermFiniteLength.{u, u, max (u + 1) v}
      (parabolic i ν) (levi i ν) (unipotent i ν) hM hU I J n hs ht) :
    geometricTermK0.{u, u, max (u + 1) v}
        (parabolic i ν) (levi i ν) (unipotent i ν) hM hU I J n hs ht hfl =
      standardIntersectionTermK0.{u, u, max (u + 1) v}
        (parabolic i ν) (levi i ν) (unipotent i ν) hM hU I J
        (leviIndex J (intersectionLeviIndex cs I J w))
        (leviIndex I (intersectionLeviIndex cs J I w⁻¹)) n
        (levi_le_of_subset i ν hInter hG hi hν _ J
          (leviIndex_subset J (intersectionLeviIndex cs I J w)))
        (levi_le_of_subset i ν hInter hG hi hν _ I
          (leviIndex_subset I (intersectionLeviIndex cs J I w⁻¹)))
        (isSemidirectDecomposition_in_levi i ν hInter hG hi hν J
          (intersectionLeviIndex cs I J w))
        (isSemidirectDecomposition_in_levi i ν hInter hG hi hν I
          (intersectionLeviIndex cs J I w⁻¹))
        (pointSourceIntersectionConjugationMembership i ν cs hSource I J w hw n hn)
        ⟨(hLfl J (intersectionLeviIndex cs I J w)).2.2.1,
          (hLfl J (intersectionLeviIndex cs I J w)).2.2.2⟩
        ⟨(hLfl I (intersectionLeviIndex cs J I w⁻¹)).1,
          (hLfl I (intersectionLeviIndex cs J I w⁻¹)).2.1⟩ := by
  obtain ⟨hSL, -, hSU⟩ := hSource I J w hw n hn
  obtain ⟨hTL, hTP, hTU⟩ :=
    pointTargetIntersectionIdentities i ν cs hSource I J w hw n hn
  have hS := pointSourceIntersectionIndex i ν cs I J w hw
  have hT := pointSourceIntersectionIndex i ν cs J I w⁻¹ (isMinimal_inv cs hw)
  simp only [inv_inv] at hT
  rw [← hS] at hSL hSU
  rw [← hT] at hTL hTP hTU
  exact geometricTermK0_eq_standardOfEq.{u, u, max (u + 1) v}
    (parabolic i ν) (levi i ν) (unipotent i ν) hM hU I J
    (leviIndex J (intersectionLeviIndex cs I J w))
    (leviIndex I (intersectionLeviIndex cs J I w⁻¹)) n
    (levi_le_of_subset i ν hInter hG hi hν _ J
      (leviIndex_subset J (intersectionLeviIndex cs I J w)))
    (levi_le_of_subset i ν hInter hG hi hν _ I
      (leviIndex_subset I (intersectionLeviIndex cs J I w⁻¹)))
    (isSemidirectDecomposition_in_levi i ν hInter hG hi hν J
      (intersectionLeviIndex cs I J w))
    (isSemidirectDecomposition_in_levi i ν hInter hG hi hν I
      (intersectionLeviIndex cs J I w⁻¹))
    (pointSourceIntersectionConjugationMembership i ν cs hSource I J w hw n hn)
    ⟨(hLfl J (intersectionLeviIndex cs I J w)).2.2.1,
      (hLfl J (intersectionLeviIndex cs I J w)).2.2.2⟩
    ⟨(hLfl I (intersectionLeviIndex cs J I w⁻¹)).1,
      (hLfl I (intersectionLeviIndex cs J I w⁻¹)).2.1⟩
    hs ht hSL hSU hTL hTP hTU hfl

section Induced

variable (hStandard : StandardCocharacterStatement.{u})
  (hfl : ∀ A, ParabolicFiniteLength.{u, max (u + 1) v}
    (isSemidirectDecomposition_of_standardCocharacterStatement
      i ν hStandard hG hi hν A) (hU A))
  (I J : Finset (SimpleRoot i ν)) (w : Weyl i) (hw : IsMinimal cs I J w)
  (n : Group.RelativeWeyl.normalizer (torusPoints i)) (hn : QuotientGroup.mk n = w)

local notation "dec" => isSemidirectDecomposition_of_standardCocharacterStatement
  i ν hStandard hG hi hν

/-- Ambient induction of the actual geometric term, with its finite-length
and short-exactness properties derived from the point-source identities. -/
def pointSourceInducedGeometricTermK0
    (hs : GeometricSourceDecomposition (parabolic i ν) (levi i ν) (unipotent i ν) I J n)
    (ht : GeometricTargetDecomposition (parabolic i ν) (levi i ν) (unipotent i ν) I J n) :
    FiniteLengthGrothendieckGroup.{0, u, max (u + 1) v} ℂ (levi i ν J) →ₗ[ℤ]
      FiniteLengthGrothendieckGroup.{0, u, max (u + 1) v} ℂ (RationalPoint k G.X) :=
  (inductionK0.{u, max (u + 1) v} (dec I) (hU I) (hfl I).1 (hfl I).2.1).comp
    (geometricTermK0.{u, u, max (u + 1) v}
      (parabolic i ν) (levi i ν) (unipotent i ν) hM hU I J n hs ht
      (geometricTermFiniteLength_of_pointSource.{u, v}
        i ν cs hSource hInter hG hi hν hU hM hLfl I J w hw n hn hs ht))

variable [ValuativeRel k] [IsNonarchimedeanLocalField k]
  (hproj : ∀ A : Finset (SimpleRoot i ν), Continuous
    (isSemidirectDecomposition_of_standardCocharacterStatement
      i ν hStandard hG hi hν A).projection)
  (hUc : ∀ A, Jacquet.Localization.IsLimitOfCompactSubgroups (unipotent i ν A))
  (hLUc : ∀ (A : Finset (SimpleRoot i ν)) (B : Finset A),
    Jacquet.Localization.IsLimitOfCompactSubgroups
      ((unipotent i ν (leviIndex A B)).subgroupOf (levi i ν A)))

include hproj hUc hLUc in
/-- Actual induction stages reduce every induced geometric term to its
literal source alternating term, assuming the fine-Levi induced Weyl equation.
The subgroup identities have no representation-theoretic premise. -/
theorem pointSourceInducedGeometricTermK0_eq
    (hWeyl :
      (inductionK0.{u, max (u + 1) v}
        (dec (leviIndex I (intersectionLeviIndex cs J I w⁻¹)))
        (hU (leviIndex I (intersectionLeviIndex cs J I w⁻¹)))
        (hfl (leviIndex I (intersectionLeviIndex cs J I w⁻¹))).1
        (hfl (leviIndex I (intersectionLeviIndex cs J I w⁻¹))).2.1).comp
          (conjugationK0.{u, max (u + 1) v} (n : RationalPoint k G.X)
            (pointSourceIntersectionConjugationMembership
              i ν cs hSource I J w hw n hn)) =
      inductionK0.{u, max (u + 1) v}
        (dec (leviIndex J (intersectionLeviIndex cs I J w)))
        (hU (leviIndex J (intersectionLeviIndex cs I J w)))
        (hfl (leviIndex J (intersectionLeviIndex cs I J w))).1
        (hfl (leviIndex J (intersectionLeviIndex cs I J w))).2.1)
    (hs : GeometricSourceDecomposition (parabolic i ν) (levi i ν) (unipotent i ν) I J n)
    (ht : GeometricTargetDecomposition (parabolic i ν) (levi i ν) (unipotent i ν) I J n) :
    pointSourceInducedGeometricTermK0.{u, v}
        i ν cs hSource hInter hG hi hν hU hM hLfl hStandard hfl
        I J w hw n hn hs ht =
      inducedLeviAlternatingTerm.{u, u, max (u + 1) v}
        (parabolic i ν) (levi i ν) (unipotent i ν) dec hU hfl hM J
        (isSemidirectDecomposition_in_levi i ν hInter hG hi hν J)
        (hLfl J) (intersectionLeviIndex cs I J w) := by
  let _ := (hM J).locallyCompactSpace
  let _ := (hM I).locallyCompactSpace
  have hS := standardInductionStagesIso.{u, v}
    i ν hInter hG hi hν hStandard hU hproj hUc
    J (intersectionLeviIndex cs I J w) (hM J)
    (hLUc J (intersectionLeviIndex cs I J w))
  have hT := standardInductionStagesIso.{u, v}
    i ν hInter hG hi hν hStandard hU hproj hUc
    I (intersectionLeviIndex cs J I w⁻¹) (hM I)
    (hLUc I (intersectionLeviIndex cs J I w⁻¹))
  have hterm := inducedStandardIntersectionTermK0_eq.{u, u, max (u + 1) v}
    (parabolic i ν) (levi i ν) (unipotent i ν) dec hU hfl hM
    I J (intersectionLeviIndex cs I J w) (intersectionLeviIndex cs J I w⁻¹)
    (n : RationalPoint k G.X)
    (levi_le_of_subset i ν hInter hG hi hν _ J
      (leviIndex_subset J (intersectionLeviIndex cs I J w)))
    (levi_le_of_subset i ν hInter hG hi hν _ I
      (leviIndex_subset I (intersectionLeviIndex cs J I w⁻¹)))
    (isSemidirectDecomposition_in_levi i ν hInter hG hi hν J)
    (isSemidirectDecomposition_in_levi i ν hInter hG hi hν I
      (intersectionLeviIndex cs J I w⁻¹))
    (pointSourceIntersectionConjugationMembership i ν cs hSource I J w hw n hn)
    (hLfl J)
    ⟨(hLfl I (intersectionLeviIndex cs J I w⁻¹)).1,
      (hLfl I (intersectionLeviIndex cs J I w⁻¹)).2.1⟩ hS hT hWeyl
  unfold pointSourceInducedGeometricTermK0
  rw [geometricTermK0_eq_standard_of_pointSource.{u, v}
    i ν cs hSource hInter hG hi hν hU hM hLfl I J w hw n hn hs ht
    (geometricTermFiniteLength_of_pointSource.{u, v}
      i ν cs hSource hInter hG hi hν hU hM hLfl I J w hw n hn hs ht)]
  exact hterm

end Induced

end Topology

end Langlands.Aubert.General.RationalPointFamily
