import Langlands.Representation.CuspidalSupport.BernsteinSubrepresentationReduction
import Langlands.Representation.Category.SpanningDisjointCoproduct

/-! # Regrouping actual coproducts by Bernstein inertial classes -/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Langlands.AlgebraicGeometry.PointTopology
open Langlands.Aubert.General Langlands.Aubert.General.RationalPointFamily
open Langlands.GroupScheme
open scoped CategoryTheory.MonObj

namespace Langlands.CuspidalSupport

universe uF uV uI

variable {F : Type uF} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  [LocallyOfFiniteType G.X.hom]
  {T : CommGroupScheme (Spec (CommRingCat.of F))}
  (i : T.toGrp ⟶ G) (ν : cocharacterLattice T)

local instance bernsteinCoproductRegroupingTopology :
    TopologicalSpace (rationalPoints G) := pointTopology

variable [LocallyCompactSpace (rationalPoints G)] [NonarchimedeanGroup (rationalPoints G)]
  (family : BernsteinStandardFamily i ν)
  {I : Type uI}

/-- The component in an actual Bernstein class is the invariant sum of all
cofan-leg images carrying that class label. Its carrier stays in `uV`. -/
def bernsteinGroupedSubspace
    (A : I → SmoothRep.{0, uF, uV} ℂ (rationalPoints G)) (s : Cofan A)
    (label : I → BernsteinInertialClass.{uF, max uF uV} i ν family)
    (c : BernsteinInertialClass.{uF, max uF uV} i ν family) :
    Subrepresentation s.pt.representation :=
  ⨆ j : {j : I // label j = c}, (SmoothRep.hom (s.inj j.val)).range

/-- Grouping preserves membership in the original all-constituents block. -/
theorem bernsteinGroupedSubspace_mem_block
    (A : I → SmoothRep.{0, uF, uV} ℂ (rationalPoints G)) (s : Cofan A)
    (label : I → BernsteinInertialClass.{uF, max uF uV} i ν family)
    (hA : ∀ j, bernsteinBlockProperty i ν family (label j) (A j))
    (c : BernsteinInertialClass.{uF, max uF uV} i ν family) :
    bernsteinBlockProperty i ν family c
      (SmoothRep.subrepresentation s.pt (bernsteinGroupedSubspace i ν family A s label c)) := by
  intro D hD hDB
  obtain ⟨j, hj⟩ := SmoothRep.irreducibleSubquotient_iSup hD
    (fun j : {j : I // label j = c} => (SmoothRep.hom (s.inj j.val)).range) hDB
  have hDA := smoothSubquotientTransitivity ℂ _ _ _ _ hj
    (SmoothRep.image_isQuotient (s.inj j.val)).isSubquotient
  exact j.property ▸ hA j.val D hD hDA

/-- A colimiting cofan stays spanning after grouping by actual class labels. -/
theorem iSup_bernsteinGroupedSubspace_eq_top
    (A : I → SmoothRep.{0, uF, uV} ℂ (rationalPoints G)) (s : Cofan A)
    (hs : IsColimit s)
    (label : I → BernsteinInertialClass.{uF, max uF uV} i ν family) :
    (⨆ c, bernsteinGroupedSubspace i ν family A s label c) = ⊤ := by
  apply top_unique
  rw [← SmoothRep.iSup_range_cofan_eq_top A s hs]
  refine iSup_le fun j => ?_
  exact le_iSup_of_le (label j)
    (le_iSup_of_le (⟨j, rfl⟩ : {k : I // label k = label j}) le_rfl)

/-- Actual support uniqueness makes the grouped inclusion cofan colimiting.
Neither index type is required to fit in the carrier universe. -/
def bernsteinGroupedCofanIsColimit
    (hunique : BernsteinInertialSupportUniquenessStatement.{uF, uV} i ν family)
    (A : I → SmoothRep.{0, uF, uV} ℂ (rationalPoints G)) (s : Cofan A)
    (hs : IsColimit s)
    (label : I → BernsteinInertialClass.{uF, max uF uV} i ν family)
    (hA : ∀ j, bernsteinBlockProperty i ν family (label j) (A j)) :
    IsColimit (SmoothRep.invariantSubspaceCofan
      (bernsteinGroupedSubspace i ν family A s label)) := by
  apply SmoothRep.invariantSubspaceCofanIsColimit _
    (iSup_bernsteinGroupedSubspace_eq_top i ν family A s hs label)
  intro c d hcd D hD hDC hDD
  exact hcd (hunique _ c d
    (bernsteinGroupedSubspace_mem_block i ν family A s label hA c D hD hDC)
    (bernsteinGroupedSubspace_mem_block i ν family A s label hA d D hD hDD))

/-- Any actual coproduct with individually labelled Bernstein-block summands
can be collected into one component per original Bernstein inertial class. -/
theorem isBernsteinCoproductOfComponents_of_labelledCofan
    (hunique : BernsteinInertialSupportUniquenessStatement.{uF, uV} i ν family)
    (A : I → SmoothRep.{0, uF, uV} ℂ (rationalPoints G)) (s : Cofan A)
    (hs : IsColimit s)
    (label : I → BernsteinInertialClass.{uF, max uF uV} i ν family)
    (hA : ∀ j, bernsteinBlockProperty i ν family (label j) (A j)) :
    Renard.IsCoproductOfComponents
      (fun c : BernsteinInertialClass.{uF, max uF uV} i ν family =>
        bernsteinBlockProperty.{uF, uV} i ν family c) s.pt :=
  ⟨_, (SmoothRep.invariantSubspaceCofan
      (bernsteinGroupedSubspace i ν family A s label)).inj,
    bernsteinGroupedSubspace_mem_block i ν family A s label hA,
    ⟨bernsteinGroupedCofanIsColimit i ν family hunique A s hs label hA⟩⟩

end Langlands.CuspidalSupport
