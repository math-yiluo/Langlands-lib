import Langlands.GroupScheme.Rational.RelativeRankStatement
import Langlands.GroupScheme.Rational.PositiveRootInduction
import Langlands.GroupScheme.Rational.RelativeRootStandardCocharacter

/-! # Actual simple relative roots as a rational basis -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry TensorProduct
open Langlands.LinearAlgebra.RationalSpan

namespace Langlands.GroupScheme

variable {k : Type u} [Field k]
  {T : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))}
  [IsAffineHom G.X.hom] (i : T.toGrp ⟶ G) (ν : cocharacterLattice T)

/-- Genericity and negation stability make the actual simple roots span the
actual rational relative-root span. -/
theorem ratSpan_simpleRelativeRoots_eq_relativeRootSpan
    (hν : IsGenericCocharacter i ν)
    (hneg : ∀ α ∈ relativeRoots i, -α ∈ relativeRoots i) :
    ratSpan (simpleRelativeRoots i ν) = relativeRootSpan i := by
  apply le_antisymm
  · exact Submodule.span_mono (Set.image_mono fun _ hα => hα.1.1)
  · have hclosure : AddSubgroup.closure (simpleRelativeRoots i ν) ≤
        (ratSpan (simpleRelativeRoots i ν)).toAddSubgroup.comap toRat := by
      apply (AddSubgroup.closure_le _).mpr
      intro α hα
      exact toRat_mem_ratSpan hα
    apply Submodule.span_le.mpr
    rintro _ ⟨α, hα, rfl⟩
    exact hclosure (relativeRoots_subset_addSubgroupClosure_simpleRelativeRoots i ν hν hneg hα)

/-- The published actual simple-root vectors span their existing subtype. -/
theorem span_simpleRelativeRootVector_eq_top
    (hν : IsGenericCocharacter i ν)
    (hneg : ∀ α ∈ relativeRoots i, -α ∈ relativeRoots i) :
    Submodule.span ℚ (Set.range (simpleRelativeRootVector i ν)) = ⊤ := by
  apply (Submodule.span_range_subtype_eq_top_iff (relativeRootSpan i)
    (fun α : simpleRelativeRoots i ν => toRat_mem_ratSpan α.2.1.1)).mpr
  have hrange :
      Set.range (fun α : simpleRelativeRoots i ν => toRat (α : characterLattice T)) =
        toRat '' simpleRelativeRoots i ν := by
    ext x
    constructor
    · rintro ⟨α, rfl⟩
      exact ⟨α, α.2, rfl⟩
    · rintro ⟨α, hα, rfl⟩
      exact ⟨⟨α, hα⟩, rfl⟩
  rw [hrange]
  exact ratSpan_simpleRelativeRoots_eq_relativeRootSpan i ν hν hneg

/-- A basis consisting of the actual simple roots, from rational independence
and the explicit all-root sign hypotheses. -/
def simpleRelativeRootBasisOfLinearIndependent
    (hν : IsGenericCocharacter i ν)
    (hneg : ∀ α ∈ relativeRoots i, -α ∈ relativeRoots i)
    (hli : LinearIndependent ℚ
      (fun α : simpleRelativeRoots i ν => toRat (α : characterLattice T))) :
    Module.Basis (simpleRelativeRoots i ν) ℚ (relativeRootSpan i) :=
  Module.Basis.mk
    (LinearIndependent.of_comp (v := simpleRelativeRootVector i ν)
      (relativeRootSpan i).subtype hli)
    (le_of_eq (span_simpleRelativeRootVector_eq_top i ν hν hneg).symm)

@[simp] theorem simpleRelativeRootBasisOfLinearIndependent_apply
    (hν : IsGenericCocharacter i ν)
    (hneg : ∀ α ∈ relativeRoots i, -α ∈ relativeRoots i)
    (hli : LinearIndependent ℚ
      (fun α : simpleRelativeRoots i ν => toRat (α : characterLattice T)))
    (α : simpleRelativeRoots i ν) :
    simpleRelativeRootBasisOfLinearIndependent i ν hν hneg hli α =
      simpleRelativeRootVector i ν α :=
  Module.Basis.mk_apply _ _ _

/-- Cardinality of the actual simple roots computes the rational root rank
once their rational independence is established. -/
theorem relativeRootRank_eq_natCard_simpleRelativeRoots_of_linearIndependent
    (hν : IsGenericCocharacter i ν)
    (hneg : ∀ α ∈ relativeRoots i, -α ∈ relativeRoots i)
    (hli : LinearIndependent ℚ
      (fun α : simpleRelativeRoots i ν => toRat (α : characterLattice T))) :
    relativeRootRank i = Nat.card (simpleRelativeRoots i ν) :=
  Module.finrank_eq_nat_card_basis
    (simpleRelativeRootBasisOfLinearIndependent i ν hν hneg hli)

variable [Mono i.hom.hom.left]

/-- The published relative-root-system realization supplies the actual
simple-root basis, including nonreduced and empty systems. -/
def HasRelativeRootSystem.simpleRelativeRootBasis
    (h : HasRelativeRootSystem i) (hT : IsSplitTorus T.toGrp)
    (hν : IsGenericCocharacter i ν) :
    Module.Basis (simpleRelativeRoots i ν) ℚ (relativeRootSpan i) :=
  simpleRelativeRootBasisOfLinearIndependent i ν hν
    (fun _ hα => h.neg_mem_relativeRoots i hT hα)
    (h.linearIndependent_simpleRelativeRoots i ν hT hν)

@[simp] theorem HasRelativeRootSystem.simpleRelativeRootBasis_apply
    (h : HasRelativeRootSystem i) (hT : IsSplitTorus T.toGrp)
    (hν : IsGenericCocharacter i ν) (α : simpleRelativeRoots i ν) :
    h.simpleRelativeRootBasis i ν hT hν α = simpleRelativeRootVector i ν α :=
  simpleRelativeRootBasisOfLinearIndependent_apply i ν hν
    (fun _ hα => h.neg_mem_relativeRoots i hT hα)
    (h.linearIndependent_simpleRelativeRoots i ν hT hν) α

/-- The existing intrinsic root-system target implies the entire existing
simple-root basis target at the same universe and hypothesis scope. -/
theorem relativeSimpleRootBasisStatement_of_relativeRootSystemStatement
    (hroot : RelativeRootSystemStatement.{u}) : RelativeSimpleRootBasisStatement.{u} := by
  intro k _ G hG T i hi
  have := hG.isAffineHom
  have := hi.isSplitSubtorus.mono
  intro ν hν
  have h := hroot k G hG T i hi
  have hT := hi.isSplitSubtorus.1
  refine ⟨(h.finite_simpleRelativeRoots i hT ν).to_subtype, ?_, ?_⟩
  · exact ⟨h.simpleRelativeRootBasis i ν hT hν,
      h.simpleRelativeRootBasis_apply i ν hT hν⟩
  · exact Module.finrank_eq_nat_card_basis (h.simpleRelativeRootBasis i ν hT hν)

end Langlands.GroupScheme
