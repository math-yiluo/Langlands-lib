import Langlands.Representation.Aubert.General.FirstAdjointnessConsequences
import Langlands.Representation.Aubert.General.SupportCategoryReductions

/-! # Jacquet modules of proper subrepresentations of actual induction -/

noncomputable section

set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.Aubert.General

universe uG uV

open CategoryTheory SmoothRep

variable {G : Type uG} [Group G] [TopologicalSpace G]
  [LocallyCompactSpace G] [NonarchimedeanGroup G]
  {P M U : Subgroup G}
  (h : IsSemidirectDecomposition P M U) (hU : IsClosed (U : Set G))
  (hUc : Jacquet.Localization.IsLimitOfCompactSubgroups U)
  (σ : SmoothRep.{0, uG, uV} ℂ M)


/-- A nonzero invariant subspace maps isomorphically onto the actual Jacquet
module of induction when that module is irreducible. -/
def subrepresentationJacquetInclusionEquiv
    (hJac : ((jacquetFunctor.{uG, max uG uV} h hU).obj ((normalizedInductionFunctor h hU).obj σ)).IsIrreducible)
    (S : Subrepresentation ((normalizedInductionFunctor h hU).obj σ).representation) (hS : S ≠ ⊥) :
    ((jacquetFunctor.{uG, max uG uV} h hU).obj (subrepresentation ((normalizedInductionFunctor h hU).obj σ) S)).representation.Equiv
      ((jacquetFunctor.{uG, max uG uV} h hU).obj ((normalizedInductionFunctor h hU).obj σ)).representation := by
  haveI := hJac
  let f := hom ((jacquetFunctor.{uG, max uG uV} h hU).map (subtype ((normalizedInductionFunctor h hU).obj σ) S))
  have hex := jacquetFunctor_map_isShortExact h hU hUc
    (subtype ((normalizedInductionFunctor h hU).obj σ) S) (mkQ ((normalizedInductionFunctor h hU).obj σ) S) (subtype_mkQ_isShortExact ((normalizedInductionFunctor h hU).obj σ) S)
  have hi : hom (subtype ((normalizedInductionFunctor h hU).obj σ) S) ≠ 0 := by
    intro he
    apply hS
    apply le_antisymm _ bot_le
    intro v hv
    change v = 0
    exact congrArg (fun F : (subrepresentation ((normalizedInductionFunctor h hU).obj σ) S).representation.IntertwiningMap
      ((normalizedInductionFunctor h hU).obj σ).representation => F ⟨v, hv⟩) he
  have hnt := FirstAdjointness.nontrivial_jacquet_of_map_ne_zero h hU
    (isUnimodularModulus_of_isLimitOfCompactSubgroups U hU hUc)
    (subrepresentation ((normalizedInductionFunctor h hU).obj σ) S) σ (hom (subtype ((normalizedInductionFunctor h hU).obj σ) S)) hi
  have hf : f ≠ 0 := by
    intro hf
    have hz : Subsingleton ((jacquetFunctor.{uG, max uG uV} h hU).obj (subrepresentation ((normalizedInductionFunctor h hU).obj σ) S)) := ⟨fun a b =>
      hex.1 (by change f a = f b; rw [hf]; rfl)⟩
    exact not_subsingleton_iff_nontrivial.mpr hnt hz
  exact f.ofBijective ⟨hex.1,
    (Representation.IsIrreducible.surjective_or_eq_zero f).resolve_right hf⟩

@[simp]
theorem subrepresentationJacquetInclusionEquiv_apply
    (hJac : ((jacquetFunctor.{uG, max uG uV} h hU).obj ((normalizedInductionFunctor h hU).obj σ)).IsIrreducible)
    (S : Subrepresentation ((normalizedInductionFunctor h hU).obj σ).representation) (hS : S ≠ ⊥)
    (v : (jacquetFunctor.{uG, max uG uV} h hU).obj (subrepresentation ((normalizedInductionFunctor h hU).obj σ) S)) :
    subrepresentationJacquetInclusionEquiv h hU hUc σ hJac S hS v =
      hom ((jacquetFunctor.{uG, max uG uV} h hU).map (subtype ((normalizedInductionFunctor h hU).obj σ) S)) v := rfl

include hUc in
/-- The quotient by such a nonzero invariant subspace has zero Jacquet module
along the inducing parabolic. No finite-length premise is needed. -/
theorem quotient_jacquet_subsingleton_of_irreducible_induction_jacquet
    (hJac : ((jacquetFunctor.{uG, max uG uV} h hU).obj ((normalizedInductionFunctor h hU).obj σ)).IsIrreducible)
    (S : Subrepresentation ((normalizedInductionFunctor h hU).obj σ).representation) (hS : S ≠ ⊥) :
    Subsingleton ((jacquetFunctor.{uG, max uG uV} h hU).obj (quotient ((normalizedInductionFunctor h hU).obj σ) S)) := by
  let e := subrepresentationJacquetInclusionEquiv h hU hUc σ hJac S hS
  have hex := jacquetFunctor_map_isShortExact h hU hUc
    (subtype ((normalizedInductionFunctor h hU).obj σ) S) (mkQ ((normalizedInductionFunctor h hU).obj σ) S) (subtype_mkQ_isShortExact ((normalizedInductionFunctor h hU).obj σ) S)
  have hz (v : (jacquetFunctor.{uG, max uG uV} h hU).obj ((normalizedInductionFunctor h hU).obj σ)) : hom ((jacquetFunctor.{uG, max uG uV} h hU).map (mkQ ((normalizedInductionFunctor h hU).obj σ) S)) v = 0 := by
    obtain ⟨x, rfl⟩ := e.surjective v
    exact (show e x ∈ LinearMap.ker (hom ((jacquetFunctor.{uG, max uG uV} h hU).map (mkQ ((normalizedInductionFunctor h hU).obj σ) S))).toLinearMap by
      rw [← hex.2.2]
      exact ⟨x, rfl⟩)
  refine ⟨fun a b => ?_⟩
  obtain ⟨x, rfl⟩ := hex.2.1 a
  obtain ⟨y, rfl⟩ := hex.2.1 b
  rw [hz, hz]

section SecondJacquet

variable {Q L V : Subgroup G}
  (hO : IsSemidirectDecomposition Q L V) (hV : IsClosed (V : Set G))
  (hVc : Jacquet.Localization.IsLimitOfCompactSubgroups V)


include hUc hVc in
/-- For two simple middle Jacquet modules, detection of the nonzero proper
quotient by these two modules forces the second Jacquet module of the
subrepresentation to vanish. Detection is retained as a separate input. -/
theorem proper_subrepresentation_second_jacquet_subsingleton
    (hJac : ((jacquetFunctor.{uG, max uG uV} h hU).obj ((normalizedInductionFunctor h hU).obj σ)).IsIrreducible)
    (hJacO : ((jacquetFunctor.{uG, max uG uV} hO hV).obj ((normalizedInductionFunctor h hU).obj σ)).IsIrreducible)
    (S : Subrepresentation ((normalizedInductionFunctor h hU).obj σ).representation) (hS : S ≠ ⊥) (hStop : S ≠ ⊤)
    (hdetect : Subsingleton ((jacquetFunctor.{uG, max uG uV} h hU).obj (quotient ((normalizedInductionFunctor h hU).obj σ) S)) →
      Subsingleton ((jacquetFunctor.{uG, max uG uV} hO hV).obj (quotient ((normalizedInductionFunctor h hU).obj σ) S)) → Subsingleton (quotient ((normalizedInductionFunctor h hU).obj σ) S)) :
    Subsingleton ((jacquetFunctor.{uG, max uG uV} hO hV).obj (subrepresentation ((normalizedInductionFunctor h hU).obj σ) S)) := by
  have := hJacO
  have hr := quotient_jacquet_subsingleton_of_irreducible_induction_jacquet
    h hU hUc σ hJac S hS
  have hq : ¬ Subsingleton (quotient ((normalizedInductionFunctor h hU).obj σ) S) := by
    intro hz
    apply hStop
    apply le_antisymm le_top
    intro v _
    exact (Submodule.Quotient.mk_eq_zero S.toSubmodule).mp (hz.elim _ 0)
  have hsq : ¬ Subsingleton ((jacquetFunctor.{uG, max uG uV} hO hV).obj (quotient ((normalizedInductionFunctor h hU).obj σ) S)) :=
    fun hz => hq (hdetect hr hz)
  have hex := jacquetFunctor_map_isShortExact hO hV hVc
    (subtype ((normalizedInductionFunctor h hU).obj σ) S) (mkQ ((normalizedInductionFunctor h hU).obj σ) S) (subtype_mkQ_isShortExact ((normalizedInductionFunctor h hU).obj σ) S)
  let f := hom ((jacquetFunctor.{uG, max uG uV} hO hV).map (subtype ((normalizedInductionFunctor h hU).obj σ) S))
  let p := hom ((jacquetFunctor.{uG, max uG uV} hO hV).map (mkQ ((normalizedInductionFunctor h hU).obj σ) S))
  have hp : p ≠ 0 := by
    intro hp
    apply hsq
    refine ⟨fun a b => ?_⟩
    obtain ⟨x, rfl⟩ := hex.2.1 a
    obtain ⟨y, rfl⟩ := hex.2.1 b
    change p x = p y
    rw [hp]
    rfl
  have hinj := (Representation.IsIrreducible.injective_or_eq_zero p).resolve_right hp
  have hzero (x : (jacquetFunctor.{uG, max uG uV} hO hV).obj (subrepresentation ((normalizedInductionFunctor h hU).obj σ) S)) : f x = 0 := by
    apply hinj
    rw [map_zero]
    exact (show f x ∈ LinearMap.ker p.toLinearMap by
      rw [← hex.2.2]
      exact ⟨x, rfl⟩)
  exact ⟨fun a b => hex.1 ((hzero a).trans (hzero b).symm)⟩

end SecondJacquet

end Langlands.Aubert.General
