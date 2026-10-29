import Langlands.Representation.Geometric.FlattenedLevi
import Langlands.Representation.Classification.SegmentEdgeJacquetReduction

/-! Whole-target geometric pieces in flattened refined-Levi coordinates. -/

noncomputable section

namespace Langlands.Geometric

open GeneralLinear CuspidalSupport CategoryTheory
open Langlands.Classification.SegmentEdge

universe uF uV

section Intersections

variable {F : Type uF} [Field F] {n : ℕ} (B C : BlockShape n)
  (S : BlockRefinement B)

/-- Ambient membership in the flattened Levi is exactly refined membership. -/
theorem leviEmbedding_mem_flattenedLevi_iff (m : B.Levi F) :
    B.leviEmbedding F m ∈ (B.flatten S).leviSubgroup F ↔ m ∈ refinedLevi F B S := by
  constructor
  · rintro ⟨d, hd⟩
    have hm : (flattenedLeviEquiv F B S d).val = m :=
      B.leviEmbedding_injective F ((flattenedLeviEquiv_embedding F B S d).trans hd)
    exact hm ▸ (flattenedLeviEquiv F B S d).property
  · intro hm
    exact ⟨(flattenedLeviEquiv F B S).symm ⟨m, hm⟩,
      flattenedLeviEquiv_symm_embedding F B S ⟨m, hm⟩⟩

/-- The fine block diagonal subgroup lies in the coarse block diagonal subgroup. -/
theorem flattenedLeviSubgroup_le :
    (B.flatten S).leviSubgroup F ≤ B.leviSubgroup F := by
  rintro g ⟨d, rfl⟩
  exact ⟨(flattenedLeviEquiv F B S d).val, flattenedLeviEquiv_embedding F B S d⟩

/-- Conjugating the flattened source onto the target identifies the source
intersection with the actual refined Levi, without a minimality assumption. -/
theorem sourceLevi_eq_refined_of_flattened_conjugates (w : Equiv.Perm (Fin n))
    (hw : ConjugatesLevi (F := F) (B.flatten S) C w) :
    sourceLevi F B C w = refinedLevi F B S := by
  ext m
  change (MulAut.conj (permutation n F w)) (B.leviEmbedding F m) ∈
    C.leviSubgroup F ↔ m ∈ refinedLevi F B S
  rw [← hw]
  exact (Subgroup.mem_map_iff_mem
    (f := (MulAut.conj (permutation n F w)).toMonoidHom)
    (MulAut.conj (permutation n F w)).injective).trans
      (leviEmbedding_mem_flattenedLevi_iff B S m)

/-- The target intersection is the whole target when it is conjugate to the
flattened source refinement. -/
theorem targetLevi_eq_top_of_flattened_conjugates (w : Equiv.Perm (Fin n))
    (hw : ConjugatesLevi (F := F) (B.flatten S) C w) :
    sourceLevi F C B w⁻¹ = ⊤ := by
  have hfull := targetLevi_eq_top_of_conjugates (B.flatten S) C w hw
  apply top_unique
  intro m _
  have hm : m ∈ sourceLevi F C (B.flatten S) w⁻¹ := hfull ▸ Subgroup.mem_top m
  exact flattenedLeviSubgroup_le B S hm

end Intersections

section Representation

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p}
  (T : F.TopologicalData) {n : ℕ} (B C : BlockShape n)
  (w : Equiv.Perm (Fin n)) (S : BlockRefinement B) (R : BlockRefinement C)
  (hS : sourceLevi F.Carrier B C w = refinedLevi F.Carrier B S)
  (hR : sourceLevi F.Carrier C B w⁻¹ = refinedLevi F.Carrier C R)
  (hw : ConjugatesLevi (F := F.Carrier) (B.flatten S) C w)

set_option maxHeartbeats 1200000 in
/-- When the flattened source refinement is conjugated onto the whole target,
the geometric piece is its actual transported normalized refined Jacquet
module. No source cuspidality, minimality, or vanishing premise is needed. -/
def wholeLeviGeometricPieceEquiv :
    letI := T.topology
    ∀ A : SmoothRep.{0, uF, uV} ℂ (B.Levi F.Carrier),
      ((geometricPieceFunctor T B C w S R hS hR).obj A).ρ.Equiv
        (transport (B.flatten S) C w hw
          ((T.normalizedRefinedJacquet B S A.representation).comp
            (flattenedLeviEquiv F.Carrier B S).toMonoidHom)) := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  intro A
  let J := (T.normalizedRefinedJacquetFunctor B S).obj A
  let e := flattenedLeviEquiv F.Carrier B S
  let ρ := J.representation.comp e.toMonoidHom
  have eJ0 : J.representation.Equiv (ρ.comp e.symm.toMonoidHom) :=
    (FiniteTensorFiltration.compSymmComp J.representation e).symm
  let J' := (subgroupEqualityFunctor _ _ hS.symm).obj J
  let ψ := e.symm.toMonoidHom.comp (MulEquiv.subgroupCongr hS.symm).symm.toMonoidHom
  have hψ : ∀ x, (B.flatten S).leviEmbedding F.Carrier (ψ x) =
      B.leviEmbedding F.Carrier x.val := by
    intro x
    exact flattenedLeviEquiv_symm_embedding F.Carrier B S
      ((MulEquiv.subgroupCongr hS.symm).symm x)
  have eJ' : J'.representation.Equiv (ρ.comp ψ) :=
    subgroupEqualityCompEquiv _ _ hS.symm J ρ e.symm.toMonoidHom eJ0
  let τ := transport (B.flatten S) C w hw ρ
  let Q := (intersectionTransportFunctor F.Carrier B C w).obj J'
  have eQ : Q.representation.Equiv
      (τ.comp (sourceLevi F.Carrier C B w⁻¹).subtype) :=
    intersectionTransportEquivOf B C (B.flatten S) w hw ψ hψ J'.representation ρ eJ'
  let Q' := (subgroupEqualityFunctor _ _ hR).obj Q
  have eQ' : Q'.representation.Equiv (τ.comp (refinedLevi F.Carrier C R).subtype) :=
    subgroupEqualityEquiv _ _ hR Q τ eQ
  have hfullR : refinedLevi F.Carrier C R = ⊤ :=
    hR.symm.trans (targetLevi_eq_top_of_flattened_conjugates B C S w hw)
  have hρ : IsSmooth ρ := isSmooth_comp e.toMonoidHom
    (flattenedLeviEquivContinuous F.Carrier B S).continuous J.isSmooth
  have hτ : IsSmooth τ := isSmooth_transport (B.flatten S) C w hw hρ
  change (T.normalizedRefinedInduced C R Q'.representation).Equiv τ
  exact fullRefinedInductionEquiv T C R hfullR Q'.representation τ eQ' hτ

end Representation
end Langlands.Geometric
