import Langlands.Representation.Archimedean.RealInductionStagesFiltration
import Langlands.Representation.Archimedean.RealSliceSurjective
import Langlands.Representation.Archimedean.RealStandardNontrivialProof
import Mathlib.LinearAlgebra.Projection

/-! # Irreducibility descends to consecutive blocks of a real standard module -/

noncomputable section

open scoped TensorProduct

set_option autoImplicit false

namespace Langlands.Archimedean

attribute [local instance 100] LieRing.ofAssociativeRing

open Langlands.LocalFactor.Archimedean InductionStages

private theorem exists_compact_projection {r : ℕ} {ds : List RealBlock}
    (W : Submodule ℂ (KFin r ds))
    (hW : ∀ k v, v ∈ W → kRep r ds k v ∈ W) :
    ∃ P : KFin r ds →ₗ[ℂ] KFin r ds,
      (∀ k v, P (kRep r ds k v) = kRep r ds k (P v)) ∧
      (∀ v, P v ∈ W) ∧ ∀ v ∈ W, P v = v := by
  obtain ⟨C, hC⟩ := W.exists_isCompl
  let A := W.projection C hC
  refine ⟨avg A, avg_kRep A, ?_, ?_⟩
  · intro v
    exact avg_mem_of_forall A W v fun k =>
      hW k⁻¹ _ (W.projection_apply_mem hC _)
  · intro v hv
    have h := avg_sub_mem A ⊥ v v fun k => by
      rw [conj_apply, W.projection_apply_of_mem_left hC (hW k v hv),
        kRep_inv_kRep, sub_self]
      exact Submodule.zero_mem _
    exact sub_eq_zero.mp ((Submodule.mem_bot ℂ).mp h)

/-- In a real standard module formed by consecutive inducing blocks, the standard
module of any consecutive sublist is irreducible if the full module is irreducible. -/
def RealStandardIrreducibilityInStagesStatement : Prop :=
  ∀ (n : ℕ) (pre ds post : List RealBlock), realRank (pre ++ ds ++ post) = n →
    IsIrreducibleGKModule (realStandardRep n (pre ++ ds ++ post))
      (realStandardLie n (pre ++ ds ++ post)) →
    IsIrreducibleGKModule (realStandardRep (realRank ds) ds)
      (realStandardLie (realRank ds) ds)

theorem realStandardIrreducibilityInStages : RealStandardIrreducibilityInStagesStatement := by
  intro n pre ds post hn hirr
  let r := realRank ds
  let a := realRank pre
  let blocks := pre ++ ds ++ post
  have h : a + r ≤ n := by
    simp only [realRank_append'] at hn
    dsimp only [a, r]
    omega
  refine ⟨realStandardNontrivial r ds rfl, fun W hWK hWL => ?_⟩
  obtain ⟨P, hPK, hPW, hPid⟩ := exists_compact_projection W
    (fun k v hv => hWK (toUnitary r k) v hv)
  let σ (k : unitaryCompact ℝ n) : KFin n blocks →ₗ[ℂ] KFin r ds :=
    sliceK (post := post) h rfl rfl k
  let Q : KFin n blocks →ₗ[ℂ] KFin n blocks := ind h rfl rfl rfl hn P hPK
  let U : Submodule ℂ (KFin n blocks) := ⨅ k, W.comap (σ k)
  have hU (v : KFin n blocks) : v ∈ U ↔ ∀ k, σ k v ∈ W := by
    simp [U]
  have hQ (k : unitaryCompact ℝ n) (v : KFin n blocks) : σ k (Q v) = P (σ k v) :=
    sliceK_ind h rfl rfl rfl hn hPK k v
  have hQmem (v : KFin n blocks) : Q v ∈ U := (hU _).mpr fun k => hQ k v ▸ hPW _
  have hQid (v : KFin n blocks) (hv : v ∈ U) : Q v = v := by
    apply sub_eq_zero.mp
    apply eq_zero_of_sliceK h rfl rfl
    intro k
    change σ k (Q v - v) = 0
    rw [map_sub, hQ, hPid _ ((hU _).mp hv k), sub_self]
  have hUK (k : Matrix.unitaryGroup (Fin n) ℝ) (v : KFin n blocks) (hv : v ∈ U) :
      realStandardRep n blocks k v ∈ U := by
    apply (hU _).mpr
    intro κ
    change σ κ (kRep n blocks (ofUnitary n k) v) ∈ W
    exact (sliceK_kRep h rfl rfl κ (ofUnitary n k) v).symm ▸
      (hU _).mp hv (κ * ofUnitary n k)
  have hULreal (X : Matrix (Fin n) (Fin n) ℝ) (v : KFin n blocks) (hv : v ∈ U) :
      lie n blocks X v ∈ U := by
    have hPdef (Y : Matrix (Fin r) (Fin r) ℝ) (f : KFin r ds) :
        P (lie r ds Y f) - lie r ds Y (P f) ∈ W :=
      W.sub_mem (hPW _) (hWL (1 ⊗ₜ Y) _ (hPW f))
    apply (hU _).mpr
    intro κ
    have hdef : σ κ (Q (lie n blocks X v) - lie n blocks X (Q v)) ∈ W :=
      sliceK_ind_lie_sub_mem h rfl rfl rfl hn hPK W hPdef X v κ
    rw [hQid v hv, map_sub, hQ] at hdef
    simpa only [sub_sub_cancel] using W.sub_mem (hPW (σ κ (lie n blocks X v))) hdef
  have hUL (X : ℂ ⊗[ℝ] Matrix (Fin n) (Fin n) ℝ) (v : KFin n blocks) (hv : v ∈ U) :
      realStandardLie n blocks X v ∈ U := by
    induction X using TensorProduct.inductionOn with
    | tmul c X =>
      have hc : (c ⊗ₜ[ℝ] X : ℂ ⊗[ℝ] Matrix (Fin n) (Fin n) ℝ) =
          c • ((1 : ℂ) ⊗ₜ[ℝ] X) := by
        rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
      rw [hc, map_smul, LinearMap.smul_apply]
      exact U.smul_mem _ (hULreal X v hv)
    | add X Y hX hY =>
      rw [map_add, LinearMap.add_apply]
      exact U.add_mem hX hY
  have hσsurj : Function.Surjective (σ 1) :=
    RealSliceSurjective.sliceK_one_surjective h rfl rfl hn
  rcases hirr.2 U hUK hUL with hbot | htop
  · left
    apply (W.eq_bot_iff).mpr
    intro v hv
    obtain ⟨F, hF⟩ := hσsurj v
    have h0 : Q F = 0 := (Submodule.mem_bot ℂ).mp (hbot ▸ hQmem F)
    simpa only [h0, map_zero, hF, hPid v hv] using (hQ 1 F).symm
  · right
    apply Submodule.eq_top_iff'.mpr
    intro v
    obtain ⟨F, hF⟩ := hσsurj v
    rw [← hF]
    exact (hU F).mp (htop ▸ Submodule.mem_top) 1

end Langlands.Archimedean
