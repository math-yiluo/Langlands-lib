import Langlands.Group.GL.NonarchimedeanStatement
import Mathlib.Tactic.NoncommRing

/-!
# Intrinsic valuative neighborhoods in actual general linear groups
-/

namespace Langlands

open Filter Topology

universe u

variable {K : Type u} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsValuativeTopology K]

private theorem finitePiBasis {ι α κ : Type*} [Finite ι] {l : Filter α}
    {p : κ → Prop} {s : κ → Set α} (h : l.HasBasis p s) :
    (Filter.pi fun _ : ι => l).HasBasis p (fun k => {f | ∀ i, f i ∈ s k}) := by
  refine h.pi_self.to_hasBasis ?_ ?_
  · rintro ⟨I, k⟩ ⟨_, hk⟩
    exact ⟨k, hk, fun f hf i _ => hf i⟩
  · intro k hk
    exact ⟨(Set.univ, k), ⟨Set.finite_univ, hk⟩, fun f hf i => hf i (Set.mem_univ i)⟩

private theorem matrixZeroBasis (n : ℕ) :
    (𝓝 (0 : Matrix (Fin n) (Fin n) K)).HasBasis
      (fun _ : (ValuativeRel.ValueGroupWithZero K)ˣ => True)
      (fun γ => {A | ∀ i j, ValuativeRel.valuation K (A i j) < γ}) := by
  change (@nhds (Fin n → Fin n → K) Pi.topologicalSpace (fun _ _ => 0)).HasBasis
    (fun _ : (ValuativeRel.ValueGroupWithZero K)ˣ => True)
    (fun γ => {A : Fin n → Fin n → K |
      ∀ i j, ValuativeRel.valuation K (A i j) < γ})
  simpa only [nhds_pi, Set.mem_ofPred_eq] using
    finitePiBasis (ι := Fin n)
      (finitePiBasis (ι := Fin n) (IsValuativeTopology.hasBasis_nhds_zero K))

private theorem valuativeBallOpen (γ : (ValuativeRel.ValueGroupWithZero K)ˣ) :
    IsOpen {x : K | ValuativeRel.valuation K x < γ} := by
  rw [isOpen_iff_mem_nhds]
  intro x hx
  apply IsValuativeTopology.mem_nhds_iff'.mpr
  refine ⟨γ, fun y hy => ?_⟩
  have h := (ValuativeRel.valuation K).map_add (y - x) x
  rw [sub_add_cancel] at h
  exact h.trans_lt (max_lt hy hx)

private def valuativeMatrixMonoid (n : ℕ)
    (γ : (ValuativeRel.ValueGroupWithZero K)ˣ) (hγ : (γ : ValuativeRel.ValueGroupWithZero K) ≤ 1) :
    Submonoid (Matrix (Fin n) (Fin n) K) where
  carrier := {A | ∀ i j, ValuativeRel.valuation K ((A - 1) i j) < γ}
  one_mem' := by simp
  mul_mem' := by
    intro A B hA hB i j
    have hmul : ValuativeRel.valuation K (((A - 1) * (B - 1)) i j) < γ := by
      rw [Matrix.mul_apply]
      apply (ValuativeRel.valuation K).map_sum_lt γ.ne_zero
      intro k _
      rw [map_mul]
      calc
        ValuativeRel.valuation K ((A - 1) i k) *
            ValuativeRel.valuation K ((B - 1) k j)
            ≤ ValuativeRel.valuation K ((A - 1) i k) :=
          mul_le_of_le_one_right zero_le ((hB k j).le.trans hγ)
        _ < γ := hA i k
    have hid : A * B - 1 = (A - 1) * (B - 1) + (A - 1) + (B - 1) := by
      noncomm_ring
    rw [hid, Matrix.add_apply, Matrix.add_apply]
    exact ((ValuativeRel.valuation K).map_add _ _).trans_lt
      (max_lt (((ValuativeRel.valuation K).map_add _ _).trans_lt
        (max_lt hmul (hA i j))) (hB i j))

private theorem valuativeMatrixMonoidOpen (n : ℕ)
    (γ : (ValuativeRel.ValueGroupWithZero K)ˣ)
    (hγ : (γ : ValuativeRel.ValueGroupWithZero K) ≤ 1) :
    IsOpen (valuativeMatrixMonoid (K := K) n γ hγ : Set (Matrix (Fin n) (Fin n) K)) :=
  (valuativeBallOpen γ).matrix.preimage (continuous_id.sub continuous_const)

private theorem existsSmallMatrix (n : ℕ)
    {U : Set (Matrix (Fin n) (Fin n) K)} (hU : U ∈ 𝓝 1) :
    ∃ γ : (ValuativeRel.ValueGroupWithZero K)ˣ,
      ∀ A : Matrix (Fin n) (Fin n) K,
        (∀ i j, ValuativeRel.valuation K ((A - 1) i j) < γ) → A ∈ U := by
  have htranslate : (fun A : Matrix (Fin n) (Fin n) K => A + 1) ⁻¹' U ∈ 𝓝 0 :=
    (continuous_id.add continuous_const).continuousAt.preimage_mem_nhds (by simpa using hU)
  obtain ⟨γ, _, hγ⟩ := (matrixZeroBasis (K := K) n).mem_iff.mp htranslate
  exact ⟨γ, fun A hA => by simpa using hγ hA⟩

/-- The actual general linear group over a valuative field is nonarchimedean. -/
theorem valuativeGeneralLinearNonarchimedean :
    ValuativeGeneralLinearNonarchimedean.{u} := by
  intro K _ _ _ _ n
  refine { is_nonarchimedean := ?_ }
  intro U hU
  change U ∈ 𝓝 (1 : (Matrix (Fin n) (Fin n) K)ˣ) at hU
  rw [Units.isInducing_embedProduct.nhds_eq_comap, Filter.mem_comap] at hU
  obtain ⟨V, hV, hVU⟩ := hU
  have hV' : V ∈ 𝓝 (1 : Matrix (Fin n) (Fin n) K) ×ˢ
      𝓝 (1 : (Matrix (Fin n) (Fin n) K)ᵐᵒᵖ) := by
    change V ∈ 𝓝 ((1 : Matrix (Fin n) (Fin n) K), 1) at hV
    rw [nhds_prod_eq] at hV
    exact hV
  obtain ⟨V₁, hV₁, V₂, hV₂, hV₁₂⟩ := Filter.mem_prod_iff.mp hV'
  have hV₂' : MulOpposite.op ⁻¹' V₂ ∈ 𝓝 (1 : Matrix (Fin n) (Fin n) K) :=
    MulOpposite.continuous_op.continuousAt.preimage_mem_nhds (by simpa using hV₂)
  obtain ⟨γ, hγ⟩ := existsSmallMatrix n (inter_mem hV₁ hV₂')
  let δ : (ValuativeRel.ValueGroupWithZero K)ˣ :=
    Units.mk0 (min (γ : ValuativeRel.ValueGroupWithZero K) 1)
      (ne_of_gt (lt_min (pos_iff_ne_zero.mpr γ.ne_zero) zero_lt_one))
  have hδ₁ : (δ : ValuativeRel.ValueGroupWithZero K) ≤ 1 := min_le_right _ _
  have hδγ : (δ : ValuativeRel.ValueGroupWithZero K) ≤ γ := min_le_left _ _
  let S := valuativeMatrixMonoid (K := K) n δ hδ₁
  refine ⟨{ S.units with isOpen' :=
    Submonoid.isOpen_units (valuativeMatrixMonoidOpen n δ hδ₁) }, ?_⟩
  intro g hg
  have hg' : g.val ∈ S ∧ (g⁻¹).val ∈ S := hg
  have hmatrix := hγ g.val (fun i j => (hg'.1 i j).trans_le hδγ)
  have hinverse := hγ (g⁻¹).val (fun i j => (hg'.2 i j).trans_le hδγ)
  exact hVU (hV₁₂ ⟨hmatrix.1, hinverse.2⟩)

end Langlands
