import Langlands.GroupScheme.Composition.CayleyIdentities
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-! # Existence of a Peirce frame for an isotropic idempotent of a Cayley datum -/

noncomputable section

universe u

open Module

namespace Langlands.GroupScheme.CayleyDatum

variable {K : Type u} [Field K] (c : CayleyDatum K)

local notation "μ" => c.multiplication

namespace PeirceExistence

/-- The Peirce space `U = {y | T(y) = 0, b(y, e) = 0, e y = y}`. -/
def peirceU (e : CayleyVector K) : Submodule K (CayleyVector K) :=
  LinearMap.ker (c.form.flip c.unit) ⊓ LinearMap.ker (c.form.flip e) ⊓
    LinearMap.ker (c.multiplication e - LinearMap.id)

/-- The Peirce space `V = {y | T(y) = 0, b(y, e) = 0, e y = 0}`. -/
def peirceV (e : CayleyVector K) : Submodule K (CayleyVector K) :=
  LinearMap.ker (c.form.flip c.unit) ⊓ LinearMap.ker (c.form.flip e) ⊓
    LinearMap.ker (c.multiplication e)

variable {c}

theorem mem_peirceU {e y : CayleyVector K} :
    y ∈ peirceU c e ↔ c.trace y = 0 ∧ c.form y e = 0 ∧ μ e y = y := by
  simp only [peirceU, Submodule.mem_inf, LinearMap.mem_ker, LinearMap.sub_apply,
    LinearMap.id_apply, sub_eq_zero, and_assoc, trace]
  exact Iff.rfl

theorem mem_peirceV {e y : CayleyVector K} :
    y ∈ peirceV c e ↔ c.trace y = 0 ∧ c.form y e = 0 ∧ μ e y = 0 := by
  simp only [peirceV, Submodule.mem_inf, LinearMap.mem_ker, and_assoc, trace]
  exact Iff.rfl

section Peirce

variable {e : CayleyVector K}

theorem form_e_e (he0 : c.norm e = 0) : c.form e e = 0 := by
  rw [c.form_self, he0, mul_zero]

theorem e_mul_e (he0 : c.norm e = 0) (he1 : c.trace e = 1) : μ e e = e := by
  rw [c.mul_self, he1, he0, one_smul, zero_smul, sub_zero]

theorem e_mul_e_mul (he0 : c.norm e = 0) (he1 : c.trace e = 1) (y : CayleyVector K) :
    μ e (μ e y) = μ e y := by
  rw [c.mul_mul_self_left, e_mul_e he0 he1]

theorem trace_e_mul (he1 : c.trace e = 1) {y : CayleyVector K} (hy1 : c.trace y = 0)
    (hye : c.form y e = 0) : c.trace (μ e y) = 0 := by
  have h := c.form_mul_left e y c.unit
  rw [c.mul_unit, hye, he1, one_mul, add_zero] at h
  change c.form (μ e y) c.unit = 0
  rw [h]
  exact hy1

theorem form_e_mul_e (he0 : c.norm e = 0) (y : CayleyVector K) : c.form (μ e y) e = 0 := by
  have h := c.form_mul_mul_left e y c.unit
  rw [c.mul_unit, he0, zero_mul] at h
  exact h

theorem mul_e_eq (he1 : c.trace e = 1) {y : CayleyVector K} (hy1 : c.trace y = 0)
    (hye : c.form y e = 0) : μ y e = y - μ e y := by
  have h := c.mul_add_mul_comm e y
  rw [he1, hy1, c.form_comm e y, hye, one_smul, zero_smul, zero_smul, add_zero,
    sub_zero] at h
  rw [eq_sub_iff_add_eq, add_comm]
  exact h

theorem norm_of_mem_U (he0 : c.norm e = 0) {y : CayleyVector K} (hy : y ∈ peirceU c e) :
    c.norm y = 0 := by
  obtain ⟨-, -, h⟩ := mem_peirceU.mp hy
  rw [← h, c.norm_mul, he0, zero_mul]

theorem mul_e_of_mem_V (he1 : c.trace e = 1) {y : CayleyVector K} (hy : y ∈ peirceV c e) :
    μ y e = y := by
  obtain ⟨h1, h2, h3⟩ := mem_peirceV.mp hy
  rw [mul_e_eq he1 h1 h2, h3, sub_zero]

theorem norm_of_mem_V (he0 : c.norm e = 0) (he1 : c.trace e = 1) {y : CayleyVector K}
    (hy : y ∈ peirceV c e) : c.norm y = 0 := by
  rw [← mul_e_of_mem_V he1 hy, c.norm_mul, he0, mul_zero]

theorem form_of_mem_U (he0 : c.norm e = 0) {y z : CayleyVector K} (hy : y ∈ peirceU c e)
    (hz : z ∈ peirceU c e) : c.form y z = 0 := by
  have h := c.norm_add y z
  rw [norm_of_mem_U he0 (add_mem hy hz), norm_of_mem_U he0 hy, norm_of_mem_U he0 hz] at h
  linear_combination -h

theorem form_of_mem_V (he0 : c.norm e = 0) (he1 : c.trace e = 1) {y z : CayleyVector K}
    (hy : y ∈ peirceV c e) (hz : z ∈ peirceV c e) : c.form y z = 0 := by
  have h := c.norm_add y z
  rw [norm_of_mem_V he0 he1 (add_mem hy hz), norm_of_mem_V he0 he1 hy,
    norm_of_mem_V he0 he1 hz] at h
  linear_combination -h

/-- Every vector decomposes along `span {1, e} + U + V`. -/
theorem decomp (he0 : c.norm e = 0) (he1 : c.trace e = 1) (y : CayleyVector K) :
    ∃ a b : K, ∃ p ∈ peirceU c e, ∃ q ∈ peirceV c e, y = a • c.unit + b • e + p + q := by
  set w := y - c.form y e • c.unit - (c.trace y - 2 * c.form y e) • e with hw
  have hBue : c.form c.unit e = 1 := by rw [c.form_comm]; exact he1
  have hw1 : c.trace w = 0 := by
    rw [hw, c.trace_sub, c.trace_sub, c.trace_smul, c.trace_smul, c.trace_unit, he1]
    ring
  have hwe : c.form w e = 0 := by
    rw [hw]
    simp only [map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul]
    rw [hBue, form_e_e he0]
    ring
  refine ⟨c.form y e, c.trace y - 2 * c.form y e, μ e w, ?_, w - μ e w, ?_, ?_⟩
  · exact mem_peirceU.mpr ⟨trace_e_mul he1 hw1 hwe, form_e_mul_e he0 w, e_mul_e_mul he0 he1 w⟩
  · refine mem_peirceV.mpr ⟨?_, ?_, ?_⟩
    · rw [c.trace_sub, hw1, trace_e_mul he1 hw1 hwe, sub_zero]
    · rw [map_sub, LinearMap.sub_apply, hwe, form_e_mul_e he0, sub_zero]
    · rw [map_sub, e_mul_e_mul he0 he1, sub_self]
  · rw [hw]
    abel

theorem sup_eq_top (he0 : c.norm e = 0) (he1 : c.trace e = 1) :
    Submodule.span K (Set.range ![c.unit, e]) ⊔ peirceU c e ⊔ peirceV c e = ⊤ := by
  refine eq_top_iff.mpr fun y _ => ?_
  obtain ⟨a, b, p, hp, q, hq, rfl⟩ := decomp he0 he1 y
  refine add_mem (add_mem (Submodule.mem_sup_left (Submodule.mem_sup_left ?_))
    (Submodule.mem_sup_left (Submodule.mem_sup_right hp))) (Submodule.mem_sup_right hq)
  exact add_mem (Submodule.smul_mem _ _ (Submodule.subset_span ⟨0, by simp⟩))
    (Submodule.smul_mem _ _ (Submodule.subset_span ⟨1, by simp⟩))

theorem eight_le_finrank (he0 : c.norm e = 0) (he1 : c.trace e = 1) :
    8 ≤ 2 + finrank K (peirceU c e) + finrank K (peirceV c e) := by
  have h1 := Submodule.finrank_add_le_finrank_add_finrank
    (Submodule.span K (Set.range ![c.unit, e]) ⊔ peirceU c e) (peirceV c e)
  have h2 := Submodule.finrank_add_le_finrank_add_finrank
    (Submodule.span K (Set.range ![c.unit, e])) (peirceU c e)
  have h3 : finrank K (Submodule.span K (Set.range ![c.unit, e])) ≤ 2 := by
    have h4 := finrank_range_le_card (R := K) ![c.unit, e]
    rw [Fintype.card_fin] at h4
    exact h4
  rw [sup_eq_top he0 he1, finrank_top, Module.finrank_fin_fun] at h1
  omega

/-- A vector orthogonal to `1`, `e`, `U` and `V` is zero. -/
theorem eq_zero_of_orthogonal (he0 : c.norm e = 0) (he1 : c.trace e = 1) {x : CayleyVector K}
    (h1 : c.trace x = 0) (he : c.form x e = 0) (hU : ∀ p ∈ peirceU c e, c.form x p = 0)
    (hV : ∀ q ∈ peirceV c e, c.form x q = 0) : x = 0 := by
  refine c.polar_nondegenerate x fun y => ?_
  obtain ⟨a, b, p, hp, q, hq, rfl⟩ := decomp he0 he1 y
  change c.form x _ = 0
  have h1' : c.form x c.unit = 0 := h1
  simp only [map_add, map_smul, smul_eq_mul, h1', he, hU p hp, hV q hq, mul_zero, add_zero]

variable (c e) in
/-- The pairing of `V` against `U`. -/
def pairVU : peirceV c e →ₗ[K] Module.Dual K (peirceU c e) :=
  (c.form.compl₁₂ (peirceU c e).subtype (peirceV c e).subtype).flip

variable (c e) in
/-- The pairing of `U` against `V`. -/
def pairUV : peirceU c e →ₗ[K] Module.Dual K (peirceV c e) :=
  (c.form.compl₁₂ (peirceV c e).subtype (peirceU c e).subtype).flip

theorem pairVU_apply (v : peirceV c e) (p : peirceU c e) :
    pairVU c e v p = c.form (p : CayleyVector K) v := rfl

theorem pairUV_apply (p : peirceU c e) (v : peirceV c e) :
    pairUV c e p v = c.form (v : CayleyVector K) p := rfl

theorem pairVU_injective (he0 : c.norm e = 0) (he1 : c.trace e = 1) :
    Function.Injective (pairVU c e) := by
  refine (injective_iff_map_eq_zero _).mpr fun v hv => ?_
  obtain ⟨h1, h2, -⟩ := mem_peirceV.mp v.2
  refine Subtype.ext (eq_zero_of_orthogonal he0 he1 h1 h2 (fun p hp => ?_) (fun q hq => ?_))
  · have := LinearMap.congr_fun hv ⟨p, hp⟩
    rw [pairVU_apply, LinearMap.zero_apply] at this
    rw [c.form_comm]
    exact this
  · exact form_of_mem_V he0 he1 v.2 hq

theorem pairUV_injective (he0 : c.norm e = 0) (he1 : c.trace e = 1) :
    Function.Injective (pairUV c e) := by
  refine (injective_iff_map_eq_zero _).mpr fun p hp => ?_
  obtain ⟨h1, h2, -⟩ := mem_peirceU.mp p.2
  refine Subtype.ext (eq_zero_of_orthogonal he0 he1 h1 h2 (fun q hq => ?_) (fun v hv => ?_))
  · exact form_of_mem_U he0 p.2 hq
  · have := LinearMap.congr_fun hp ⟨v, hv⟩
    rw [pairUV_apply, LinearMap.zero_apply] at this
    rw [c.form_comm]
    exact this

theorem finrank_V_eq_U (he0 : c.norm e = 0) (he1 : c.trace e = 1) :
    finrank K (peirceV c e) = finrank K (peirceU c e) := by
  have h1 := LinearMap.finrank_le_finrank_of_injective (pairVU_injective he0 he1)
  have h2 := LinearMap.finrank_le_finrank_of_injective (pairUV_injective he0 he1)
  rw [Subspace.dual_finrank_eq] at h1 h2
  omega

theorem three_le_finrank_U (he0 : c.norm e = 0) (he1 : c.trace e = 1) :
    3 ≤ finrank K (peirceU c e) := by
  have := eight_le_finrank he0 he1
  rw [finrank_V_eq_U he0 he1] at this
  omega

theorem pairVU_surjective (he0 : c.norm e = 0) (he1 : c.trace e = 1) :
    Function.Surjective (pairVU c e) :=
  (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
    (by rw [Subspace.dual_finrank_eq, finrank_V_eq_U he0 he1])).mp (pairVU_injective he0 he1)

end Peirce

end PeirceExistence

open PeirceExistence in
/-- An isotropic vector `e` of trace one has three vectors `u a` in its Peirce space
`U = {y | e y = y, T(y) = 0, b(y, e) = 0}` and three vectors `v b` in its Peirce space
`V = {y | e y = 0, T(y) = 0, b(y, e) = 0}` with `b(u a, v b) = δ_{ab}`. -/
theorem exists_peirceFrame {e : CayleyVector K} (hN : c.norm e = 0) (hT : c.trace e = 1) :
    ∃ u v : Fin 3 → CayleyVector K,
      (∀ a, c.multiplication e (u a) = u a ∧ c.trace (u a) = 0 ∧ c.form (u a) e = 0) ∧
      (∀ a, c.multiplication e (v a) = 0 ∧ c.trace (v a) = 0 ∧ c.form (v a) e = 0) ∧
      (∀ a b, c.form (u a) (v b) = if a = b then 1 else 0) := by
  have hd := three_le_finrank_U hN hT
  let bU := Module.finBasis K (peirceU c e)
  let idx : Fin 3 → Fin (finrank K (peirceU c e)) := Fin.castLE hd
  have hsurj := pairVU_surjective hN hT
  let v : Fin 3 → peirceV c e := fun j => (hsurj (bU.coord (idx j))).choose
  have hv : ∀ j, pairVU c e (v j) = bU.coord (idx j) := fun j =>
    (hsurj (bU.coord (idx j))).choose_spec
  refine ⟨fun i => bU (idx i), fun j => v j, fun i => ?_, fun j => ?_, fun i j => ?_⟩
  · obtain ⟨h1, h2, h3⟩ := mem_peirceU.mp (bU (idx i)).2
    exact ⟨h3, h1, h2⟩
  · obtain ⟨h1, h2, h3⟩ := mem_peirceV.mp (v j).2
    exact ⟨h3, h1, h2⟩
  · have := LinearMap.congr_fun (hv j) (bU (idx i))
    rw [pairVU_apply, Basis.coord_apply, Basis.repr_self, Finsupp.single_apply] at this
    rw [this]
    by_cases hij : i = j
    · subst hij
      simp
    · have hne : idx i ≠ idx j := fun h => hij (Fin.castLE_injective hd h)
      simp [hne, hij]

end Langlands.GroupScheme.CayleyDatum
