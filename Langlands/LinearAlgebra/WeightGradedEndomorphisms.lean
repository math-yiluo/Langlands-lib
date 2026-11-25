import Langlands.MathlibBase

/-! # Endomorphisms of a weight-graded vector space -/

noncomputable section

open Set Function Module

namespace Langlands.LinearAlgebra.WeightGraded

variable {k U X : Type*} [Field k] [AddCommGroup U] [Module k U] [AddCommGroup X]
  (W : X → Submodule k U)

/-- The endomorphisms raising every weight by `χ`. -/
def shift (χ : X) : Submodule k (Module.End k U) where
  carrier := {f | ∀ μ, ∀ u ∈ W μ, f u ∈ W (μ + χ)}
  add_mem' := fun hf hg μ u hu => Submodule.add_mem _ (hf μ u hu) (hg μ u hu)
  zero_mem' := fun _ _ _ => Submodule.zero_mem _
  smul_mem' := fun c _ hf μ u hu => Submodule.smul_mem _ c (hf μ u hu)

variable {W}

theorem mem_shift {χ : X} {f : Module.End k U} :
    f ∈ shift W χ ↔ ∀ μ, ∀ u ∈ W μ, f u ∈ W (μ + χ) :=
  Iff.rfl

theorem mapsTo_of_mem_shift {χ : X} {f : Module.End k U} (hf : f ∈ shift W χ) {μ ν : X}
    (h : μ + χ = ν) : MapsTo f (W μ) (W ν) := by
  subst h
  exact fun u hu => hf μ u hu

theorem mul_mem_shift {χ χ' : X} {f g : Module.End k U} (hf : f ∈ shift W χ)
    (hg : g ∈ shift W χ') : f * g ∈ shift W (χ + χ') := by
  intro μ u hu
  have h := hf _ _ (hg μ u hu)
  rwa [add_assoc, add_comm χ' χ] at h

theorem commutator_mem_shift {χ χ' : X} {f g : Module.End k U} (hf : f ∈ shift W χ)
    (hg : g ∈ shift W χ') : f * g - g * f ∈ shift W (χ + χ') := by
  refine Submodule.sub_mem _ (mul_mem_shift hf hg) ?_
  rw [add_comm χ χ']
  exact mul_mem_shift hg hf

variable (W) in
/-- `t` acts on every weight space `W μ` by the scalar `φ μ`. -/
def IsScalarOn (φ : X → k) (t : Module.End k U) : Prop :=
  ∀ μ, ∀ u ∈ W μ, t u = φ μ • u

variable (W) in
theorem IsScalarOn.mem_shift_zero {φ : X → k} {t : Module.End k U} (ht : IsScalarOn W φ t) :
    t ∈ shift W 0 := by
  intro μ u hu
  rw [add_zero, ht μ u hu]
  exact Submodule.smul_mem _ _ hu

omit [AddCommGroup X] in
theorem IsScalarOn.add {φ ψ : X → k} {t s : Module.End k U} (ht : IsScalarOn W φ t)
    (hs : IsScalarOn W ψ s) : IsScalarOn W (φ + ψ) (t + s) := by
  intro μ u hu
  rw [LinearMap.add_apply, ht μ u hu, hs μ u hu, Pi.add_apply, add_smul]

omit [AddCommGroup X] in
theorem IsScalarOn.smul {φ : X → k} {t : Module.End k U} (ht : IsScalarOn W φ t) (c : k) :
    IsScalarOn W (c • φ) (c • t) := by
  intro μ u hu
  rw [LinearMap.smul_apply, ht μ u hu, Pi.smul_apply, smul_smul, smul_eq_mul]

omit [AddCommGroup X] in
theorem IsScalarOn.mul {φ ψ : X → k} {t s : Module.End k U} (ht : IsScalarOn W φ t)
    (hs : IsScalarOn W ψ s) : IsScalarOn W (φ * ψ) (t * s) := by
  intro μ u hu
  rw [Module.End.mul_apply, hs μ u hu, map_smul, ht μ u hu, smul_smul, Pi.mul_apply,
    mul_comm]

omit [AddCommGroup X] in
theorem isScalarOn_zero : IsScalarOn W (0 : X → k) 0 := by
  intro μ u _
  simp

omit [AddCommGroup X] in
theorem IsScalarOn.sum {κ : Type*} (s : Finset κ) {φ : κ → X → k} {t : κ → Module.End k U}
    (h : ∀ a ∈ s, IsScalarOn W (φ a) (t a)) :
    IsScalarOn W (∑ a ∈ s, φ a) (∑ a ∈ s, t a) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (isScalarOn_zero (W := W))
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    exact (h a (Finset.mem_insert_self a s)).add
      (ih fun b hb => h b (Finset.mem_insert_of_mem hb))

omit [AddCommGroup X] in
/-- Two endomorphisms that agree on every weight space agree, when the weight spaces span. -/
theorem ext_of_iSup_eq_top (hW : ⨆ μ, W μ = ⊤) {f g : Module.End k U}
    (h : ∀ μ, ∀ u ∈ W μ, f u = g u) : f = g := by
  ext u
  have hu : u ∈ ⨆ μ, W μ := by rw [hW]; exact Submodule.mem_top
  induction hu using Submodule.iSup_induction' with
  | mem μ u hu => exact h μ u hu
  | zero => simp
  | add u v _ _ hu hv => rw [map_add, map_add, hu, hv]

theorem IsScalarOn.commutator {φ : X → k} {t : Module.End k U} (ht : IsScalarOn W φ t)
    (hφ : ∀ μ ν, φ (μ + ν) = φ μ + φ ν) (hW : ⨆ μ, W μ = ⊤) {χ : X}
    {f : Module.End k U} (hf : f ∈ shift W χ) : t * f - f * t = φ χ • f := by
  refine ext_of_iSup_eq_top hW fun μ u hu => ?_
  rw [LinearMap.sub_apply, Module.End.mul_apply, Module.End.mul_apply, ht _ _ (hf μ u hu),
    ht μ u hu, map_smul, hφ, LinearMap.smul_apply, add_comm (φ μ), add_smul, add_sub_cancel_right]

section FiniteDimensional

variable [FiniteDimensional k U]

omit [AddCommGroup X] in
theorem finite_ne_bot (hWi : iSupIndep W) : {μ | W μ ≠ ⊥}.Finite :=
  Submodule.finite_ne_bot_of_iSupIndep hWi

omit [AddCommGroup X] [FiniteDimensional k U] in
theorem isInternal [DecidableEq X] (hWi : iSupIndep W) (hW : ⨆ μ, W μ = ⊤) : DirectSum.IsInternal W :=
  DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top hWi hW

/-- The trace of an endomorphism raising weights by a nonzero `χ` vanishes. -/
theorem trace_eq_zero_of_mem_shift (hWi : iSupIndep W) (hW : ⨆ μ, W μ = ⊤) {χ : X}
    (hχ : χ ≠ 0) {f : Module.End k U} (hf : f ∈ shift W χ) : LinearMap.trace k U f = 0 := by
  classical
  exact LinearMap.trace_eq_zero_of_mapsTo_ne (isInternal hWi hW) (fun μ => μ + χ)
    (fun μ h => hχ (by simpa using h)) (fun μ => mapsTo_of_mem_shift (ν := μ + χ) hf rfl)

/-- The trace of an endomorphism acting by scalars on the weight spaces. -/
theorem trace_eq_finsum_of_isScalarOn (hWi : iSupIndep W) (hW : ⨆ μ, W μ = ⊤) {φ : X → k}
    {t : Module.End k U} (ht : IsScalarOn W φ t) :
    LinearMap.trace k U t = ∑ᶠ μ, (finrank k (W μ) : k) * φ μ := by
  classical
  have hmaps : ∀ μ, MapsTo t (W μ) (W μ) :=
    fun μ => mapsTo_of_mem_shift (ht.mem_shift_zero W) (add_zero μ)
  rw [LinearMap.trace_eq_sum_trace_restrict' (isInternal hWi hW) (finite_ne_bot hWi) hmaps]
  have hsupp : support (fun μ => (finrank k (W μ) : k) * φ μ) ⊆
      ↑(finite_ne_bot hWi).toFinset := by
    intro μ hμ
    rw [Finite.coe_toFinset, mem_ofPred_eq]
    intro hbot
    apply hμ
    have h0 : finrank k (W μ) = 0 := by rw [hbot]; exact finrank_bot k U
    simp [h0]
  rw [finsum_eq_sum_of_support_subset _ hsupp]
  refine Finset.sum_congr rfl fun μ _ => ?_
  have hr : t.restrict (hmaps μ) = φ μ • LinearMap.id := by
    ext u
    exact ht μ u u.2
  rw [hr, map_smul, LinearMap.trace_id, smul_eq_mul, mul_comm]

variable [IsAddTorsionFree X]

/-- Along a nonzero direction, the weight spaces eventually vanish. -/
theorem exists_forall_ge_eq_bot (hWi : iSupIndep W) {α : X} (hα : α ≠ 0) (μ : X) :
    ∃ N : ℕ, ∀ j, N ≤ j → W (μ + j • α) = ⊥ := by
  have hinj : Injective fun j : ℕ => μ + j • α := by
    intro i j hij
    have h : (i : ℤ) • α = (j : ℤ) • α := by
      simpa only [add_right_inj, natCast_zsmul] using hij
    have : HasUniqueDiv X :=
      ⟨fun _ hn a b hab ↦ eq_of_nsmul_eq_nsmul_of_addCommute hn (AddCommute.all a b) hab⟩
    exact Nat.cast_inj.mp (smul_left_injective ℤ hα h)
  have hfin : ((fun j : ℕ => μ + j • α) ⁻¹' {μ | W μ ≠ ⊥}).Finite :=
    (finite_ne_bot hWi).preimage hinj.injOn
  obtain ⟨N, hN⟩ := hfin.bddAbove
  refine ⟨N + 1, fun j hj => ?_⟩
  by_contra h
  have := hN (show j ∈ (fun j : ℕ => μ + j • α) ⁻¹' {μ | W μ ≠ ⊥} from h)
  omega

/-- An endomorphism raising weights by a nonzero `χ` is nilpotent. -/
theorem isNilpotent_of_mem_shift (hWi : iSupIndep W) (hW : ⨆ μ, W μ = ⊤) {χ : X}
    (hχ : χ ≠ 0) {f : Module.End k U} (hf : f ∈ shift W χ) : IsNilpotent f := by
  refine Module.End.isNilpotent_iff_of_finite.mpr fun u => ?_
  have hu : u ∈ ⨆ μ, W μ := by rw [hW]; exact Submodule.mem_top
  induction hu using Submodule.iSup_induction' with
  | mem μ u hu =>
    obtain ⟨N, hN⟩ := exists_forall_ge_eq_bot hWi hχ μ
    refine ⟨N, ?_⟩
    have hpow : ∀ j : ℕ, (f ^ j) u ∈ W (μ + j • χ) := by
      intro j
      induction j with
      | zero => simpa using hu
      | succ j ih =>
        rw [pow_succ', Module.End.mul_apply]
        have h := hf _ _ ih
        rwa [add_assoc, ← succ_nsmul] at h
    have h := hpow N
    rwa [hN N le_rfl, Submodule.mem_bot] at h
  | zero => exact ⟨0, map_zero _⟩
  | add u v _ _ hu hv =>
    obtain ⟨n₁, hn₁⟩ := hu
    obtain ⟨n₂, hn₂⟩ := hv
    refine ⟨max n₁ n₂, ?_⟩
    rw [map_add, Module.End.pow_map_zero_of_le le_sup_left hn₁,
      Module.End.pow_map_zero_of_le le_sup_right hn₂, add_zero]

end FiniteDimensional

end Langlands.LinearAlgebra.WeightGraded
