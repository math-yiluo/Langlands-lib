import Langlands.LinearAlgebra.StableEndomorphismStatements
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/-!
# Proofs for stable endomorphisms of arbitrary complex vector spaces

Proofs of the six statement targets for Renard 2026, Appendix C.II,
Lemma (i)–(iv), and of their aggregate `StableEndomorphismStatement`.
No finite-dimensionality or chain condition is used.
-/

set_option autoImplicit false

namespace Langlands.LinearAlgebra.StableEndomorphism

universe uV uA uB uC

section OneSpace

variable {V : Type uV} [AddCommGroup V] [Module ℂ V]

theorem ker_le_ker_sq (t : Module.End ℂ V) : LinearMap.ker t ≤ LinearMap.ker (t ^ 2) := by
  intro x hx
  rw [LinearMap.mem_ker] at hx ⊢
  rw [pow_two, Module.End.mul_apply, hx, map_zero]

theorem range_sq_le_range (t : Module.End ℂ V) :
    LinearMap.range (t ^ 2) ≤ LinearMap.range t := by
  rintro _ ⟨w, rfl⟩
  exact ⟨t w, by rw [pow_two, Module.End.mul_apply]⟩

/-- Stability reduces to the two nontrivial inclusions. -/
theorem stable_iff_le (t : Module.End ℂ V) :
    Stable t ↔ LinearMap.ker (t ^ 2) ≤ LinearMap.ker t ∧
      LinearMap.range t ≤ LinearMap.range (t ^ 2) :=
  ⟨fun h => ⟨h.1.ge, h.2.le⟩,
    fun h => ⟨le_antisymm (ker_le_ker_sq t) h.1, le_antisymm h.2 (range_sq_le_range t)⟩⟩

/-- The kernel half of stability, in elementwise form. -/
theorem Stable.apply_eq_zero {t : Module.End ℂ V} (h : Stable t) {x : V}
    (hx : t (t x) = 0) : t x = 0 := by
  have hx' : x ∈ LinearMap.ker (t ^ 2) := by
    rw [LinearMap.mem_ker, pow_two, Module.End.mul_apply]
    exact hx
  rw [← h.1, LinearMap.mem_ker] at hx'
  exact hx'

/-- The range half of stability, in elementwise form. -/
theorem Stable.exists_apply_sq {t : Module.End ℂ V} (h : Stable t) (x : V) :
    ∃ y, t (t y) = t x := by
  have hx : t x ∈ LinearMap.range (t ^ 2) := h.2 ▸ LinearMap.mem_range_self t x
  obtain ⟨y, hy⟩ := hx
  exact ⟨y, by rw [← hy, pow_two, Module.End.mul_apply]⟩

/-- For a stable endomorphism, every vector is a kernel vector plus a vector in the
range of the square. -/
theorem Stable.exists_decomp_sq {t : Module.End ℂ V} (h : Stable t) (x : V) :
    ∃ k u, t k = 0 ∧ x = k + t (t u) := by
  obtain ⟨w, hw⟩ := h.exists_apply_sq x
  obtain ⟨u, hu⟩ := h.exists_apply_sq w
  refine ⟨x - t w, u, ?_, ?_⟩
  · rw [map_sub, hw, sub_self]
  · rw [hu, sub_add_cancel]

/-- Lemma (i): stability is equivalent to complementarity of kernel and range. -/
theorem stable_iff_isCompl (t : Module.End ℂ V) :
    Stable t ↔ IsCompl (LinearMap.ker t) (LinearMap.range t) := by
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · rw [Submodule.disjoint_def]
      rintro x hx ⟨w, rfl⟩
      exact h.apply_eq_zero hx
    · rw [Submodule.codisjoint_iff_exists_add_eq]
      intro x
      obtain ⟨w, hw⟩ := h.exists_apply_sq x
      refine ⟨x - t w, t w, ?_, LinearMap.mem_range_self t w, sub_add_cancel x (t w)⟩
      rw [LinearMap.mem_ker, map_sub, hw, sub_self]
  · intro h
    rw [stable_iff_le]
    refine ⟨?_, ?_⟩
    · intro x hx
      rw [LinearMap.mem_ker, pow_two, Module.End.mul_apply] at hx
      exact Submodule.disjoint_def.mp h.disjoint (t x) hx (LinearMap.mem_range_self t x)
    · rintro _ ⟨w, rfl⟩
      obtain ⟨k, y, hk, ⟨z, rfl⟩, rfl⟩ :=
        Submodule.codisjoint_iff_exists_add_eq.mp h.codisjoint w
      refine ⟨z, ?_⟩
      rw [LinearMap.mem_ker] at hk
      rw [pow_two, Module.End.mul_apply, map_add, hk, zero_add]

end OneSpace

section Rows

variable {A : Type uA} {B : Type uB} {C : Type uC}
  [AddCommGroup A] [Module ℂ A]
  [AddCommGroup B] [Module ℂ B]
  [AddCommGroup C] [Module ℂ C]

/-- Lemma (ii): transfer of stability to the cokernel end of an exact row
`A → B → C → 0`. -/
theorem stable_of_rightExact (phi : A →ₗ[ℂ] B) (psi : B →ₗ[ℂ] C)
    (fA : Module.End ℂ A) (fB : Module.End ℂ B) (fC : Module.End ℂ C)
    (hexact : LinearMap.range phi = LinearMap.ker psi)
    (hsurj : Function.Surjective psi)
    (hphi : fB.comp phi = phi.comp fA) (hpsi : fC.comp psi = psi.comp fB)
    (hA : Stable fA) (hB : Stable fB) : Stable fC := by
  have hphi' : ∀ a, fB (phi a) = phi (fA a) := fun a => LinearMap.congr_fun hphi a
  have hpsi' : ∀ b, fC (psi b) = psi (fB b) := fun b => LinearMap.congr_fun hpsi b
  have hpsiphi : ∀ a, psi (phi a) = 0 := fun a => by
    rw [← LinearMap.mem_ker, ← hexact]
    exact LinearMap.mem_range_self phi a
  rw [stable_iff_le]
  refine ⟨?_, ?_⟩
  · intro c hc
    rw [LinearMap.mem_ker, pow_two, Module.End.mul_apply] at hc
    rw [LinearMap.mem_ker]
    obtain ⟨b, rfl⟩ := hsurj c
    rw [hpsi', hpsi'] at hc
    have hb : fB (fB b) ∈ LinearMap.range phi := by
      rw [hexact]
      exact hc
    obtain ⟨a, ha⟩ := hb
    obtain ⟨k, u, hk, rfl⟩ := hA.exists_decomp_sq a
    -- `phi k` lies in `ker fB ∩ range fB`, hence vanishes.
    have hphik : phi k = fB (fB (b - phi u)) := by
      rw [map_sub, map_sub, hphi', hphi', ← ha, map_add, add_sub_cancel_right]
    have hphik0 : phi k = 0 := by
      rw [hphik]
      apply hB.apply_eq_zero
      rw [← hphik, hphi', hk, map_zero]
    have hbu : fB (b - phi u) = 0 := by
      apply hB.apply_eq_zero
      rw [← hphik, hphik0]
    rw [map_sub, sub_eq_zero, hphi'] at hbu
    rw [hpsi', hbu, hpsiphi]
  · rintro _ ⟨c, rfl⟩
    obtain ⟨b, rfl⟩ := hsurj c
    obtain ⟨y, hy⟩ := hB.exists_apply_sq b
    refine ⟨psi y, ?_⟩
    rw [pow_two, Module.End.mul_apply, hpsi', hpsi', hpsi', hy]

/-- Lemma (iii): transfer of stability to the kernel end of an exact row
`0 → A → B → C`. -/
theorem stable_of_leftExact (phi : A →ₗ[ℂ] B) (psi : B →ₗ[ℂ] C)
    (fA : Module.End ℂ A) (fB : Module.End ℂ B) (fC : Module.End ℂ C)
    (hinj : Function.Injective phi)
    (hexact : LinearMap.range phi = LinearMap.ker psi)
    (hphi : fB.comp phi = phi.comp fA) (hpsi : fC.comp psi = psi.comp fB)
    (hB : Stable fB) (hC : Stable fC) : Stable fA := by
  have hphi' : ∀ a, fB (phi a) = phi (fA a) := fun a => LinearMap.congr_fun hphi a
  have hpsi' : ∀ b, fC (psi b) = psi (fB b) := fun b => LinearMap.congr_fun hpsi b
  have hpsiphi : ∀ a, psi (phi a) = 0 := fun a => by
    rw [← LinearMap.mem_ker, ← hexact]
    exact LinearMap.mem_range_self phi a
  rw [stable_iff_le]
  refine ⟨?_, ?_⟩
  · intro a ha
    rw [LinearMap.mem_ker, pow_two, Module.End.mul_apply] at ha
    rw [LinearMap.mem_ker]
    apply hinj
    rw [map_zero, ← hphi']
    apply hB.apply_eq_zero
    rw [hphi', hphi', ha, map_zero]
  · rintro _ ⟨a, rfl⟩
    obtain ⟨k, b, hk, hdecomp⟩ := hB.exists_decomp_sq (phi a)
    -- `psi k` lies in `ker fC` and equals `-fC (fC (psi b))`.
    have hsum : psi k + fC (fC (psi b)) = 0 := by
      rw [hpsi', hpsi', ← map_add, ← hdecomp, hpsiphi]
    have hfCk : fC (psi k) = 0 := by rw [hpsi', hk, map_zero]
    have hb3 : fC (fC (fC (psi b))) = 0 := by
      rw [← neg_eq_of_add_eq_zero_right hsum, map_neg, hfCk, neg_zero]
    have hb1 : fC (psi b) = 0 := hC.apply_eq_zero (hC.apply_eq_zero hb3)
    rw [hpsi'] at hb1
    have hb : fB b ∈ LinearMap.range phi := by
      rw [hexact]
      exact hb1
    obtain ⟨a₁, ha₁⟩ := hb
    have hk' : k = phi (a - fA a₁) := by
      rw [map_sub, ← hphi', ha₁, hdecomp, add_sub_cancel_right]
    have hfA : fA (a - fA a₁) = 0 := by
      apply hinj
      rw [map_zero, ← hphi', ← hk', hk]
    refine ⟨a₁, ?_⟩
    rw [map_sub, sub_eq_zero] at hfA
    rw [pow_two, Module.End.mul_apply, hfA]

end Rows

section Chains

variable {V : Type uV} [AddCommGroup V] [Module ℂ V]

/-- Monotonicity of the kernel chain and antitonicity of the range chain. -/
theorem ker_pow_monotone (t : Module.End ℂ V) :
    Monotone (fun k : ℕ => LinearMap.ker (t ^ k)) :=
  (LinearMap.iterateKer t).monotone

theorem range_pow_antitone (t : Module.End ℂ V) :
    Antitone (fun k : ℕ => LinearMap.range (t ^ k)) :=
  fun _ _ h => (LinearMap.iterateRange t).monotone h

/-- An adjacent kernel equality propagates to every later exponent. -/
theorem ker_pow_eq_of_le {t : Module.End ℂ V} {k : ℕ}
    (h : LinearMap.ker (t ^ k) = LinearMap.ker (t ^ (k + 1))) {m : ℕ} (hm : k ≤ m) :
    LinearMap.ker (t ^ m) = LinearMap.ker (t ^ k) := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hm
  exact (Module.End.ker_pow_constant h j).symm

/-- An adjacent range equality propagates to every later exponent. -/
theorem range_pow_eq_of_le {t : Module.End ℂ V} {k : ℕ}
    (h : LinearMap.range (t ^ k) = LinearMap.range (t ^ (k + 1))) {m : ℕ} (hm : k ≤ m) :
    LinearMap.range (t ^ m) = LinearMap.range (t ^ k) := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hm
  induction j with
  | zero => rfl
  | succ j ih =>
    have hsucc : ∀ n : ℕ, LinearMap.range (t ^ (n + 1)) = (LinearMap.range (t ^ n)).map t :=
      fun n => LinearMap.iterateRange_succ
    rw [← add_assoc, hsucc, ih (Nat.le_add_right k j), ← hsucc, ← h]

/-- Eventual stability gives a common exponent from which both chains are constant. -/
theorem EventuallyStable.exists_constant {t : Module.End ℂ V} (h : EventuallyStable t) :
    ∃ M : ℕ, (∀ m, M ≤ m → LinearMap.ker (t ^ m) = LinearMap.ker (t ^ M)) ∧
      (∀ m, M ≤ m → LinearMap.range (t ^ m) = LinearMap.range (t ^ M)) := by
  obtain ⟨n, hn, hK, hR⟩ := h
  rw [← pow_mul] at hK hR
  have hle : n + 1 ≤ n * 2 := by omega
  have hK1 : LinearMap.ker (t ^ n) = LinearMap.ker (t ^ (n + 1)) :=
    le_antisymm (ker_pow_monotone t (Nat.le_succ n))
      (hK ▸ ker_pow_monotone t hle)
  have hR1 : LinearMap.range (t ^ n) = LinearMap.range (t ^ (n + 1)) :=
    le_antisymm (hR ▸ range_pow_antitone t hle)
      (range_pow_antitone t (Nat.le_succ n))
  exact ⟨n, fun m hm => ker_pow_eq_of_le hK1 hm, fun m hm => range_pow_eq_of_le hR1 hm⟩

/-- Under eventual stability, an adjacent kernel equality gives the adjacent range
equality at the same exponent. -/
theorem range_eq_of_ker_eq {t : Module.End ℂ V} (h : EventuallyStable t) {k : ℕ}
    (hk : LinearMap.ker (t ^ k) = LinearMap.ker (t ^ (k + 1))) :
    LinearMap.range (t ^ k) = LinearMap.range (t ^ (k + 1)) := by
  obtain ⟨M, -, hR⟩ := h.exists_constant
  refine le_antisymm ?_ (range_pow_antitone t (Nat.le_succ k))
  rintro _ ⟨v, rfl⟩
  have hv : (t ^ (k + M)) v ∈ LinearMap.range (t ^ (k + M + 1)) := by
    rw [hR (k + M + 1) (by omega), ← hR (k + M) (by omega)]
    exact LinearMap.mem_range_self _ v
  obtain ⟨w, hw⟩ := hv
  have hvw : v - t w ∈ LinearMap.ker (t ^ (k + M)) := by
    rw [LinearMap.mem_ker, map_sub, ← Module.End.mul_apply, ← pow_succ, hw, sub_self]
  rw [ker_pow_eq_of_le hk (Nat.le_add_right k M), LinearMap.mem_ker, map_sub,
    sub_eq_zero] at hvw
  exact ⟨w, by rw [hvw, pow_succ, Module.End.mul_apply]⟩

/-- Under eventual stability, an adjacent range equality gives the adjacent kernel
equality at the same exponent. -/
theorem ker_eq_of_range_eq {t : Module.End ℂ V} (h : EventuallyStable t) {k : ℕ}
    (hk : LinearMap.range (t ^ k) = LinearMap.range (t ^ (k + 1))) :
    LinearMap.ker (t ^ k) = LinearMap.ker (t ^ (k + 1)) := by
  obtain ⟨M, hK, -⟩ := h.exists_constant
  refine le_antisymm (ker_pow_monotone t (Nat.le_succ k)) ?_
  intro v hv
  rw [LinearMap.mem_ker] at hv ⊢
  have hkv : (t ^ k) v ∈ LinearMap.range (t ^ (k + M)) := by
    rw [range_pow_eq_of_le hk (Nat.le_add_right k M)]
    exact LinearMap.mem_range_self _ v
  obtain ⟨w, hw⟩ := hkv
  have hw1 : w ∈ LinearMap.ker (t ^ (k + M + 1)) := by
    rw [LinearMap.mem_ker, pow_succ', Module.End.mul_apply, hw, ← Module.End.mul_apply,
      ← pow_succ', hv]
  rw [hK (k + M + 1) (by omega), ← hK (k + M) (by omega), LinearMap.mem_ker, hw] at hw1
  exact hw1

end Chains

/-- Lemma (i), as the published closed statement. -/
theorem stableIffIsCompl : StableIffIsComplStatement.{uV} :=
  fun _ _ _ t => stable_iff_isCompl t

/-- Lemma (ii), as the published closed statement. -/
theorem stableOfRightExact : StableOfRightExactStatement.{uA, uB, uC} :=
  fun _ _ _ _ _ _ _ _ _ phi psi fA fB fC hexact hsurj hphi hpsi hA hB =>
    stable_of_rightExact phi psi fA fB fC hexact hsurj hphi hpsi hA hB

/-- Lemma (iii), as the published closed statement. -/
theorem stableOfLeftExact : StableOfLeftExactStatement.{uA, uB, uC} :=
  fun _ _ _ _ _ _ _ _ _ phi psi fA fB fC hinj hexact hphi hpsi hB hC =>
    stable_of_leftExact phi psi fA fB fC hinj hexact hphi hpsi hB hC

/-- Monotonicity clause of Lemma (iv), as the published closed statement. -/
theorem powerKernelRangeMonotonicity : PowerKernelRangeMonotonicityStatement.{uV} :=
  fun _ _ _ t => ⟨ker_pow_monotone t, range_pow_antitone t⟩

/-- Adjacent-equality clause of Lemma (iv), as the published closed statement. -/
theorem adjacentStabilization : AdjacentStabilizationStatement.{uV} := by
  intro V _ _ t h k
  refine ⟨⟨range_eq_of_ker_eq h, ker_eq_of_range_eq h⟩, ?_⟩
  intro hor m hm
  have hK : LinearMap.ker (t ^ k) = LinearMap.ker (t ^ (k + 1)) :=
    hor.elim id (ker_eq_of_range_eq h)
  exact ⟨ker_pow_eq_of_le hK hm, range_pow_eq_of_le (range_eq_of_ker_eq h hK) hm⟩

/-- Common first stabilization index of Lemma (iv), as the published closed statement. -/
theorem firstStabilizationIndex : FirstStabilizationIndexStatement.{uV} := by
  classical
  intro V _ _ t h
  have hex : ∃ k : ℕ, LinearMap.ker (t ^ k) = LinearMap.ker (t ^ (k + 1)) := by
    obtain ⟨M, hK, -⟩ := h.exists_constant
    exact ⟨M, (hK (M + 1) (Nat.le_succ M)).symm⟩
  refine ⟨Nat.find hex, ?_, ?_⟩
  · intro m hm
    have hK := Nat.find_spec hex
    exact ⟨ker_pow_eq_of_le hK hm, range_pow_eq_of_le (range_eq_of_ker_eq h hK) hm⟩
  · intro j hj
    have hKj : LinearMap.ker (t ^ j) ≠ LinearMap.ker (t ^ (j + 1)) := Nat.find_min hex hj
    exact ⟨hKj, fun hRj => hKj (ker_eq_of_range_eq h hRj)⟩

/-- Renard 2026, Appendix C.II, Lemma (i)–(iv): the complete published aggregate. -/
theorem stableEndomorphism : StableEndomorphismStatement.{uV, uA, uB, uC} :=
  ⟨stableIffIsCompl, stableOfRightExact, stableOfLeftExact, powerKernelRangeMonotonicity,
    adjacentStabilization, firstStabilizationIndex⟩

end Langlands.LinearAlgebra.StableEndomorphism
