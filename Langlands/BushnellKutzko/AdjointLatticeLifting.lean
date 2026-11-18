import Langlands.BushnellKutzko.AdjointCentralizer

/-! # Lifting at a specified adjoint lattice depth -/

open ValuativeRel

noncomputable section

namespace Langlands.BushnellKutzko

universe uF uE uV

variable {F : Type uF} [Field F] [ValuativeRel F]
  {V : Type uV} [AddCommGroup V] [Module F V]
  (𝓛 : LatticeChain 𝒪[F] F V) (b : Module.End F V)

local notation "A" => Module.End F V
local notation "P" => 𝓛.endFiltration
local notation "Q" => centralizerLattice 𝓛 b
local notation "N" => adjointLattice 𝓛 b
local notation "a" => adjointMap F b

/-- The adjoint preimage at depth `m` of filtration step `m+k`. -/
def mixedAdjointLattice (m k : ℤ) : Submodule 𝒪[F] A :=
  P m ⊓ (P (m + k)).comap (adjointMap 𝒪[F] b)

local notation "M" => mixedAdjointLattice 𝓛 b

@[simp]
theorem mixedAdjointLattice_zero (k : ℤ) : M 0 k = N k := by
  simp [mixedAdjointLattice, adjointLattice]

theorem mem_mixedAdjointLattice_iff {m k : ℤ} {x : A} :
    x ∈ M m k ↔ x ∈ P m ∧ a x ∈ P (m + k) := Iff.rfl

theorem mixedAdjointLattice_antitone (m : ℤ) : Antitone (M m) := by
  intro j k hjk x hx
  obtain ⟨hx, hax⟩ := (mem_mixedAdjointLattice_iff 𝓛 b).mp hx
  exact (mem_mixedAdjointLattice_iff 𝓛 b).mpr
    ⟨hx, 𝓛.endFiltration_antitone (add_le_add_right hjk m) hax⟩

theorem centralizerLattice_le_mixedAdjointLattice (m k : ℤ) : Q m ≤ M m k := by
  intro x hx
  obtain ⟨hp, ha⟩ := (mem_centralizerLattice_iff 𝓛).mp hx
  exact (mem_mixedAdjointLattice_iff 𝓛 b).mpr ⟨hp, ha ▸ (P (m + k)).zero_mem⟩

omit [ValuativeRel F] in
theorem adjointMap_mul_left_of_ker {q : A} (hq : a q = 0) (x : A) :
    a (q * x) = q * a x := by
  change b * q - q * b = 0 at hq
  change b * (q * x) - (q * x) * b = q * (b * x - x * b)
  rw [← mul_assoc b q x, sub_eq_zero.mp hq, mul_assoc, mul_assoc, mul_sub]

private theorem centralizerLattice_mul_le (m n : ℤ) :
    Q m * Q n ≤ Q (m + n) := by
  apply Submodule.mul_le.mpr
  intro q hq x hx
  obtain ⟨hq, hqa⟩ := (mem_centralizerLattice_iff 𝓛).mp hq
  obtain ⟨hx, hxa⟩ := (mem_centralizerLattice_iff 𝓛).mp hx
  exact (mem_centralizerLattice_iff 𝓛).mpr
    ⟨𝓛.mul_mem_endFiltration hq hx, by rw [adjointMap_mul_left_of_ker b hqa, hxa, mul_zero]⟩

private theorem centralizerLattice_mul_endFiltration_le (m n : ℤ) :
    Q m * P n ≤ P (m + n) :=
  Submodule.mul_le.mpr fun _ hq _ hx => 𝓛.mul_mem_endFiltration hq.1 hx

private theorem centralizerLattice_mul_mixedAdjointLattice_le (m n k : ℤ) :
    Q m * M n k ≤ M (m + n) k := by
  apply Submodule.mul_le.mpr
  intro q hq x hx
  obtain ⟨hq, hqa⟩ := (mem_centralizerLattice_iff 𝓛).mp hq
  obtain ⟨hx, hxa⟩ := (mem_mixedAdjointLattice_iff 𝓛 b).mp hx
  refine ⟨𝓛.mul_mem_endFiltration hq hx, ?_⟩
  change a (q * x) ∈ P (m + n + k)
  rw [adjointMap_mul_left_of_ker b hqa, add_assoc]
  exact 𝓛.mul_mem_endFiltration hq hxa

private theorem submodule_mul_eq_of_inverse {S S' T U : Submodule 𝒪[F] A}
    (h : S * T ≤ U) (hinv : S' * U ≤ T) (hone : 1 ∈ S * S') : S * T = U := by
  refine h.antisymm fun x hx => ?_
  have hmem : 1 * x ∈ (S * S') * U := Submodule.mul_mem_mul hone hx
  rw [one_mul, mul_assoc] at hmem
  exact mul_le_mul_right hinv S hmem

/-- Multiplying a filtration step by the relative step adds the two depths. -/
theorem centralizerLattice_mul_endFiltration
    (hinv : ∀ m : ℤ, (1 : A) ∈ Q m * Q (-m)) (m n : ℤ) :
    Q m * P n = P (m + n) := by
  refine submodule_mul_eq_of_inverse (centralizerLattice_mul_endFiltration_le 𝓛 b m n) ?_ (hinv m)
  simpa only [← add_assoc, neg_add_cancel, zero_add] using
    centralizerLattice_mul_endFiltration_le 𝓛 b (-m) (m + n)

/-- The same transport formula holds for the mixed adjoint preimages. -/
theorem centralizerLattice_mul_mixedAdjointLattice
    (hinv : ∀ m : ℤ, (1 : A) ∈ Q m * Q (-m)) (m n k : ℤ) :
    Q m * M n k = M (m + n) k := by
  refine submodule_mul_eq_of_inverse
    (centralizerLattice_mul_mixedAdjointLattice_le 𝓛 b m n k) ?_ (hinv m)
  simpa only [← add_assoc, neg_add_cancel, zero_add] using
    centralizerLattice_mul_mixedAdjointLattice_le 𝓛 b (-m) (m + n) k

section LocalField

variable [TopologicalSpace F] [IsNonarchimedeanLocalField F]

/-- If the defining order condition held at depth zero, the commutator would vanish. -/
theorem adjointMap_eq_zero_of_order_le
    (hinv : ∀ m : ℤ, (1 : A) ∈ Q m * Q (-m))
    {c : F} (hc : c ≠ 0) (hclear : ∀ x : A, ∃ t : ℕ, c ^ t • x ∈ P 0)
    (hperiod : 𝓂[F] • P 0 = P (𝓛.period : ℤ))
    (h : P 0 ≤ Q 0 ⊔ P 1) : a = 0 := by
  have hstep (j : ℕ) : P j ≤ Q 0 ⊔ P (j + 1) := by
    calc
      P j = Q j * P 0 := by
        simpa using (centralizerLattice_mul_endFiltration 𝓛 b hinv j 0).symm
      _ ≤ Q j * (Q 0 ⊔ P 1) := mul_le_mul_right h _
      _ ≤ Q 0 ⊔ P (j + 1) := by
        rw [Submodule.mul_sup, centralizerLattice_mul_endFiltration 𝓛 b hinv]
        apply sup_le_sup_right
        have hq : Q (j : ℤ) ≤ Q 0 :=
          inf_le_inf_right _ (𝓛.endFiltration_antitone (Int.natCast_nonneg j))
        simpa only [add_zero] using (centralizerLattice_mul_le 𝓛 b j 0).trans hq
  have hiter (j : ℕ) : P 0 ≤ Q 0 ⊔ P j := by
    induction j with
    | zero => simpa only [Nat.cast_zero] using (le_sup_right : P 0 ≤ Q 0 ⊔ P 0)
    | succ j ih =>
      have hj := sup_le_sup_left (hstep j) (Q 0)
      exact ih.trans (by simpa only [Nat.cast_succ, ← sup_assoc, sup_idem] using hj)
  have hjac : 𝓂[F] ≤ (⊥ : Ideal 𝒪[F]).jacobson := by
    rw [Ideal.jacobson_bot, jacobson_integer_eq_maximalIdeal]
  have hle : P 0 ≤ Q 0 := Submodule.le_of_le_smul_of_le_jacobson_bot
    𝓛.endFiltration_zero_fg hjac (hperiod.symm ▸ hiter 𝓛.period)
  apply LinearMap.ext
  intro x
  obtain ⟨t, ht⟩ := hclear x
  have hz := (mem_centralizerLattice_iff 𝓛).mp (hle ht) |>.2
  rw [map_smul, smul_eq_zero_iff_right (pow_ne_zero _ hc)] at hz
  exact hz

/-- A nonscalar generator gives a nonempty critical-index set. -/
theorem criticalIndexSet_nonempty_of_inverse {E : Type uE} [Field E] [Algebra F E]
    [Module E V] [IsScalarTower F E V] (β : E)
    (hnscalar : ¬ ∃ c : F, algebraMap F E c = β)
    (hinv : ∀ m : ℤ, (1 : A) ∈ centralizerLattice 𝓛 (subfieldEmbedding F E V β) m *
      centralizerLattice 𝓛 (subfieldEmbedding F E V β) (-m))
    {ϖ : 𝒪[F]} (hϖ : Irreducible ϖ) (hclear : ∀ x : A, ∃ t : ℕ, (ϖ : F) ^ t • x ∈ P 0)
    (hperiod : 𝓂[F] • P 0 = P (𝓛.period : ℤ)) :
    (criticalIndexSet 𝓛 (subfieldEmbedding F E V β)).Nonempty := by
  classical
  let b' := subfieldEmbedding F E V β
  obtain ⟨n, hn⟩ := hclear b'
  have hb : b' ∈ P (-(n : ℤ) * 𝓛.period) := by
    apply (𝓛.uniformizer_pow_end_mem_iff hϖ n _ b').mp
    simpa only [neg_mul, neg_add_cancel] using hn
  refine ⟨-(n : ℤ) * 𝓛.period, fun h => ?_⟩
  have hN : P 0 ≤ adjointLattice 𝓛 b' (-(n : ℤ) * 𝓛.period) := by
    intro x hx
    refine ⟨hx, ?_⟩
    change b' * x - x * b' ∈ P (-(n : ℤ) * 𝓛.period)
    exact sub_mem (by simpa using 𝓛.mul_mem_endFiltration hb hx)
      (by simpa using 𝓛.mul_mem_endFiltration hx hb)
  have hne : (ϖ : F) ≠ 0 := fun h => hϖ.ne_zero (Subtype.ext h)
  have ha := adjointMap_eq_zero_of_order_le 𝓛 b' hinv hne hclear hperiod (hN.trans h)
  have hbcenter : b' ∈ Subalgebra.center F A := Subalgebra.mem_center_iff.mpr fun x => by
    have hzero := LinearMap.congr_fun ha x
    exact (sub_eq_zero.mp hzero).symm
  rw [Algebra.IsCentral.center_eq_bot] at hbcenter
  exact adjoin_subfieldEmbedding_ne_bot 𝓛 β hnscalar
    (le_bot_iff.mp (Algebra.adjoin_le fun x hx => Set.mem_singleton_iff.mp hx ▸ hbcenter))

end LocalField

/-- At a depth above the critical set, integral preimages split off a centralizer element. -/
theorem adjointLattice_succ_le_of_not_mem {k : ℤ}
    (hk : k + 1 ∉ criticalIndexSet 𝓛 b) : N (k + 1) ≤ Q 0 ⊔ M 1 k := by
  have h : N (k + 1) ≤ Q 0 ⊔ P 1 := not_not.mp hk
  intro x hx
  obtain ⟨q, hq, z, hz, rfl⟩ := Submodule.mem_sup.mp (h hx)
  have hzero := (mem_centralizerLattice_iff 𝓛).mp hq |>.2
  have ha := (mem_adjointLattice_iff 𝓛).mp hx |>.2
  rw [map_add, hzero, zero_add] at ha
  have hzm : z ∈ M 1 k :=
    (mem_mixedAdjointLattice_iff 𝓛 b).mpr ⟨hz, by simpa only [add_comm 1 k] using ha⟩
  exact Submodule.mem_sup.mpr ⟨q, hq, z, hzm, rfl⟩

private theorem exists_mixedAdjointLattice_succ_lift
    (hinv : ∀ m : ℤ, (1 : A) ∈ Q m * Q (-m)) {m k : ℤ}
    (hk : k + 1 ∉ criticalIndexSet 𝓛 b) {x : A} (hx : x ∈ M m (k + 1)) :
    ∃ z ∈ M (m + 1) k, a z = a x := by
  have hmul : M m (k + 1) = Q m * N (k + 1) := by
    simpa using (centralizerLattice_mul_mixedAdjointLattice 𝓛 b hinv m 0 (k + 1)).symm
  have hle : M m (k + 1) ≤ Q m ⊔ M (m + 1) k := by
    rw [hmul]
    refine (mul_le_mul_right (adjointLattice_succ_le_of_not_mem 𝓛 b hk) (Q m)).trans ?_
    rw [Submodule.mul_sup]
    exact sup_le_sup (by simpa using centralizerLattice_mul_le 𝓛 b m 0)
      (centralizerLattice_mul_mixedAdjointLattice_le 𝓛 b m 1 k)
  obtain ⟨q, hq, z, hz, rfl⟩ := Submodule.mem_sup.mp (hle hx)
  refine ⟨z, hz, ?_⟩
  rw [map_add, (mem_centralizerLattice_iff 𝓛).mp hq |>.2, zero_add]

private theorem exists_mixedAdjointLattice_iterated_lift
    (hinv : ∀ m : ℤ, (1 : A) ∈ Q m * Q (-m)) {k : ℤ}
    (hk : ∀ j > k, j ∉ criticalIndexSet 𝓛 b) (d : ℕ)
    (m : ℤ) {x : A} (hx : x ∈ M m (k + d)) :
    ∃ z ∈ M (m + d) k, a z = a x := by
  induction d generalizing m x with
  | zero => exact ⟨x, by simpa using hx, rfl⟩
  | succ d ih =>
    have hdepth : k + (d : ℤ) + 1 > k := by omega
    have hx' : x ∈ M m (k + (d : ℤ) + 1) := by
      simpa only [Nat.cast_succ, add_assoc] using hx
    obtain ⟨y, hy, heq⟩ :=
      exists_mixedAdjointLattice_succ_lift 𝓛 b hinv (hk _ hdepth) hx'
    obtain ⟨z, hz, heq'⟩ := ih (m + 1) hy
    refine ⟨z, ?_, heq'.trans heq⟩
    simpa only [Nat.cast_succ, ← add_assoc, add_right_comm m 1 (d : ℤ)] using hz

section LocalField

variable [TopologicalSpace F] [IsNonarchimedeanLocalField F] {ϖ : 𝒪[F]}

/-- At and above the critical depth, a global commutator lift can be placed at the
prescribed lattice depth. -/
theorem exists_mixedAdjointLattice_lift
    (hinv : ∀ m : ℤ, (1 : A) ∈ Q m * Q (-m)) (hϖ : Irreducible ϖ)
    (hclear : ∀ (x : A) (m : ℤ), ∃ t : ℕ, (ϖ : F) ^ t • x ∈ P m)
    {m k : ℤ} (hk : ∀ j > k, j ∉ criticalIndexSet 𝓛 b)
    {y : A} (hy : y ∈ P (m + k)) (ha : y ∈ (a).range) :
    ∃ z ∈ M m k, a z = y := by
  obtain ⟨x, rfl⟩ := ha
  obtain ⟨t, ht⟩ := hclear x m
  let d := t * 𝓛.period
  have hd : (d : ℤ) = (t : ℤ) * 𝓛.period := Nat.cast_mul _ _
  have hx : (ϖ : F) ^ t • x ∈ M m (k + d) := by
    refine ⟨ht, ?_⟩
    change a ((ϖ : F) ^ t • x) ∈ P (m + (k + d))
    rw [map_smul, ← add_assoc, hd]
    exact (𝓛.uniformizer_pow_end_mem_iff hϖ t (m + k) _).mpr hy
  obtain ⟨z, hz, heq⟩ := exists_mixedAdjointLattice_iterated_lift 𝓛 b hinv hk d m hx
  let u := (ϖ : F) ^ t
  let w := u⁻¹ • z
  have hu : u ≠ 0 := pow_ne_zero _ fun h => hϖ.ne_zero (Subtype.ext h)
  have hw : u • w = z := smul_inv_smul₀ hu z
  refine ⟨w, ⟨?_, ?_⟩, ?_⟩
  · apply (𝓛.uniformizer_pow_end_mem_iff hϖ t m w).mp
    rw [show (ϖ : F) ^ t • w = z from hw, ← hd]
    exact hz.1
  · change a w ∈ P (m + k)
    apply (𝓛.uniformizer_pow_end_mem_iff hϖ t (m + k) (a w)).mp
    rw [← map_smul, show (ϖ : F) ^ t • w = z from hw, ← hd, add_right_comm]
    exact hz.2
  · apply (smul_right_injective A hu)
    change u • a w = u • a x
    rw [← map_smul, hw, heq, map_smul]

end LocalField

end Langlands.BushnellKutzko
