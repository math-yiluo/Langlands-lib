import Mathlib.RingTheory.AdicCompletion.Noetherian
import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
import Langlands.Algebra.CompleteLocalIdealCofinalityStatement

/-! # Adic cofinality of a separated descending sequence of local ideals: proof -/

universe u

namespace Langlands.Algebra

namespace CompleteLocalIdealCofinality

open IsLocalRing

variable {R : Type*} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]

/-- The quotient of a Noetherian local ring by a positive power of its maximal ideal
is Artinian. -/
theorem isArtinianRing_quotient_maximalIdeal_pow {k : ℕ} (hk : 0 < k) :
    IsArtinianRing (R ⧸ maximalIdeal R ^ k) := by
  refine IsLocalRing.quotient_artinian_of_mem_minimalPrimes_of_isLocalRing _ ?_
  show Minimal (fun q : Ideal R ↦ q.IsPrime ∧ maximalIdeal R ^ k ≤ q) (maximalIdeal R)
  refine ⟨⟨inferInstance, Ideal.pow_le_self hk.ne'⟩, fun q hq _ ↦ ?_⟩
  have := hq.1
  exact Ideal.IsPrime.le_of_pow_le hq.2

/-- The ideals `J n ⊔ m ^ k` of a decreasing sequence stabilize, for each fixed `k`. -/
theorem exists_sup_pow_stable (J : ℕ → Ideal R) (hJ : Antitone J) (k : ℕ) :
    ∃ N, ∀ n, N ≤ n → J n ⊔ maximalIdeal R ^ k = J N ⊔ maximalIdeal R ^ k := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · exact ⟨0, fun n _ ↦ by simp⟩
  have := isArtinianRing_quotient_maximalIdeal_pow (R := R) hk
  let f : ℕ →o (Ideal (R ⧸ maximalIdeal R ^ k))ᵒᵈ :=
    ⟨fun n ↦ OrderDual.toDual ((J n).map (Ideal.Quotient.mk _)),
      fun i j h ↦ Ideal.map_mono (hJ h)⟩
  obtain ⟨N, hN⟩ := IsArtinian.monotone_stabilizes f
  refine ⟨N, fun n hn ↦ ?_⟩
  have h : (J N).map (Ideal.Quotient.mk (maximalIdeal R ^ k)) =
      (J n).map (Ideal.Quotient.mk (maximalIdeal R ^ k)) := hN n hn
  have h' := congrArg (Ideal.comap (Ideal.Quotient.mk (maximalIdeal R ^ k))) h
  rwa [Ideal.comap_map_of_surjective' _ Ideal.Quotient.mk_surjective,
    Ideal.comap_map_of_surjective' _ Ideal.Quotient.mk_surjective, Ideal.mk_ker, eq_comm] at h'

/-- Krull's intersection theorem for the quotient `R ⧸ I`: every ideal of a Noetherian
local ring is closed in the adic topology of the maximal ideal. -/
theorem mem_of_forall_mem_sup_pow (I : Ideal R) {y : R}
    (h : ∀ k, y ∈ I ⊔ maximalIdeal R ^ k) : y ∈ I := by
  rw [← Ideal.Quotient.eq_zero_iff_mem]
  refine IsHausdorff.haus' (I := maximalIdeal R) _ fun k ↦ ?_
  obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp (h k)
  rw [SModEq.zero, map_add, Ideal.Quotient.eq_zero_iff_mem.mpr ha, zero_add]
  have hb' : Ideal.Quotient.mk I b = b • (1 : R ⧸ I) := by
    rw [Algebra.smul_def, mul_one, Ideal.Quotient.algebraMap_eq]
  rw [hb']
  exact Submodule.smul_mem_smul hb Submodule.mem_top

end CompleteLocalIdealCofinality

open IsLocalRing CompleteLocalIdealCofinality in
/-- **Adic cofinality.** In a complete Noetherian local ring, a decreasing sequence of
ideals with zero intersection is eventually contained in every power of the maximal
ideal. -/
theorem completeLocalIdealCofinality : CompleteLocalIdealCofinalityStatement.{u} := by
  intro R _ _ _ _ J hJ hbot a
  set m := maximalIdeal R with hm
  choose N hN using exists_sup_pow_stable J hJ
  -- `L k` is the stable value of `J n ⊔ m ^ k`.
  set L : ℕ → Ideal R := fun k ↦ J (N k) ⊔ m ^ k with hLdef
  have hL : ∀ k k', k ≤ k' → L k = L k' ⊔ m ^ k := by
    intro k k' hkk'
    have h1 := hN k (max (N k) (N k')) (le_max_left _ _)
    have h2 := hN k' (max (N k) (N k')) (le_max_right _ _)
    have hpow : m ^ k' ≤ m ^ k := Ideal.pow_le_pow_right hkk'
    simp only [hLdef]
    rw [← h1, ← h2, sup_assoc, sup_eq_right.mpr hpow]
  have hlift : ∀ k x, x ∈ L k → ∃ x', x' ∈ L (k + 1) ∧ x - x' ∈ m ^ k := by
    intro k x hx
    rw [hL k (k + 1) k.le_succ] at hx
    obtain ⟨x', hx', e, he, rfl⟩ := Submodule.mem_sup.mp hx
    exact ⟨x', hx', by simpa using he⟩
  choose! lift hlift₁ hlift₂ using hlift
  refine ⟨N a, fun x hxJ ↦ ?_⟩
  have hx : x ∈ L a := Ideal.mem_sup_left hxJ
  -- A coherent sequence of lifts through the stable ideals, starting at `x`.
  let g : ℕ → R := fun k ↦ Nat.rec (motive := fun _ ↦ R) x (fun j y ↦ lift (a + j) y) k
  have hgs : ∀ k, g (k + 1) = lift (a + k) (g k) := fun k ↦ rfl
  have hgL : ∀ k, g k ∈ L (a + k) := by
    intro k
    induction k with
    | zero => exact hx
    | succ k ih => rw [hgs]; exact hlift₁ _ _ ih
  have hgstep : ∀ k, g k - g (k + 1) ∈ m ^ (a + k) := fun k ↦ by
    rw [hgs]; exact hlift₂ _ _ (hgL k)
  have hgcauchy : ∀ i j, i ≤ j → g i - g j ∈ m ^ (a + i) := by
    intro i j hij
    induction j, hij using Nat.le_induction with
    | base => simp
    | succ j hij ih =>
      have h' : g j - g (j + 1) ∈ m ^ (a + i) :=
        Ideal.pow_le_pow_right (by omega) (hgstep j)
      simpa [sub_add_sub_cancel] using add_mem ih h'
  have hsmul : ∀ k : ℕ, (m ^ k • ⊤ : Submodule R R) = m ^ k := fun k ↦ by
    rw [smul_eq_mul, Ideal.mul_top]
  -- The limit of the sequence.
  obtain ⟨y, hy⟩ := IsPrecomplete.prec' (I := m) g (fun {i j} hij ↦ by
    rw [SModEq.sub_mem, hsmul]
    exact Ideal.pow_le_pow_right (by omega) (hgcauchy i j hij))
  have hy' : ∀ k, g k - y ∈ m ^ k := fun k ↦ by
    have := hy k
    rwa [SModEq.sub_mem, hsmul] at this
  have hyL : ∀ k, y ∈ L k := by
    intro k
    have hgk : g k ∈ L k := by
      rw [hL k (a + k) (by omega)]
      exact Ideal.mem_sup_left (hgL k)
    have hdk : g k - y ∈ L k := Ideal.mem_sup_right (hy' k)
    simpa using sub_mem hgk hdk
  have hyJ : ∀ n, y ∈ J n := by
    intro n
    refine mem_of_forall_mem_sup_pow (J n) fun k ↦ ?_
    have h := hyL k
    simp only [hLdef] at h
    rw [← hN k (max n (N k)) (le_max_right _ _)] at h
    exact sup_le_sup_right (hJ (le_max_left _ _)) _ h
  have hy0 : y = 0 := by
    have : y ∈ ⨅ n, J n := Submodule.mem_iInf _ |>.mpr hyJ
    rwa [hbot, Submodule.mem_bot] at this
  have h0 : x - g a ∈ m ^ a := by
    have := hgcauchy 0 a (Nat.zero_le a)
    rwa [add_zero] at this
  have h1 : g a - y ∈ m ^ a := hy' a
  have hxy : x = (x - g a) + (g a - y) := by rw [hy0]; ring
  rw [hxy]
  exact add_mem h0 h1

end Langlands.Algebra
