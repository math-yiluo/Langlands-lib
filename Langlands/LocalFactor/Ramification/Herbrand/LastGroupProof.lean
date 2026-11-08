import Langlands.LocalFactor.Ramification.Herbrand.InertiaProof
import Langlands.VirtualRepresentation.Weil.Ramification

/-!
# The last ramification group is abelian

If `σ, τ` lie in the lower ramification group of index `n ≥ 1`, their commutator lies
in the lower group of index `2n`. Hence, when the group of index `n + 1` is trivial,
the group of index `n` is commutative. In upper numbering: if all upper groups of
index above `a > 0` are trivial, the upper group of index `a` is commutative.
-/

noncomputable section

namespace Langlands.Ramification.HerbrandBridge

open IsLocalRing

universe uK uL

section LocalRing

variable {A : Type*} [CommRing A] [IsLocalRing A]

/-- An automorphism moving every element by `𝔪^(n+1)` moves `𝔪^k` by `𝔪^(k+n)`. -/
theorem sub_mem_maximalIdeal_pow_of_mem (f : A ≃+* A) {n : ℕ}
    (hf : ∀ x, f x - x ∈ maximalIdeal A ^ (n + 1)) :
    ∀ k : ℕ, 1 ≤ k → ∀ b ∈ maximalIdeal A ^ k, f b - b ∈ maximalIdeal A ^ (k + n) := by
  intro k hk
  induction k, hk using Nat.le_induction with
  | base =>
    intro b _
    rw [add_comm]
    exact hf b
  | succ k hk ih =>
    intro b hb
    rw [pow_succ] at hb
    refine Submodule.mul_induction_on hb (fun x hx y hy => ?_) (fun x y hx hy => ?_)
    · have hfx : f x ∈ maximalIdeal A ^ k :=
        (ringEquiv_mem_maximalIdeal_pow_iff f k x).mpr hx
      have h1 : f x * (f y - y) ∈ maximalIdeal A ^ (k + 1 + n) := by
        rw [show k + 1 + n = k + (n + 1) by ring, pow_add]
        exact Ideal.mul_mem_mul hfx (hf y)
      have h2 : (f x - x) * y ∈ maximalIdeal A ^ (k + 1 + n) := by
        rw [show k + 1 + n = (k + n) + 1 by ring, pow_succ]
        exact Ideal.mul_mem_mul (ih x hx) hy
      have : f (x * y) - x * y = f x * (f y - y) + (f x - x) * y := by
        rw [map_mul]
        ring
      rw [this]
      exact Ideal.add_mem _ h1 h2
    · have : f (x + y) - (x + y) = (f x - x) + (f y - y) := by
        rw [map_add]
        ring
      rw [this]
      exact Ideal.add_mem _ hx hy

/-- Two automorphisms moving every element by `𝔪^(n+1)` commute modulo `𝔪^(2n+1)`. -/
theorem commutator_sub_mem_maximalIdeal_pow (f g : A ≃+* A) {n : ℕ}
    (hf : ∀ x, f x - x ∈ maximalIdeal A ^ (n + 1))
    (hg : ∀ x, g x - x ∈ maximalIdeal A ^ (n + 1)) (x : A) :
    f (g x) - g (f x) ∈ maximalIdeal A ^ (2 * n + 1) := by
  have ha := hf x
  have hb := hg x
  have h1 := sub_mem_maximalIdeal_pow_of_mem f hf (n + 1) (by omega) (g x - x) hb
  have h2 := sub_mem_maximalIdeal_pow_of_mem g hg (n + 1) (by omega) (f x - x) ha
  have : f (g x) - g (f x) =
      (f (g x - x) - (g x - x)) - (g (f x - x) - (f x - x)) := by
    rw [map_sub, map_sub]
    ring
  rw [this, show 2 * n + 1 = n + 1 + n by ring]
  exact Ideal.sub_mem _ h1 h2

end LocalRing

section Finite

open _root_.Langlands.Ramification.Padic

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uL} p} (T : F.TopologicalData)
  (K : Type uK) [Field K] [Algebra (Padic p) K] [Algebra K F.Carrier]
  [IsScalarTower (Padic p) K F.Carrier]

theorem integerAutomorphism_mul (σ τ : F.Carrier ≃ₐ[K] F.Carrier) (x : T.Integers) :
    integerAutomorphism T K (σ * τ) x =
      integerAutomorphism T K σ (integerAutomorphism T K τ x) :=
  Subtype.ext rfl

theorem integerAutomorphism_inv_apply (σ : F.Carrier ≃ₐ[K] F.Carrier) (x : T.Integers) :
    integerAutomorphism T K σ⁻¹ (integerAutomorphism T K σ x) = x :=
  Subtype.ext (σ.symm_apply_apply (x : F.Carrier))

/-- The commutator of two elements of the lower group of index `n ≥ 1` lies in the lower
group of index `2n`. -/
theorem commutator_mem_lowerRamificationGroup {n : ℕ} {σ τ : F.Carrier ≃ₐ[K] F.Carrier}
    (hσ : σ ∈ Padic.lowerRamificationGroup T K n) (hτ : τ ∈ Padic.lowerRamificationGroup T K n) :
    (τ * σ)⁻¹ * (σ * τ) ∈ Padic.lowerRamificationGroup T K (2 * n) := by
  rw [Padic.mem_lowerRamificationGroup] at hσ hτ ⊢
  intro y
  have hc := commutator_sub_mem_maximalIdeal_pow (integerAutomorphism T K σ)
    (integerAutomorphism T K τ) hσ hτ y
  set e := integerAutomorphism T K (τ * σ)⁻¹
  have he := (ringEquiv_mem_maximalIdeal_pow_iff e (2 * n + 1) _).mpr hc
  rw [map_sub] at he
  rw [integerAutomorphism_mul, integerAutomorphism_mul]
  convert he using 2
  rw [← integerAutomorphism_mul T K τ σ y]
  exact (integerAutomorphism_inv_apply T K (τ * σ) y).symm

/-- If the lower group of index `n + 1 ≥ 2` is trivial, the lower group of index `n` is
commutative. -/
theorem lowerRamificationGroup_commute {n : ℕ} (hn : 1 ≤ n)
    (hbot : Padic.lowerRamificationGroup T K (n + 1) = ⊥) {σ τ : F.Carrier ≃ₐ[K] F.Carrier}
    (hσ : σ ∈ Padic.lowerRamificationGroup T K n) (hτ : τ ∈ Padic.lowerRamificationGroup T K n) :
    σ * τ = τ * σ := by
  have h := Padic.lowerRamificationGroup_antitone T K (show n + 1 ≤ 2 * n by omega)
    (commutator_mem_lowerRamificationGroup T K hσ hτ)
  rw [hbot, Subgroup.mem_bot, inv_mul_eq_one] at h
  exact h.symm

/-- For `a > 0`, the commutator of two elements of the upper group of index `a` lies in an
upper group of strictly larger index. -/
theorem exists_gt_commutator_mem_upperRamificationGroup {a : ℝ} (ha : 0 < a)
    {σ τ : F.Carrier ≃ₐ[K] F.Carrier}
    (hσ : σ ∈ Padic.upperRamificationGroup T K a) (hτ : τ ∈ Padic.upperRamificationGroup T K a) :
    ∃ w, a < w ∧ (τ * σ)⁻¹ * (σ * τ) ∈ Padic.upperRamificationGroup T K w := by
  have hpos : 0 < Padic.herbrandPsi T K a := Padic.herbrandPsi_pos T K ha
  obtain ⟨m, hm⟩ : ∃ m : ℕ, ⌈Padic.herbrandPsi T K a⌉ = m :=
    ⟨_, (Int.toNat_of_nonneg (Int.ceil_nonneg hpos.le)).symm⟩
  have hm1 : 1 ≤ m := by
    have := Int.ceil_pos.mpr hpos
    omega
  have hlt : Padic.herbrandPsi T K a < (m : ℝ) + 1 := by
    have := Int.le_ceil (Padic.herbrandPsi T K a)
    rw [show (⌈Padic.herbrandPsi T K a⌉ : ℝ) = (m : ℝ) by exact_mod_cast hm] at this
    linarith
  obtain ⟨w, haw, hw⟩ : ∃ w, a < w ∧ Padic.herbrandPsi T K w < (m : ℝ) + 1 := by
    have hev : ∀ᶠ w in nhds a, Padic.herbrandPsi T K w < (m : ℝ) + 1 :=
      ((Padic.herbrandPsi_continuous T K).tendsto a).eventually (gt_mem_nhds hlt)
    obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.mp hev
    refine ⟨a + ε / 2, by linarith, hball ?_⟩
    rw [Real.dist_eq, abs_lt]
    constructor <;> linarith
  have hceil : ⌈Padic.herbrandPsi T K w⌉ ≤ ((m + 1 : ℕ) : ℤ) := by
    rw [Int.ceil_le]
    push_cast
    exact hw.le
  have hle : Padic.lowerRamificationGroup T K (m + 1) ≤ Padic.upperRamificationGroup T K w := by
    rw [Padic.upperRamificationGroup_eq_lower, ← Padic.lowerRamificationGroupReal_nat,
      Padic.lowerRamificationGroupReal,
      show ⌈((m + 1 : ℕ) : ℝ)⌉ = ((m + 1 : ℕ) : ℤ) from Int.ceil_natCast _]
    exact Padic.lowerRamificationGroupInt_antitone T K hceil
  have hlower : ∀ {ρ : F.Carrier ≃ₐ[K] F.Carrier}, ρ ∈ Padic.upperRamificationGroup T K a →
      ρ ∈ Padic.lowerRamificationGroup T K m := by
    intro ρ hρ
    rw [Padic.upperRamificationGroup_eq_lower, hm, ← Padic.lowerRamificationGroupReal_int,
      Int.cast_natCast, Padic.lowerRamificationGroupReal_nat] at hρ
    exact hρ
  refine ⟨w, haw, hle ?_⟩
  exact Padic.lowerRamificationGroup_antitone T K (show m + 1 ≤ 2 * m by omega)
    (commutator_mem_lowerRamificationGroup T K (hlower hσ) (hlower hτ))

/-- If every upper group of index above `a > 0` is trivial, the upper group of index `a`
is commutative. -/
theorem upperRamificationGroup_commute {a : ℝ} (ha : 0 < a)
    (hbot : ∀ w, a < w → Padic.upperRamificationGroup T K w = ⊥)
    {σ τ : F.Carrier ≃ₐ[K] F.Carrier}
    (hσ : σ ∈ Padic.upperRamificationGroup T K a) (hτ : τ ∈ Padic.upperRamificationGroup T K a) :
    σ * τ = τ * σ := by
  obtain ⟨w, haw, h⟩ := exists_gt_commutator_mem_upperRamificationGroup T K ha hσ hτ
  rw [hbot w haw, Subgroup.mem_bot, inv_mul_eq_one] at h
  exact h.symm

end Finite

section Absolute

open _root_.Langlands.Ramification.Padic

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uL} p)

/-- The closed right limit `G^{a+}` of the absolute upper filtration: the Krull closure of
the union of the upper groups of index strictly larger than `a`. -/
def absoluteUpperRightLimit (a : ℝ) : Subgroup (Field.absoluteGaloisGroup F.Carrier) :=
  (⨆ (w : ℝ) (_ : a < w), absoluteUpperRamificationGroup F w).topologicalClosure

theorem isClosed_absoluteUpperRightLimit (a : ℝ) :
    IsClosed (absoluteUpperRightLimit F a : Set (Field.absoluteGaloisGroup F.Carrier)) :=
  Subgroup.isClosed_topologicalClosure _

/-- For `a > 0`, the commutator of two elements of the absolute upper group of index `a`
lies in the closed right limit `G^{a+}`. -/
theorem commutator_mem_closedRightLimit {a : ℝ} (ha : 0 < a)
    {σ τ : Field.absoluteGaloisGroup F.Carrier}
    (hσ : σ ∈ absoluteUpperRamificationGroup F a) (hτ : τ ∈ absoluteUpperRamificationGroup F a) :
    (τ * σ)⁻¹ * (σ * τ) ∈ absoluteUpperRightLimit F a := by
  rw [← iInf_comap_map_absoluteFiniteRestriction F _ (isClosed_absoluteUpperRightLimit F a),
    Subgroup.mem_iInf]
  intro L
  rw [Subgroup.mem_comap, absoluteUpperRightLimit,
    absoluteUpperClosedRightImage F L a (by linarith)]
  have hσL := absoluteUpperRamificationGroup_le_comap F a L hσ
  have hτL := absoluteUpperRamificationGroup_le_comap F a L hτ
  rw [Subgroup.mem_comap] at hσL hτL
  obtain ⟨w, haw, hw⟩ := exists_gt_commutator_mem_upperRamificationGroup
    (absoluteFiniteExtension F L).canonicalTopologicalData F.Carrier ha hσL hτL
  have hmem : (absoluteFiniteRestriction F L).toMonoidHom ((τ * σ)⁻¹ * (σ * τ)) ∈
      canonicalUpperRamificationGroup (absoluteFiniteExtension F L) F.Carrier w := by
    rw [map_mul, map_inv, map_mul, map_mul]
    exact hw
  exact (le_iSup₂ (f := fun (w : ℝ) (_ : a < w) =>
    canonicalUpperRamificationGroup (absoluteFiniteExtension F L) F.Carrier w) w haw) hmem

/-- The same statement for the actual upper groups of the local Weil group. -/
theorem localProjection_commutator_mem_closedRightLimit {a : ℝ} (ha : 0 < a)
    {x y : Weil.Local.localWeilGroup F}
    (hx : x ∈ VirtualRepresentation.LocalWeil.Ramification.upperGroup F a)
    (hy : y ∈ VirtualRepresentation.LocalWeil.Ramification.upperGroup F a) :
    Weil.Local.localProjection F ((y * x)⁻¹ * (x * y)) ∈ absoluteUpperRightLimit F a := by
  rw [map_mul, map_inv, map_mul, map_mul]
  exact commutator_mem_closedRightLimit F ha hx hy

end Absolute

end Langlands.Ramification.HerbrandBridge
