import Mathlib.GroupTheory.Transfer

/-! # The transfer to the kernel of a degree map modulo `f`

Let `d : G →* Multiplicative ℤ` be a homomorphism and `H` the subgroup of elements whose
degree is divisible by `f`, assumed of finite index (which forces `f > 0` as soon as some
element has degree one). For an element `y` of degree one, the cosets of `H` form one orbit
under the powers of `y`, of length `f`, so the transfer of `ϕ : H →* A` at `y` is
`ϕ (y ^ f)`.
-/

namespace Langlands.GroupTheory.Transfer

open MulAction Subgroup

variable {G A : Type*} [Group G] [CommGroup A]

/-- If `H` has finite index and consists of the elements whose degree is divisible by `f`,
and `y` has degree one, then the transfer of every `ϕ : H →* A` at `y` is `ϕ (y ^ f)`. -/
theorem transfer_eq_of_degree (H : Subgroup G) [H.FiniteIndex] (d : G →* Multiplicative ℤ)
    (f : ℕ) (hH : ∀ g, g ∈ H ↔ (f : ℤ) ∣ (d g).toAdd) (ϕ : H →* A) (y : G)
    (hy : d y = Multiplicative.ofAdd 1) :
    MonoidHom.transfer ϕ y = ϕ ⟨y ^ f, (hH _).2 (by simp [hy])⟩ := by
  classical
  have hdz : ∀ k : ℤ, (d (y ^ k)).toAdd = k := by
    intro k
    simp [map_zpow, hy]
  have hdn : ∀ k : ℕ, (d (y ^ k)).toAdd = k := by
    intro k
    simpa using hdz k
  have hcoset : ∀ (k : ℤ) (a b : G), (y ^ k • (a : G ⧸ H) = (b : G ⧸ H)) ↔
      (f : ℤ) ∣ (d b).toAdd - (d a).toAdd - k := by
    intro k a b
    rw [MulAction.Quotient.smul_mk, QuotientGroup.eq, hH]
    simp only [smul_eq_mul, mul_inv_rev, map_mul, map_inv, map_zpow, hy, toAdd_mul, toAdd_inv,
      toAdd_zpow, toAdd_ofAdd, smul_eq_mul, mul_one]
    constructor <;> intro h <;> convert h using 1 <;> ring
  have hsub : Subsingleton (Quotient (orbitRel (zpowers y) (G ⧸ H))) := by
    refine ⟨fun q₁ q₂ => ?_⟩
    induction q₁ using Quotient.inductionOn with
    | h Q₁ =>
    induction q₂ using Quotient.inductionOn with
    | h Q₂ =>
    induction Q₁ using QuotientGroup.induction_on with
    | H a =>
    induction Q₂ using QuotientGroup.induction_on with
    | H b =>
    apply Quotient.sound
    change (orbitRel (zpowers y) (G ⧸ H)) (a : G ⧸ H) (b : G ⧸ H)
    rw [orbitRel_apply]
    refine ⟨⟨y ^ ((d a).toAdd - (d b).toAdd), zpow_mem_zpowers _ _⟩, ?_⟩
    change y ^ ((d a).toAdd - (d b).toAdd) • (b : G ⧸ H) = (a : G ⧸ H)
    rw [hcoset]
    simp
  have hperiod : ∀ Q : G ⧸ H, Function.minimalPeriod (y • ·) Q = f := by
    intro Q
    induction Q using QuotientGroup.induction_on with
    | H a =>
    have hper : ∀ n : ℕ, Function.IsPeriodicPt (y • ·) n (a : G ⧸ H) ↔ (f : ℤ) ∣ n := by
      intro n
      rw [Function.IsPeriodicPt, Function.IsFixedPt, smul_iterate, ← zpow_natCast, hcoset]
      simp
    apply Nat.dvd_antisymm
    · exact Function.IsPeriodicPt.minimalPeriod_dvd ((hper f).2 dvd_rfl)
    · exact Int.natCast_dvd_natCast.mp
        ((hper _).1 (Function.isPeriodicPt_minimalPeriod (y • ·) (a : G ⧸ H)))
  have key : ∀ (r : G) (n : ℕ) (hn : n = f) (p : r⁻¹ * y ^ n * r ∈ H),
      ϕ ⟨r⁻¹ * y ^ n * r, p⟩ = ϕ ⟨y ^ f, (hH _).2 (by simp [hy])⟩ := by
    rintro r n rfl p
    set k := (d r).toAdd
    have hh : y ^ (-k) * r ∈ H := by
      rw [hH]
      simp [k, hy]
    have heq : (⟨r⁻¹ * y ^ n * r, p⟩ : H) =
        (⟨y ^ (-k) * r, hh⟩ : H)⁻¹ * ⟨y ^ n, (hH _).2 (by simp [hy])⟩ *
          ⟨y ^ (-k) * r, hh⟩ := by
      apply Subtype.ext
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, mul_inv_rev, zpow_neg, inv_inv]
      have hc : y ^ k * y ^ n = y ^ n * y ^ k := by
        rw [← zpow_natCast, ← zpow_add, ← zpow_add, add_comm]
      calc r⁻¹ * y ^ n * r = r⁻¹ * (y ^ k * y ^ n) * (y ^ k)⁻¹ * r := by
            rw [hc]; group
        _ = _ := by group
    rw [heq, map_mul, map_mul, map_inv, mul_comm (ϕ _)⁻¹, mul_assoc, inv_mul_cancel, mul_one]
  have : Fintype (Quotient (orbitRel (zpowers y) (G ⧸ H))) := Fintype.ofFinite _
  rw [MonoidHom.transfer_eq_prod_quotient_orbitRel_zpowers_quot]
  obtain ⟨q₀⟩ : Nonempty (Quotient (orbitRel (zpowers y) (G ⧸ H))) :=
    ⟨Quotient.mk _ ((1 : G) : G ⧸ H)⟩
  rw [Fintype.prod_subsingleton _ q₀]
  exact key _ _ (hperiod _) _

end Langlands.GroupTheory.Transfer
