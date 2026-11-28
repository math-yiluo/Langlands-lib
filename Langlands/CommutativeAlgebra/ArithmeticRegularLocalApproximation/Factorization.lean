import Mathlib.RingTheory.Adjoin.Basic
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.RingTheory.Ideal.Maps
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.RingTheory.Localization.FractionRing

/-! # Factoring a map to a fraction field through a localization at one element -/

namespace Langlands.CommutativeAlgebra.ArithmeticRegularLocalApproximation

/-- In a discrete valuation ring with uniformizer `ϖ`, every element of the fraction field
becomes integral after multiplication by a power of `ϖ`. -/
theorem exists_mul_pow_eq_algebraMap {W K : Type*} [CommRing W] [IsDomain W]
    [IsDiscreteValuationRing W] [Field K] [Algebra W K] [IsFractionRing W K] {ϖ : W}
    (hϖ : Irreducible ϖ) (x : K) :
    ∃ (a : W) (n : ℕ), x * algebraMap W K (ϖ ^ n) = algebraMap W K a := by
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := W) x
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
  obtain ⟨n, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hb0 hϖ
  refine ⟨a * ↑u⁻¹, n, ?_⟩
  have hu : algebraMap W K (↑u⁻¹ : W) * algebraMap W K (u : W) = 1 := by
    rw [← map_mul, Units.inv_mul, map_one]
  have hne : algebraMap W K ((u : W) * ϖ ^ n) ≠ 0 :=
    (IsFractionRing.injective W K).ne_iff' (map_zero _) |>.mpr hb0
  rw [div_mul_eq_mul_div, div_eq_iff hne]
  simp only [map_mul]
  linear_combination (-(algebraMap W K a * algebraMap W K (ϖ ^ n))) * hu

/-- Let `Θ : A → W'` be a ring map to a domain and `Ψ : A → P` a ring map with
`ker Θ ⊆ ker Ψ`, and let `hP : P → W'` satisfy `hP ∘ Ψ = Θ`. Let `a₀ ∈ A` with `Θ a₀ ≠ 0`. If
`F : C → Frac W'` sends each member of a set generating `C` as a ring to a quotient
`Θ a / (Θ a₀)ⁿ`, then `F` factors through `P[1/Ψ a₀]`, compatibly with `hP`. -/
theorem exists_away_factorization {A W' P C : Type*} [CommRing A] [CommRing W'] [IsDomain W']
    [CommRing P] [CommRing C] (Θ : A →+* W') (Ψ : A →+* P) (hP : P →+* W')
    (hPΨ : hP.comp Ψ = Θ) (hker : RingHom.ker Θ ≤ RingHom.ker Ψ) (a₀ : A) (ha₀ : Θ a₀ ≠ 0)
    (F : C →+* FractionRing W') (s : Set C) (hs : Algebra.adjoin ℤ s = ⊤)
    (hF : ∀ c ∈ s, ∃ (a : A) (n : ℕ),
      F c * algebraMap W' (FractionRing W') (Θ a₀ ^ n) = algebraMap W' (FractionRing W') (Θ a)) :
    ∃ (jAway : Localization.Away (Ψ a₀) →+* FractionRing W')
      (g : C →+* Localization.Away (Ψ a₀)),
      jAway.comp (algebraMap P (Localization.Away (Ψ a₀))) =
        (algebraMap W' (FractionRing W')).comp hP ∧
      jAway.comp g = F := by
  classical
  have hinjW : Function.Injective (algebraMap W' (FractionRing W')) :=
    IsFractionRing.injective W' (FractionRing W')
  have hkerS : RingHom.ker Θ.rangeRestrict ≤ RingHom.ker Ψ := by
    rw [RingHom.ker_rangeRestrict]
    exact hker
  -- The induced map `θ : Θ(A) → P`.
  let θ : Θ.range →+* P :=
    Θ.rangeRestrict.liftOfSurjective Θ.rangeRestrict_surjective ⟨Ψ, hkerS⟩
  have hθ (a : A) : θ (Θ.rangeRestrict a) = Ψ a :=
    RingHom.liftOfSurjective_comp_apply _ _ _ a
  have hPθ (r : Θ.range) : hP (θ r) = r := by
    obtain ⟨a, rfl⟩ := Θ.rangeRestrict_surjective r
    rw [hθ, ← RingHom.comp_apply, hPΨ]
    rfl
  set x₀ : Θ.range := Θ.rangeRestrict a₀ with hx₀def
  have hx₀ : θ x₀ = Ψ a₀ := hθ a₀
  -- The embedding `ι : Θ(A)[1/x₀] → Frac W'`.
  have hu : IsUnit (((algebraMap W' (FractionRing W')).comp Θ.range.subtype) x₀) := by
    rw [isUnit_iff_ne_zero, RingHom.comp_apply]
    exact hinjW.ne_iff' (map_zero _) |>.mpr ha₀
  let ι : Localization.Away x₀ →+* FractionRing W' := IsLocalization.Away.lift x₀ hu
  have hι : Function.Injective ι := by
    rw [injective_iff_map_eq_zero]
    intro z hz
    obtain ⟨⟨r, m⟩, rfl⟩ := IsLocalization.mk'_surjective (Submonoid.powers x₀) z
    have h1 := (IsLocalization.lift_mk'_spec _ _ _ _).mp hz
    rw [mul_zero, RingHom.comp_apply] at h1
    have h2 : r = 0 := Subtype.ext (hinjW (h1.trans (map_zero _).symm))
    rw [h2]
    exact IsLocalization.mk'_zero _
  have hrange (c : C) : F c ∈ ι.range := by
    have hc : c ∈ Algebra.adjoin ℤ s := hs ▸ Algebra.mem_top
    induction hc using Algebra.adjoin_induction with
    | mem c hc =>
      obtain ⟨a, n, ha⟩ := hF c hc
      refine ⟨IsLocalization.mk' _ (Θ.rangeRestrict a)
        (⟨x₀ ^ n, n, rfl⟩ : Submonoid.powers x₀), ?_⟩
      refine (IsLocalization.lift_mk'_spec _ _ _ _).mpr ?_
      simp only [RingHom.comp_apply, Subring.coe_subtype, SubmonoidClass.coe_pow]
      rw [mul_comm]
      exact ha.symm
    | algebraMap n =>
      simp only [algebraMap_int_eq, eq_intCast, map_intCast]
      exact intCast_mem _ n
    | add x y _ _ hx hy => simpa using add_mem hx hy
    | mul x y _ _ hx hy => simpa using mul_mem hx hy
  let e : Localization.Away x₀ ≃+* ι.range :=
    RingEquiv.ofBijective ι.rangeRestrict
      ⟨fun a b hab => hι (congrArg Subtype.val hab), ι.rangeRestrict_surjective⟩
  let g₁ : C →+* Localization.Away x₀ := e.symm.toRingHom.comp (F.codRestrict ι.range hrange)
  have hg₁ : ι.comp g₁ = F := by
    ext c
    exact congrArg Subtype.val (e.apply_symm_apply ⟨F c, hrange c⟩)
  -- Comparison of `Θ(A)[1/x₀]` with `P[1/Ψ a₀]`.
  have hμ : IsUnit (((algebraMap P (Localization.Away (Ψ a₀))).comp θ) x₀) := by
    rw [RingHom.comp_apply, hx₀]
    exact IsLocalization.Away.algebraMap_isUnit _
  let μ : Localization.Away x₀ →+* Localization.Away (Ψ a₀) := IsLocalization.Away.lift x₀ hμ
  have hunit : IsUnit (((algebraMap W' (FractionRing W')).comp hP) (Ψ a₀)) := by
    rw [isUnit_iff_ne_zero, RingHom.comp_apply, ← RingHom.comp_apply hP, hPΨ]
    exact hinjW.ne_iff' (map_zero _) |>.mpr ha₀
  let jAway : Localization.Away (Ψ a₀) →+* FractionRing W' :=
    IsLocalization.Away.lift (Ψ a₀) hunit
  have hjAway : jAway.comp (algebraMap P (Localization.Away (Ψ a₀))) =
      (algebraMap W' (FractionRing W')).comp hP :=
    IsLocalization.Away.lift_comp _ hunit
  have hjμ : jAway.comp μ = ι := by
    apply IsLocalization.ringHom_ext (Submonoid.powers x₀)
    ext r
    simp only [RingHom.comp_apply, μ, ι, IsLocalization.Away.lift_eq, jAway, hPθ,
      Subring.coe_subtype]
  refine ⟨jAway, μ.comp g₁, hjAway, ?_⟩
  rw [← RingHom.comp_assoc, hjμ, hg₁]

end Langlands.CommutativeAlgebra.ArithmeticRegularLocalApproximation
