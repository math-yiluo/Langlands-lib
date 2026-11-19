import Langlands.AlgebraicGeometry.SmoothThickeningLiftingStatement
import Langlands.AlgebraicGeometry.SmoothLifting.SquareZero

/-! # Proof: smooth morphisms lift along nilpotent thickenings of affine schemes

The square-zero case is `SmoothLifting.exists_lift_sqZero`. A kernel `K` with `K ^ (m + 2) = 0`
is handled by lifting first through `C ⧸ K ^ (m + 1) → D` (induction) and then through the
square-zero thickening `C → C ⧸ K ^ (m + 1)`.
-/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.AlgebraicGeometry

open SmoothLifting

/-- Lifting along a surjection whose kernel has vanishing `(m + 1)`-st power. -/
theorem exists_lift_of_pow_eq_bot {X S : Scheme.{u}} (f : X ⟶ S) [Smooth f] (m : ℕ) :
    ∀ {C D : CommRingCat.{u}} (q : C ⟶ D), Function.Surjective q.hom →
      RingHom.ker q.hom ^ (m + 1) = ⊥ → ∀ (x₀ : Spec D ⟶ X) (s : Spec C ⟶ S),
        x₀ ≫ f = Spec.map q ≫ s → ∃ x : Spec C ⟶ X, Spec.map q ≫ x = x₀ ∧ x ≫ f = s := by
  induction m with
  | zero =>
    intro C D q hq hK x₀ s h
    refine exists_lift_sqZero q hq (fun a ha b _ => ?_) x₀ s h
    rw [zero_add, pow_one] at hK
    rw [hK] at ha
    rw [(Submodule.mem_bot _).mp ha, zero_mul]
  | succ m ih =>
    intro C D q hq hK x₀ s h
    set K := RingHom.ker q.hom
    set J := K ^ (m + 1)
    have hJK : J ≤ K := Ideal.pow_le_self (Nat.succ_ne_zero m)
    let q₁ : CommRingCat.of (C ⧸ J) ⟶ D := CommRingCat.ofHom (Ideal.Quotient.lift J q.hom hJK)
    let π : C ⟶ CommRingCat.of (C ⧸ J) := CommRingCat.ofHom (Ideal.Quotient.mk J)
    have hq₁π : π ≫ q₁ = q := by ext c; rfl
    have hq₁ : Function.Surjective q₁.hom := by
      intro d
      obtain ⟨c, rfl⟩ := hq d
      exact ⟨Ideal.Quotient.mk J c, rfl⟩
    have hker : RingHom.ker q₁.hom ≤ K.map (Ideal.Quotient.mk J) := by
      intro y hy
      obtain ⟨c, rfl⟩ := Ideal.Quotient.mk_surjective y
      exact Ideal.mem_map_of_mem _ hy
    have hK₁ : RingHom.ker q₁.hom ^ (m + 1) = ⊥ := by
      refine le_bot_iff.mp ((Ideal.pow_right_mono hker _).trans ?_)
      rw [← Ideal.map_pow, Ideal.map_quotient_self]
    obtain ⟨x₁, hx₁, hx₁f⟩ := ih q₁ hq₁ hK₁ x₀ (Spec.map π ≫ s)
      (by rw [h, ← hq₁π, Spec.map_comp, Category.assoc])
    have hJsq : SqZero (RingHom.ker π.hom) := by
      intro a ha b hb
      have ha' : a ∈ J := by
        rw [CommRingCat.hom_ofHom, Ideal.mk_ker] at ha; exact ha
      have hb' : b ∈ J := by
        rw [CommRingCat.hom_ofHom, Ideal.mk_ker] at hb; exact hb
      have hab : a * b ∈ K ^ (m + 1 + 1) := by
        refine Ideal.pow_le_pow_right (show m + 1 + 1 ≤ (m + 1) + (m + 1) by omega) ?_
        rw [pow_add]
        exact Ideal.mul_mem_mul ha' hb'
      rw [hK] at hab
      exact (Submodule.mem_bot _).mp hab
    obtain ⟨x, hx, hxf⟩ := exists_lift_sqZero π Ideal.Quotient.mk_surjective hJsq x₁ s hx₁f
    refine ⟨x, ?_, hxf⟩
    rw [← hq₁π, Spec.map_comp, Category.assoc, hx, hx₁]

/-- **Infinitesimal lifting for smooth morphisms** along nilpotent thickenings of affine
schemes. -/
theorem smoothThickeningLifting : SmoothThickeningLiftingStatement.{u} := by
  intro X S f _ C D q hq hnil x₀ s h
  obtain ⟨n, hn⟩ := hnil
  refine exists_lift_of_pow_eq_bot f n q hq ?_ x₀ s h
  rw [Submodule.zero_eq_bot] at hn
  exact le_bot_iff.mp ((Ideal.pow_le_pow_right (Nat.le_succ n)).trans hn.le)

end Langlands.AlgebraicGeometry
