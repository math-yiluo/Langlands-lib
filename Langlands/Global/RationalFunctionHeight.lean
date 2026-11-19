import Mathlib.NumberTheory.Height.NumberField
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.Algebra.MvPolynomial.CommRing

/-! # Polynomial height bounds for rational functions -/

noncomputable section

namespace Langlands.Global

open Height Height.AdmissibleAbsValues

section Field

variable {K : Type*} [Field K] [AdmissibleAbsValues K] {X : Type*}

/-- Functions with a polynomial bound on their scalar height form a subalgebra. -/
def polynomialHeightBounded (H : X → ℝ) (hH : ∀ x, 1 ≤ H x) : Subalgebra K (X → K) where
  carrier := {f | ∃ C : ℝ, 0 < C ∧ ∃ d : ℕ, ∀ x, mulHeight₁ (f x) ≤ C * H x ^ d}
  algebraMap_mem' c := ⟨mulHeight₁ c, mulHeight₁_pos c, 0, fun x => by simp⟩
  add_mem' := by
    rintro f g ⟨C, hC, d, hf⟩ ⟨D, hD, e, hg⟩
    refine ⟨2 ^ totalWeight K * C * D, by positivity, d + e, fun x => ?_⟩
    have hx : 0 ≤ H x := zero_le_one.trans (hH x)
    calc
      mulHeight₁ ((f + g) x) ≤ 2 ^ totalWeight K * mulHeight₁ (f x) * mulHeight₁ (g x) :=
        mulHeight₁_add_le _ _
      _ ≤ (2 ^ totalWeight K * (C * H x ^ d)) * (D * H x ^ e) :=
        mul_le_mul (mul_le_mul_of_nonneg_left (hf x) (by positivity)) (hg x)
          (mulHeight₁_nonneg _) (by positivity)
      _ = (2 ^ totalWeight K * C * D) * H x ^ (d + e) := by rw [pow_add]; ring
  mul_mem' := by
    rintro f g ⟨C, hC, d, hf⟩ ⟨D, hD, e, hg⟩
    refine ⟨C * D, mul_pos hC hD, d + e, fun x => ?_⟩
    have hx : 0 ≤ H x := zero_le_one.trans (hH x)
    calc
      mulHeight₁ ((f * g) x) ≤ mulHeight₁ (f x) * mulHeight₁ (g x) :=
        mulHeight₁_mul_le _ _
      _ ≤ (C * H x ^ d) * (D * H x ^ e) :=
        mul_le_mul (hf x) (hg x) (mulHeight₁_nonneg _) (by positivity)
      _ = (C * D) * H x ^ (d + e) := by rw [pow_add]; ring

theorem inv_mem_polynomialHeightBounded {H : X → ℝ} {hH : ∀ x, 1 ≤ H x} {f : X → K}
    (hf : f ∈ polynomialHeightBounded H hH) : f⁻¹ ∈ polynomialHeightBounded H hH := by
  obtain ⟨C, hC, d, hf⟩ := hf
  exact ⟨C, hC, d, fun x => by simpa only [Pi.inv_apply, mulHeight₁_inv] using hf x⟩

theorem mulHeight₁_div_le_mulHeight {ι : Type*} [Finite ι] (a : ι → K) (i j : ι) :
    mulHeight₁ (a i / a j) ≤ mulHeight a := by
  have hpair : a ∘ (![i, j] : Fin 2 → ι) = ![a i, a j] := by
    funext r
    fin_cases r <;> rfl
  rw [mulHeight₁_div_eq_mulHeight, ← hpair]
  exact mulHeight_comp_le _ _

variable {A B : Type*} [CommRing A] [CommRing B] [Algebra K A] [Algebra K B]

/-- If generators evaluate to functions of polynomial height growth, so does
every element of the algebra. -/
theorem mem_polynomialHeightBounded_of_adjoin_eq_top
    {H : X → ℝ} {hH : ∀ x, 1 ≤ H x} (ev : X → A →ₐ[K] K)
    {S : Set A} (hS : Algebra.adjoin K S = ⊤)
    (hgen : ∀ a ∈ S, (fun x => ev x a) ∈ polynomialHeightBounded H hH) (a : A) :
    (fun x => ev x a) ∈ polynomialHeightBounded H hH := by
  let e : A →ₐ[K] (X → K) := AlgHom.pi ev
  have hle : Algebra.adjoin K S ≤ (polynomialHeightBounded H hH).comap e :=
    Algebra.adjoin_le fun a ha => hgen a ha
  exact hle (by simp [hS])

/-- Localization preserves the polynomial height bound under evaluation in the
coefficient field. The chosen evaluation maps may vary with the point. -/
theorem mem_polynomialHeightBounded_away {H : X → ℝ} {hH : ∀ x, 1 ≤ H x}
    [Algebra A B] [IsScalarTower K A B] (f : A) [IsLocalization.Away f B]
    (ev : X → B →ₐ[K] K)
    (hbase : ∀ a : A, (fun x => ev x (algebraMap A B a)) ∈ polynomialHeightBounded H hH)
    (b : B) :
    (fun x => ev x b) ∈ polynomialHeightBounded H hH := by
  obtain ⟨⟨a, s⟩, hab⟩ := IsLocalization.surj (Submonoid.powers f) b
  have hs : (fun x => ev x (algebraMap A B (s : A))) ∈ polynomialHeightBounded H hH :=
    hbase s
  convert (polynomialHeightBounded H hH).mul_mem (hbase a)
    (inv_mem_polynomialHeightBounded hs) using 1
  funext x
  have hnz : ev x (algebraMap A B (s : A)) ≠ 0 :=
    ((IsLocalization.map_units B s).map (ev x).toMonoidHom).ne_zero
  have hb := congrArg (ev x) hab
  simp only [map_mul] at hb
  change ev x b = ev x (algebraMap A B a) * (ev x (algebraMap A B (s : A)))⁻¹
  rw [← div_eq_mul_inv, eq_div_iff hnz]
  exact hb

end Field

end Langlands.Global
