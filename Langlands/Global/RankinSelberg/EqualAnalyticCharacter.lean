import Langlands.Global.RankinSelberg.EqualAnalyticFourierSeries
import Langlands.Global.RankinSelberg.UnequalAnalyticStatement
import Langlands.Automorphic.CuspidalWhittaker.AdelicCharacter
import Langlands.Automorphic.CuspidalWhittaker.QuotientTorus

/-! # Standard additive characters of `𝔸 / F`

Every continuous unitary nontrivial character `ψ` of `𝔸` trivial on `F` is
`x ↦ ψ₀(b x)` for some `b ∈ F^×`, where `ψ₀` is the Library's explicit standard character
(`Langlands.Automorphic.CuspidalWhittaker.adelicCharacter`). The proof is by Fourier
analysis on the compact group `𝔸 / F`: the characters `x ↦ ψ₀(a x)`, `a ∈ F`, separate points
(the Library's self-duality of `F`), so a character orthogonal to all of them would vanish.
Consequently `F` is its own annihilator for every such `ψ`.
-/

noncomputable section
universe u
open NumberField MeasureTheory
open scoped ComplexConjugate Langlands.Automorphic.CuspidalWhittaker
set_option autoImplicit false

namespace Langlands.Global.RankinSelbergGlobal.EqualAnalytic

open Langlands.Global Langlands.Automorphic.CuspidalWhittaker

/-- A nontrivial continuous multiplicative function on a group with a finite invariant
measure has integral zero. -/
theorem integral_eq_zero_of_mul_apply {X : Type*} [AddGroup X] [TopologicalSpace X]
    [IsTopologicalAddGroup X] [MeasurableSpace X] [BorelSpace X] (ν : Measure X)
    [ν.IsAddLeftInvariant] (χ : X → ℂ) (hχ : ∀ x y, χ (x + y) = χ x * χ y) {y : X}
    (hy : χ y ≠ 1) : ∫ x, χ x ∂ν = 0 := by
  have h := integral_add_left_eq_self (μ := ν) χ y
  simp_rw [hχ y] at h
  rw [integral_const_mul] at h
  have : (χ y - 1) * ∫ x, χ x ∂ν = 0 := by rw [sub_mul, h, one_mul, sub_self]
  exact (mul_eq_zero.mp this).resolve_left (sub_ne_zero.mpr hy)

variable (F : Type u) [Field F] [NumberField F]

/-- The chosen lift `𝔸 / F → 𝔸`. -/
def quotientLift (x : AdeleQuotient F) : Adeles F :=
  Function.surjInv (QuotientAddGroup.mk_surjective (s := principalAdeles F)) x

theorem mk_quotientLift (x : AdeleQuotient F) :
    adeleQuotientMap F (quotientLift F x) = x :=
  Function.surjInv_eq (QuotientAddGroup.mk_surjective (s := principalAdeles F)) x

theorem exists_quotientLift_mk (y : Adeles F) :
    ∃ a : F, quotientLift F (adeleQuotientMap F y) = y + algebraMap F (Adeles F) a := by
  have h := mk_quotientLift F (adeleQuotientMap F y)
  have hmem : -y + quotientLift F (adeleQuotientMap F y) ∈ principalAdeles F :=
    QuotientAddGroup.eq.mp h.symm
  obtain ⟨a, ha⟩ := hmem
  refine ⟨a, ?_⟩
  change algebraMap F (Adeles F) a = _ at ha
  rw [ha]
  abel

theorem exists_quotientLift_add (x x' : AdeleQuotient F) :
    ∃ a : F, quotientLift F (x + x') =
      quotientLift F x + quotientLift F x' + algebraMap F (Adeles F) a := by
  have h : x + x' = adeleQuotientMap F (quotientLift F x + quotientLift F x') := by
    rw [map_add, mk_quotientLift, mk_quotientLift]
  rw [h]
  exact exists_quotientLift_mk F _

/-- A continuous function on `𝔸` invariant under translation by `F` descends to `𝔸 / F`. -/
def descend (f : Adeles F → ℂ) (hf : Continuous f)
    (hper : ∀ y (a : F), f (y + algebraMap F (Adeles F) a) = f y) :
    C(AdeleQuotient F, ℂ) where
  toFun x := f (quotientLift F x)
  continuous_toFun := by
    rw [(QuotientAddGroup.isOpenQuotientMap_mk (N := principalAdeles F)).isQuotientMap.continuous_iff]
    convert hf using 1
    funext y
    change f (quotientLift F (adeleQuotientMap F y)) = f y
    obtain ⟨a, ha⟩ := exists_quotientLift_mk F y
    rw [ha, hper]

theorem descend_mk (f : Adeles F → ℂ) (hf : Continuous f)
    (hper : ∀ y (a : F), f (y + algebraMap F (Adeles F) a) = f y) (y : Adeles F) :
    descend F f hf hper (adeleQuotientMap F y) = f y := by
  change f (quotientLift F (adeleQuotientMap F y)) = f y
  obtain ⟨a, ha⟩ := exists_quotientLift_mk F y
  rw [ha, hper]

/-- The character `x ↦ ψ(a x)` of `𝔸 / F` for an additive character `ψ` trivial on `F`. -/
def scaledCharacter (ψ : AddChar (Adeles F) ℂ) (hψ : Continuous ψ)
    (htriv : ∀ a : F, ψ (algebraMap F (Adeles F) a) = 1) (a : F) : C(AdeleQuotient F, ℂ) :=
  descend F (fun y => ψ (algebraMap F (Adeles F) a * y))
    (hψ.comp (continuous_const.mul continuous_id)) fun y b => by
      rw [mul_add, AddChar.map_add_eq_mul, ← RingHom.map_mul, htriv, mul_one]

theorem scaledCharacter_mk (ψ : AddChar (Adeles F) ℂ) (hψ : Continuous ψ)
    (htriv : ∀ a : F, ψ (algebraMap F (Adeles F) a) = 1) (a : F) (y : Adeles F) :
    scaledCharacter F ψ hψ htriv a (adeleQuotientMap F y) =
      ψ (algebraMap F (Adeles F) a * y) :=
  descend_mk F _ _ _ y

theorem scaledCharacter_apply (ψ : AddChar (Adeles F) ℂ) (hψ : Continuous ψ)
    (htriv : ∀ a : F, ψ (algebraMap F (Adeles F) a) = 1) (a : F) (x : AdeleQuotient F) :
    scaledCharacter F ψ hψ htriv a x = ψ (algebraMap F (Adeles F) a * quotientLift F x) :=
  rfl

theorem scaledCharacter_add_apply (ψ : AddChar (Adeles F) ℂ) (hψ : Continuous ψ)
    (htriv : ∀ a : F, ψ (algebraMap F (Adeles F) a) = 1) (a : F) (x x' : AdeleQuotient F) :
    scaledCharacter F ψ hψ htriv a (x + x') =
      scaledCharacter F ψ hψ htriv a x * scaledCharacter F ψ hψ htriv a x' := by
  rw [← mk_quotientLift F x, ← mk_quotientLift F x', ← map_add, scaledCharacter_mk,
    scaledCharacter_mk, scaledCharacter_mk, mul_add, AddChar.map_add_eq_mul]

/-- The standard character `ψ₀`, with complex values. -/
def standardCharacter : AddChar (Adeles F) ℂ :=
  (Circle.coeHom).compAddChar (adelicCharacter F)

theorem standardCharacter_apply (x : Adeles F) :
    standardCharacter F x = (adelicCharacter F x : ℂ) := rfl

theorem continuous_standardCharacter : Continuous (standardCharacter F) :=
  continuous_subtype_val.comp (continuous_adelicCharacter F)

theorem standardCharacter_algebraMap (a : F) :
    standardCharacter F (algebraMap F (Adeles F) a) = 1 := by
  rw [standardCharacter_apply, adelicCharacter_algebraMap, Circle.coe_one]

theorem isCharacterFamily_standard :
    IsCharacterFamily (scaledCharacter F (standardCharacter F) (continuous_standardCharacter F)
      (standardCharacter_algebraMap F)) where
  zero := by
    ext x
    rw [scaledCharacter_apply, map_zero, zero_mul, AddChar.map_zero_eq_one]
    rfl
  add a b := by
    ext x
    simp only [scaledCharacter_apply, ContinuousMap.mul_apply, map_add, add_mul,
      AddChar.map_add_eq_mul]
  neg a := by
    ext x
    simp only [scaledCharacter_apply, ContinuousMap.star_apply, map_neg, neg_mul,
      AddChar.map_neg_eq_inv, standardCharacter_apply]
    rw [← Circle.coe_inv, Circle.coe_inv_eq_conj]
    rfl
  norm_apply a x := by
    rw [scaledCharacter_apply, standardCharacter_apply, Circle.norm_coe]

theorem standardCharacter_eq_one_iff (x : Adeles F) :
    standardCharacter F x = 1 ↔ adelicCharacter F x = 1 := by
  rw [standardCharacter_apply, ← Circle.coe_one, Circle.coe_inj]

/-- The characters `x ↦ ψ₀(a x)` separate the points of `𝔸 / F`. -/
theorem standard_separates (x x' : AdeleQuotient F) (h : x ≠ x') :
    ∃ a : F, scaledCharacter F (standardCharacter F) (continuous_standardCharacter F)
        (standardCharacter_algebraMap F) a x ≠
      scaledCharacter F (standardCharacter F) (continuous_standardCharacter F)
        (standardCharacter_algebraMap F) a x' := by
  by_contra hcon
  push Not at hcon
  apply h
  obtain ⟨δ, hδ⟩ := exists_eq_algebraMap_of_orthogonal F
    (quotientLift F x' - quotientLift F x) fun a => by
      have h1 := hcon a
      rw [scaledCharacter_apply, scaledCharacter_apply, standardCharacter_apply,
        standardCharacter_apply, Circle.coe_inj] at h1
      rw [mul_sub, AddChar.map_sub_eq_div, h1, div_self']
  have hx' : quotientLift F x' = quotientLift F x + algebraMap F (Adeles F) δ := by
    rw [← hδ]
    abel
  rw [← mk_quotientLift F x, ← mk_quotientLift F x', hx', map_add]
  have hz : adeleQuotientMap F (algebraMap F (Adeles F) δ) = 0 :=
    (QuotientAddGroup.eq_zero_iff _).mpr ⟨δ, rfl⟩
  rw [hz, add_zero]

section Main

variable [CompactSpace (AdeleQuotient F)]

/-- For `a ≠ 0` the character `x ↦ ψ₀(a x)` of `𝔸 / F` has integral zero. -/
theorem integral_standard_eq_zero (a : F) (ha : a ≠ 0) :
    ∫ x, scaledCharacter F (standardCharacter F) (continuous_standardCharacter F)
      (standardCharacter_algebraMap F) a x ∂adeleQuotientHaar F = 0 := by
  obtain ⟨z, hz⟩ := exists_adelicCharacter_ne_one F
  apply integral_eq_zero_of_mul_apply (adeleQuotientHaar F) _
    (scaledCharacter_add_apply F _ _ _ a)
    (y := adeleQuotientMap F (algebraMap F (Adeles F) a⁻¹ * z))
  rw [scaledCharacter_mk, ← mul_assoc, ← RingHom.map_mul, mul_inv_cancel₀ ha, map_one,
    one_mul, Ne, standardCharacter_eq_one_iff]
  exact hz

/-- **Classification of standard characters.** Every continuous unitary nontrivial character
of `𝔸` trivial on `F` is `x ↦ ψ₀(b x)` for some `b ∈ F^×`. -/
theorem exists_eq_standardCharacter_mul (ψ : AddChar (Adeles F) ℂ)
    (hψ : IsStandardAdditiveCharacter F ψ) :
    ∃ b : F, b ≠ 0 ∧ ∀ x, ψ x = standardCharacter F (algebraMap F (Adeles F) b * x) := by
  set e := scaledCharacter F (standardCharacter F) (continuous_standardCharacter F)
    (standardCharacter_algebraMap F) with he_def
  set χ := scaledCharacter F ψ hψ.1 hψ.2.2.1 1 with hχ_def
  have hfam := isCharacterFamily_standard F
  have hex : ∃ b, ∀ x, χ x = e b x := by
    by_contra hcon
    push Not at hcon
    have hzero : χ = 0 := by
      apply eq_zero_of_fourierCoeff_eq_zero (adeleQuotientHaar F) hfam (standard_separates F)
      intro b
      obtain ⟨x₀, hx₀⟩ := hcon b
      apply integral_eq_zero_of_mul_apply (adeleQuotientHaar F)
        (fun x => χ x * star (e b x)) (y := x₀)
      · intro x x'
        rw [scaledCharacter_add_apply, he_def, scaledCharacter_add_apply, star_mul]
        ring
      · intro h1
        apply hx₀
        have hn : ‖e b x₀‖ = 1 := hfam.norm_apply b x₀
        have hstar : e b x₀ * star (e b x₀) = 1 := by
          rw [RCLike.star_def, RCLike.mul_conj, hn]
          simp
        calc χ x₀ = χ x₀ * star (e b x₀) * e b x₀ := by
              rw [mul_assoc, mul_comm (star _), hstar, mul_one]
          _ = e b x₀ := by rw [h1, one_mul]
    have h0 := congrArg (fun f : C(AdeleQuotient F, ℂ) => f (adeleQuotientMap F 0)) hzero
    simp only [hχ_def, scaledCharacter_mk, map_one, one_mul, AddChar.map_zero_eq_one,
      ContinuousMap.zero_apply] at h0
    exact one_ne_zero h0
  obtain ⟨b, hb⟩ := hex
  have hψb : ∀ x, ψ x = standardCharacter F (algebraMap F (Adeles F) b * x) := by
    intro x
    have := hb (adeleQuotientMap F x)
    rw [hχ_def, he_def, scaledCharacter_mk, scaledCharacter_mk, map_one, one_mul] at this
    exact this
  refine ⟨b, ?_, hψb⟩
  rintro rfl
  apply hψ.2.1
  ext x
  rw [hψb, map_zero, zero_mul, AddChar.map_zero_eq_one, AddChar.one_apply]

/-- **Self-duality of `F`** for every standard character: if `ψ(a y) = 1` for all `a ∈ F`,
then `y ∈ F`. -/
theorem exists_eq_algebraMap_of_forall_eq_one (ψ : AddChar (Adeles F) ℂ)
    (hψ : IsStandardAdditiveCharacter F ψ) (y : Adeles F)
    (hy : ∀ a : F, ψ (algebraMap F (Adeles F) a * y) = 1) :
    ∃ δ : F, y = algebraMap F (Adeles F) δ := by
  obtain ⟨b, hb, hψb⟩ := exists_eq_standardCharacter_mul F ψ hψ
  apply exists_eq_algebraMap_of_orthogonal F y
  intro a
  have h := hy (a / b)
  rw [hψb, ← mul_assoc, ← RingHom.map_mul, mul_div_cancel₀ a hb,
    standardCharacter_eq_one_iff] at h
  exact h

end Main

end Langlands.Global.RankinSelbergGlobal.EqualAnalytic
