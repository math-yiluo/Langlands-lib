import Langlands.Representation.RankinSelberg.EqualRankSwapTransport

/-! Coefficient-model transport by the diagonal at minus one. -/

noncomputable section

namespace Langlands.RankinSelberg

open Whittaker GeneralLinear HarmonicAnalysis MeasureTheory

universe uF uV

variable {F : Type uF} [Field F] [TopologicalSpace F] [IsTopologicalRing F]
  (ψ : UnitaryAdditiveCharacter F) {n : ℕ}
  {V : Type uV} [AddCommGroup V] [Module ℂ V]
  (π : Representation ℂ (Langlands.GeneralLinear (n + 1) F) V)

/-- Left translation by the minus-one diagonal changes standard covariance to
inverse covariance, at the original additive character. -/
def negOneInverseFunctional (ℓ : glFunctionals ψ n π) : glInverseFunctionals ψ n π :=
  ⟨(characterChangeFunctional ψ π (-1) ℓ).val, by
    simpa only [glFunctionals, glInverseFunctionals, standardCharacter_scale_neg_one]
      using (characterChangeFunctional ψ π (-1) ℓ).property⟩

/-- Left translation by the same diagonal changes inverse to standard covariance. -/
def negOneStandardFunctional (ℓ : glInverseFunctionals ψ n π) : glFunctionals ψ n π :=
  ⟨(characterChangeInverseFunctional ψ π (-1) ℓ).val, by
    simpa only [glFunctionals, glInverseFunctionals, inverseStandardCharacter_scale_neg_one]
      using (characterChangeInverseFunctional ψ π (-1) ℓ).property⟩

@[simp] theorem negOneInverseFunctional_apply (ℓ : glFunctionals ψ n π) (v : V) :
    (negOneInverseFunctional ψ π ℓ).val v =
      ℓ.val (π (characterChangeElement (-1) n) v) := rfl

@[simp] theorem negOneStandardFunctional_apply (ℓ : glInverseFunctionals ψ n π) (v : V) :
    (negOneStandardFunctional ψ π ℓ).val v =
      ℓ.val (π (characterChangeElement (-1) n) v) := rfl

omit [TopologicalSpace F] [IsTopologicalRing F] in
private theorem negOne_translate_twice (v : V) :
    π (characterChangeElement (-1) n) (π (characterChangeElement (-1) n) v) = v := by
  simpa using translate_characterChangeElement_inv π (-1 : Fˣ) v

@[simp] theorem negOneStandardFunctional_inverse (ℓ : glFunctionals ψ n π) :
    negOneStandardFunctional ψ π (negOneInverseFunctional ψ π ℓ) = ℓ := by
  apply Subtype.ext
  ext v
  simp only [negOneStandardFunctional_apply, negOneInverseFunctional_apply,
    negOne_translate_twice]

@[simp] theorem negOneInverseFunctional_standard (ℓ : glInverseFunctionals ψ n π) :
    negOneInverseFunctional ψ π (negOneStandardFunctional ψ π ℓ) = ℓ := by
  apply Subtype.ext
  ext v
  simp only [negOneStandardFunctional_apply, negOneInverseFunctional_apply,
    negOne_translate_twice]

theorem negOneInverseFunctional_ne_zero {ℓ : glFunctionals ψ n π} (hℓ : ℓ.val ≠ 0) :
    (negOneInverseFunctional ψ π ℓ).val ≠ 0 := by
  intro hzero
  apply hℓ
  ext v
  have h := congrArg (fun t : Module.Dual ℂ V =>
    t (π (characterChangeElement (-1) n) v)) hzero
  simpa only [negOneInverseFunctional_apply, negOne_translate_twice,
    LinearMap.zero_apply] using h

theorem negOneStandardFunctional_ne_zero {ℓ : glInverseFunctionals ψ n π} (hℓ : ℓ.val ≠ 0) :
    (negOneStandardFunctional ψ π ℓ).val ≠ 0 := by
  intro hzero
  apply hℓ
  ext v
  have h := congrArg (fun t : Module.Dual ℂ V =>
    t (π (characterChangeElement (-1) n) v)) hzero
  simpa only [negOneStandardFunctional_apply, negOne_translate_twice,
    LinearMap.zero_apply] using h

/-- The corresponding actual coefficient function in the inverse model. -/
def negOneInverseModelVector (ℓ : glFunctionals ψ n π)
    (f : (coefficientModel π ℓ).toSubmodule) :
    (coefficientModel π (negOneInverseFunctional ψ π ℓ)).toSubmodule := by
  refine ⟨⟨fun g => f.val.val (characterChangeElement (-1) n * g), ?_⟩, ?_⟩
  · intro u g
    have h := (characterChangeFunction ψ n (-1) f.val).property u g
    simpa only [characterChangeFunction_apply, standardCharacter_scale_neg_one] using h
  · obtain ⟨v, rfl⟩ := modelMap_surjective π ℓ f
    refine ⟨v, ?_⟩
    apply Subtype.ext
    funext g
    change ℓ.val (π (characterChangeElement (-1) n) (π g v)) =
      ℓ.val (π (characterChangeElement (-1) n * g) v)
    rw [map_mul, Module.End.mul_apply]

/-- The corresponding actual coefficient function in the standard model. -/
def negOneStandardModelVector (ℓ : glInverseFunctionals ψ n π)
    (f : (coefficientModel π ℓ).toSubmodule) :
    (coefficientModel π (negOneStandardFunctional ψ π ℓ)).toSubmodule := by
  refine ⟨⟨fun g => f.val.val (characterChangeElement (-1) n * g), ?_⟩, ?_⟩
  · intro u g
    have h := (characterChangeInverseFunction ψ n (-1) f.val).property u g
    simpa only [characterChangeInverseFunction_apply, inverseStandardCharacter_scale_neg_one] using h
  · obtain ⟨v, rfl⟩ := modelMap_surjective π ℓ f
    refine ⟨v, ?_⟩
    apply Subtype.ext
    funext g
    change ℓ.val (π (characterChangeElement (-1) n) (π g v)) =
      ℓ.val (π (characterChangeElement (-1) n * g) v)
    rw [map_mul, Module.End.mul_apply]

@[simp] theorem negOneInverseModelVector_apply (ℓ : glFunctionals ψ n π)
    (f : (coefficientModel π ℓ).toSubmodule) (g : Langlands.GeneralLinear (n + 1) F) :
    (negOneInverseModelVector ψ π ℓ f).val.val g =
      f.val.val (characterChangeElement (-1) n * g) := rfl

@[simp] theorem negOneStandardModelVector_apply (ℓ : glInverseFunctionals ψ n π)
    (f : (coefficientModel π ℓ).toSubmodule) (g : Langlands.GeneralLinear (n + 1) F) :
    (negOneStandardModelVector ψ π ℓ f).val.val g =
      f.val.val (characterChangeElement (-1) n * g) := rfl

theorem negOneInverseModelVector_surjective (ℓ : glFunctionals ψ n π) :
    Function.Surjective (negOneInverseModelVector ψ π ℓ) := by
  intro f
  obtain ⟨v, rfl⟩ := modelMap_surjective π (negOneInverseFunctional ψ π ℓ) f
  refine ⟨modelMap π ℓ v, ?_⟩
  apply Subtype.ext
  apply Subtype.ext
  funext g
  change ℓ.val (π (characterChangeElement (-1) n * g) v) =
    ℓ.val (π (characterChangeElement (-1) n) (π g v))
  rw [map_mul, Module.End.mul_apply]

theorem negOneStandardModelVector_surjective (ℓ : glInverseFunctionals ψ n π) :
    Function.Surjective (negOneStandardModelVector ψ π ℓ) := by
  intro f
  obtain ⟨v, rfl⟩ := modelMap_surjective π (negOneStandardFunctional ψ π ℓ) f
  refine ⟨modelMap π ℓ v, ?_⟩
  apply Subtype.ext
  apply Subtype.ext
  funext g
  change ℓ.val (π (characterChangeElement (-1) n * g) v) =
    ℓ.val (π (characterChangeElement (-1) n) (π g v))
  rw [map_mul, Module.End.mul_apply]

theorem HasModelMinusOneScalar.negOneInverse {ℓ : glFunctionals ψ n π} {ζ : ℂˣ}
    (hζ : HasModelMinusOneScalar π ℓ ζ) :
    HasModelMinusOneScalar π (negOneInverseFunctional ψ π ℓ) ζ := by
  intro f g
  obtain ⟨f₀, rfl⟩ := negOneInverseModelVector_surjective ψ π ℓ f
  simp only [negOneInverseModelVector_apply]
  have hcomm : characterChangeElement (-1 : Fˣ) n * ((-1) * g) =
      (-1) * (characterChangeElement (-1 : Fˣ) n * g) := by simp
  rw [hcomm, hζ]

theorem HasModelMinusOneScalar.negOneStandard {ℓ : glInverseFunctionals ψ n π} {ζ : ℂˣ}
    (hζ : HasModelMinusOneScalar π ℓ ζ) :
    HasModelMinusOneScalar π (negOneStandardFunctional ψ π ℓ) ζ := by
  intro f g
  obtain ⟨f₀, rfl⟩ := negOneStandardModelVector_surjective ψ π ℓ f
  simp only [negOneStandardModelVector_apply]
  have hcomm : characterChangeElement (-1 : Fˣ) n * ((-1) * g) =
      (-1) * (characterChangeElement (-1 : Fˣ) n * g) := by simp
  rw [hcomm, hζ]

end Langlands.RankinSelberg
