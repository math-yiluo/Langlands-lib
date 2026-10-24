import Langlands.ClassField.Global.IdeleCohomology
import Langlands.ClassField.Global.LocalUnitCohomology
import Mathlib.Data.Finsupp.Basic

/-! # The finite divisor of an actual idele -/

noncomputable section

universe u

namespace Langlands.ClassField.Global

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
open scoped NumberField
open Langlands.Global.AdelicFunctoriality

variable (E : Type u) [Field E] [NumberField E]

/-- Finite divisors supported on the finite places of a number field. -/
abbrev FinitePlaceDivisor := HeightOneSpectrum (𝓞 E) →₀ ℤ

variable {E}

/-- The usual additive order at a finite place, positive on a uniformizer. -/
def ideleOrder (w : HeightOneSpectrum (𝓞 E)) (x : IdeleGroup (𝓞 E) E) : ℤ :=
  -Multiplicative.toAdd (unitsExponent w (ideleCoordinate w x))

@[simp] theorem ideleOrder_one (w : HeightOneSpectrum (𝓞 E)) :
    ideleOrder w (1 : IdeleGroup (𝓞 E) E) = 0 := by
  simp [ideleOrder]

@[simp] theorem ideleOrder_mul (w : HeightOneSpectrum (𝓞 E))
    (x y : IdeleGroup (𝓞 E) E) :
    ideleOrder w (x * y) = ideleOrder w x + ideleOrder w y := by
  simp [ideleOrder, add_comm]

/-- Order zero is exactly membership in the local valuation-unit group. -/
theorem ideleOrder_eq_zero_iff (w : HeightOneSpectrum (𝓞 E))
    (x : IdeleGroup (𝓞 E) E) :
    ideleOrder w x = 0 ↔ Valued.v (ideleCoordinate w x : w.adicCompletion E) = 1 := by
  simp only [ideleOrder, neg_eq_zero]
  change unitsExponent w (ideleCoordinate w x) = 1 ↔ _
  exact unitsExponent_eq_one_iff w _

/-- An idele has nonzero order at only finitely many finite places. -/
theorem ideleOrder_finite_support (x : IdeleGroup (𝓞 E) E) :
    (Function.support (fun w => ideleOrder w x)).Finite := by
  let xf : (FiniteAdeleRing (𝓞 E) E)ˣ :=
    Units.map (RingHom.snd (InfiniteAdeleRing E) (FiniteAdeleRing (𝓞 E) E)).toMonoidHom x
  have h := FiniteAdeleRing.hasFiniteMulSupport_valued xf
  apply h.subset
  intro w hw
  change Valued.v (ideleCoordinate w x : w.adicCompletion E) ≠ 1
  exact fun hv => hw ((ideleOrder_eq_zero_iff w x).2 hv)

/-- The finite divisor of an idele, with its usual order convention. -/
def ideleDivisor (x : IdeleGroup (𝓞 E) E) : FinitePlaceDivisor E :=
  Finsupp.ofSupportFinite (fun w => ideleOrder w x) (ideleOrder_finite_support x)

@[simp] theorem ideleDivisor_apply (x : IdeleGroup (𝓞 E) E)
    (w : HeightOneSpectrum (𝓞 E)) : ideleDivisor x w = ideleOrder w x := rfl

@[simp] theorem ideleDivisor_one : ideleDivisor (1 : IdeleGroup (𝓞 E) E) = 0 := by
  ext w
  exact ideleOrder_one w

@[simp] theorem ideleDivisor_mul (x y : IdeleGroup (𝓞 E) E) :
    ideleDivisor (x * y) = ideleDivisor x + ideleDivisor y := by
  ext w
  exact ideleOrder_mul w x y

variable (E)

/-- The idele divisor map as a homomorphism to multiplicatively tagged divisors. -/
def ideleDivisorHom : IdeleGroup (𝓞 E) E →* Multiplicative (FinitePlaceDivisor E) where
  toFun x := Multiplicative.ofAdd (ideleDivisor x)
  map_one' := ideleDivisor_one
  map_mul' := ideleDivisor_mul

variable {E}

/-- The divisor kernel is exactly the ideles integral and invertible at every finite place. -/
theorem ideleDivisor_eq_zero_iff (x : IdeleGroup (𝓞 E) E) :
    ideleDivisor x = 0 ↔
      ∀ w : HeightOneSpectrum (𝓞 E), Valued.v (ideleCoordinate w x : w.adicCompletion E) = 1 := by
  rw [Finsupp.ext_iff]
  exact forall_congr' fun w => ideleOrder_eq_zero_iff w x

/-- A single local component contributes a single divisor coefficient. -/
theorem ideleDivisor_ofAdicCompletion (w : HeightOneSpectrum (𝓞 E))
    (a : (w.adicCompletion E)ˣ) :
    ideleDivisor (IdeleGroup.ofAdicCompletion (𝓞 E) E w a) =
      Finsupp.single w (-Multiplicative.toAdd (unitsExponent w a)) := by
  classical
  ext q
  by_cases h : q = w
  · subst q
    simp [ideleOrder]
  · simp [ideleOrder, ideleCoordinate_ofAdicCompletion_of_ne h, Finsupp.single_eq_of_ne h]

/-- Each prime divisor with arbitrary integer multiplicity comes from an idele. -/
theorem exists_ideleDivisor_single (w : HeightOneSpectrum (𝓞 E)) (n : ℤ) :
    ∃ x : IdeleGroup (𝓞 E) E, ideleDivisor x = Finsupp.single w n := by
  obtain ⟨a, ha⟩ := unitsExponent_surjective w (Multiplicative.ofAdd (-n))
  refine ⟨IdeleGroup.ofAdicCompletion (𝓞 E) E w a, ?_⟩
  rw [ideleDivisor_ofAdicCompletion, ha]
  simp

variable (E)

/-- Every finite divisor is the divisor of an idele. -/
theorem ideleDivisor_surjective : Function.Surjective (ideleDivisor (E := E)) := by
  intro d
  induction d using Finsupp.induction with
  | zero => exact ⟨1, ideleDivisor_one⟩
  | @single_add w n d hw hn ih =>
    obtain ⟨x, hx⟩ := exists_ideleDivisor_single w n
    obtain ⟨y, hy⟩ := ih
    exact ⟨x * y, by rw [ideleDivisor_mul, hx, hy]⟩

end Langlands.ClassField.Global
