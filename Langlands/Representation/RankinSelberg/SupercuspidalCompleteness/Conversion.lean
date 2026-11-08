import Langlands.Representation.Whittaker.GelfandGraev
import Langlands.Representation.RankinSelberg.SupercuspidalProductCompletenessStatement
import Langlands.Representation.RankinSelberg.SupercuspidalCompleteness.CompactGrading

/-!
# Compact Whittaker test functions as vectors of the Gelfand–Graev representation
-/

noncomputable section

namespace Langlands.RankinSelberg.SupercuspidalCompleteness

open GeneralLinear Whittaker Induction HarmonicAnalysis

universe uF

variable {F : Type uF} [Field F] [TopologicalSpace F] [IsTopologicalRing F]

/-- The underlying standard-character Whittaker function of a Gelfand–Graev vector. -/
def toWhittaker (ψ : UnitaryAdditiveCharacter F) (n : ℕ) :
    GelfandGraevFunctions ψ n →ₗ[ℂ] WhittakerFunctions ψ n where
  toFun f := ⟨eval _ _ f.1, fun u g => by
    have h := f.1.1.property u g
    change eval _ _ f.1 ((u : Langlands.GeneralLinear (n + 1) F) * g) =
      (standardCharacter ψ n u : ℂ) • eval _ _ f.1 g at h
    simpa [smul_eq_mul] using h⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp] theorem toWhittaker_apply (ψ : UnitaryAdditiveCharacter F) (n : ℕ)
    (f : GelfandGraevFunctions ψ n) (g : Langlands.GeneralLinear (n + 1) F) :
    (toWhittaker ψ n f).val g = eval _ _ f.1 g := rfl

theorem toWhittaker_injective (ψ : UnitaryAdditiveCharacter F) (n : ℕ) :
    Function.Injective (toWhittaker ψ n) := by
  intro f h hfh
  apply compactFunctions_ext
  intro g
  exact congrArg (fun H : WhittakerFunctions ψ n => H.val g) hfh

/-- Translation commutes with passing to Whittaker functions. -/
theorem toWhittaker_translate (ψ : UnitaryAdditiveCharacter F) (n : ℕ)
    (f : GelfandGraevFunctions ψ n) (s g : Langlands.GeneralLinear (n + 1) F) :
    (toWhittaker ψ n (gelfandGraev ψ n s f)).val g = (toWhittaker ψ n f).val (g * s) := rfl

/-- Every compact Whittaker test function comes from a Gelfand–Graev vector. -/
theorem exists_toWhittaker_eq (ψ : UnitaryAdditiveCharacter F) (n : ℕ)
    (H : WhittakerFunctions ψ n) (hH : IsCompactWhittakerTestFunction ψ n H) :
    ∃ f : GelfandGraevFunctions ψ n, toWhittaker ψ n f = H := by
  obtain ⟨⟨K, hK⟩, ⟨C, hC, hsupp⟩⟩ := hH
  let s : SmoothFunctions (upperUnipotent (n + 1) F) (gelfandGraevCharacterRepresentation ψ n) :=
    smoothFunctionOf _ _ H.val (by
      intro u x
      change H.val ((u : Langlands.GeneralLinear (n + 1) F) * x) =
        (standardCharacter ψ n u : ℂ) • H.val x
      rw [H.property u x, smul_eq_mul]) K (fun k x => hK x k k.property)
  have hcomp : IsCompact (quotientSupport (upperUnipotent (n + 1) F) (eval _ _ s)) := by
    apply (hC.image (continuous_quot_mk)).of_isClosed_subset (isClosed_quotientSupport s)
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨u, c, hc, rfl⟩ := hsupp x hx
    refine ⟨c, hc, ?_⟩
    apply Quotient.sound
    change QuotientGroup.rightRel _ c ((u : Langlands.GeneralLinear (n + 1) F) * c)
    rw [QuotientGroup.rightRel_apply]
    simpa [mul_assoc] using u.property
  exact ⟨⟨s, hcomp⟩, rfl⟩

end Langlands.RankinSelberg.SupercuspidalCompleteness
