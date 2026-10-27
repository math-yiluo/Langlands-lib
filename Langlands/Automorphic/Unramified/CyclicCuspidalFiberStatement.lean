import Langlands.Automorphic.CuspidalSpectralPresentation
import Langlands.Automorphic.FiniteOrderDeterminantTwist
import Langlands.Representation.Unramified.WeakTransfer
import Mathlib.FieldTheory.Galois.Basic
import Mathlib.GroupTheory.SpecificGroups.Cyclic

/-! # The direct cyclic cuspidal fiber statement of Arthur--Clozel

The premise compares two supplied genuine downstairs spectra using actual
residue degrees. The conclusion retains triviality on the actual extension
norm and the finite, compact and full enveloping actions of the twist.
-/

noncomputable section

open scoped NumberField

universe uF uE uS uT

namespace Langlands.Unramified.SpectralSystem

open Langlands.Global Langlands.Global.AdelicFunctoriality

variable {F : Type uF} [Field F] {n : ℕ}

/-- The residue-degree powers of two downstairs spectra agree outside one
finite base set, where both spectra and every place above are unramified. -/
def SameResidueDegreePowers (E : Type uE) [Field E] [NumberField E] [Algebra F E]
    (s t : SpectralSystem (FinitePlace F) n) : Prop :=
  ∀ᶠ v in Filter.cofinite,
    ∃ (hs : v ∉ s.exceptional) (ht : v ∉ t.exceptional),
      ∀ w : FinitePlacesAbove E v,
        w.1.asIdeal.ramificationIdx (𝓞 F) = 1 ∧
          (s.eigenvalues v hs).power (w.1.asIdeal.inertiaDeg (𝓞 F)) =
            (t.eigenvalues v ht).power (w.1.asIdeal.inertiaDeg (𝓞 F))

variable {E : Type uE} [Field E] [NumberField E] [Algebra F E]

/-- Removing the two finite exceptional sets makes the guarded formulation
equivalent to explicit simultaneous definedness. -/
theorem sameResidueDegreePowers_iff_guarded
    (s t : SpectralSystem (FinitePlace F) n) :
    SameResidueDegreePowers E s t ↔
      ∀ᶠ v in Filter.cofinite,
        ∀ (hs : v ∉ s.exceptional) (ht : v ∉ t.exceptional)
          (w : FinitePlacesAbove E v),
          w.1.asIdeal.ramificationIdx (𝓞 F) = 1 ∧
            (s.eigenvalues v hs).power (w.1.asIdeal.inertiaDeg (𝓞 F)) =
              (t.eigenvalues v ht).power (w.1.asIdeal.inertiaDeg (𝓞 F)) := by
  constructor
  · intro h
    exact h.mono fun _ ⟨_, _, hw⟩ _ _ w => hw w
  · intro h
    filter_upwards [h, s.exceptional.eventually_cofinite_notMem,
      t.exceptional.eventually_cofinite_notMem] with v hv hs ht
    exact ⟨hs, ht, hv hs ht⟩

theorem SameResidueDegreePowers.symm
    {s t : SpectralSystem (FinitePlace F) n}
    (h : SameResidueDegreePowers E s t) : SameResidueDegreePowers E t s :=
  h.mono fun _ ⟨hs, ht, hw⟩ => ⟨ht, hs, fun w => ⟨(hw w).1, (hw w).2.symm⟩⟩

/-- Two weak comparisons with the same supplied upstairs system give the direct
downstairs power comparison. No presentation-uniqueness assertion is used. -/
theorem SameResidueDegreePowers.of_common_weakBaseChange
    {s t : SpectralSystem (FinitePlace F) n}
    {a : SpectralSystem (FinitePlace E) n}
    (hs : a.IsArithmeticWeakBaseChangeOf s)
    (ht : a.IsArithmeticWeakBaseChangeOf t) :
    SameResidueDegreePowers E s t := by
  filter_upwards [hs, ht] with v hv hv'
  rcases hv with ⟨hs, _, he, hes⟩
  rcases hv' with ⟨ht, _, _, het⟩
  exact ⟨hs, ht, fun w => ⟨he w, (hes w).symm.trans (het w)⟩⟩

end Langlands.Unramified.SpectralSystem

namespace Langlands.Automorphic.Unramified

open Langlands.Global Langlands.Unramified

/-- AC89 III.3.1 for actual full cuspidal classes with supplied genuine
spectral systems. The extension has arbitrary cyclic degree. -/
def CyclicCuspidalFiberStatement : Prop :=
  ∀ (F : Type uF) (E : Type uE) [Field F] [NumberField F]
    [Field E] [NumberField E] [Algebra F E]
    [IsGalois F E] [IsCyclic (E ≃ₐ[F] E)] [CompactSpace (AdeleQuotient F)]
    (r : ℕ) (c d : CuspidalOperatorRealization.IsoClass F r)
    (s t : SpectralSystem (FinitePlace F) (r + 1)),
    CuspidalOperatorRealization.IsoClass.HasSpectralSystem.{uF, uS} c s →
    CuspidalOperatorRealization.IsoClass.HasSpectralSystem.{uF, uT} d t →
    SpectralSystem.SameResidueDegreePowers E s t →
    ∃ χ : HeckeCharacter F, χ.IsTrivialOnNorm E ∧
      CuspidalOperatorRealization.IsoClass.IsFiniteOrderDeterminantTwist χ c d

/-- Conditional application of III.3.1 when the two downstairs presentations
have a common supplied numerical weak base change. -/
theorem CyclicCuspidalFiberStatement.of_common_weakBaseChange
    (h : CyclicCuspidalFiberStatement.{uF, uE, uS, uT})
    (F : Type uF) (E : Type uE) [Field F] [NumberField F]
    [Field E] [NumberField E] [Algebra F E]
    [IsGalois F E] [IsCyclic (E ≃ₐ[F] E)] [CompactSpace (AdeleQuotient F)]
    (r : ℕ) (c d : CuspidalOperatorRealization.IsoClass F r)
    (s t : SpectralSystem (FinitePlace F) (r + 1))
    (a : SpectralSystem (FinitePlace E) (r + 1))
    (hc : CuspidalOperatorRealization.IsoClass.HasSpectralSystem.{uF, uS} c s)
    (hd : CuspidalOperatorRealization.IsoClass.HasSpectralSystem.{uF, uT} d t)
    (hs : a.IsArithmeticWeakBaseChangeOf s)
    (ht : a.IsArithmeticWeakBaseChangeOf t) :
    ∃ χ : HeckeCharacter F, χ.IsTrivialOnNorm E ∧
      CuspidalOperatorRealization.IsoClass.IsFiniteOrderDeterminantTwist χ c d :=
  h F E r c d s t hc hd
    (SpectralSystem.SameResidueDegreePowers.of_common_weakBaseChange hs ht)

end Langlands.Automorphic.Unramified
