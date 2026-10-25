import Langlands.Representation.Whittaker.FiniteLengthBilinearBounds
import Langlands.Representation.Whittaker.MirabolicFunctionalTransfer
import Langlands.Representation.RankinSelberg.SpectralRescaling
import Langlands.Representation.RankinSelberg.AnalyticStatement

/-! Actual mirabolic specialization and translation of finite spectral exceptions. -/

noncomputable section

namespace Langlands.RankinSelberg

/-- The exceptional spectral points for a predicate evaluated at `s + u`. -/
def shiftedSpectralExceptions (q : ℕ) (hq : 1 < q) (u : ℂ) (E : Finset ℂ) :
    Finset ℂ :=
  E.image (fun z => (↑(spectralShiftUnit q hq u)⁻¹ : ℂ) * z)

theorem not_mem_of_not_mem_shiftedSpectralExceptions
    (q : ℕ) (hq : 1 < q) (u : ℂ) (E : Finset ℂ) (s : ℂ)
    (hs : spectralPoint q s ∉ shiftedSpectralExceptions q hq u E) :
    spectralPoint q (s + u) ∉ E := by
  intro h
  apply hs
  apply Finset.mem_image.mpr
  refine ⟨spectralPoint q (s + u), h, ?_⟩
  rw [spectralPoint_add hq]
  change (↑(spectralShiftUnit q hq u)⁻¹ : ℂ) *
    ((spectralShiftUnit q hq u : ℂ) * spectralPoint q s) = spectralPoint q s
  simp only [← mul_assoc, Units.inv_mul, one_mul]

/-- A finite spectral exception set remains finite under parameter translation. -/
theorem exists_finite_exception_shift
    (q : ℕ) (hq : 1 < q) (u : ℂ) (P : ℂ → Prop)
    (h : ∃ E : Finset ℂ, ∀ s : ℂ, spectralPoint q s ∉ E → P s) :
    ∃ E : Finset ℂ, ∀ s : ℂ, spectralPoint q s ∉ E → P (s + u) := by
  obtain ⟨E, hE⟩ := h
  exact ⟨shiftedSpectralExceptions q hq u E, fun s hs =>
    hE (s + u) (not_mem_of_not_mem_shiftedSpectralExceptions q hq u E s hs)⟩

open Whittaker GeneralLinear InvariantBilinear

universe uF uV uW

/-- Finite mirabolic length and irreducible pair control give the full bilinear
bound for actual restrictions of representations with one-dimensional functionals. -/
theorem mirabolic_exists_exception_length_le_one
    {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData) (n : ℕ)
    {V : Type uV} {W : Type uW}
    [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    (ρ : Representation ℂ (Langlands.GeneralLinear (n + 1) F.Carrier) V)
    (σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F.Carrier) W)
    (θ θ' : GeneralLinear.upperUnipotent (n + 1) F.Carrier →* ℂˣ) :
    letI := T.topology
    letI := T.valuativeRel
    letI := T.localField
    ∀ (_hρ : IsSmooth ρ) (_hσ : IsSmooth σ)
      (_eρ : functionals (GeneralLinear.upperUnipotent (n + 1) F.Carrier) θ ρ ≃ₗ[ℂ] ℂ)
      (_eσ : functionals (GeneralLinear.upperUnipotent (n + 1) F.Carrier) θ' σ ≃ₗ[ℂ] ℂ)
      (_hfinρ : IsFiniteLength (MonoidAlgebra ℂ (mirabolic n F.Carrier))
        (Representation.asModule (ρ.comp (mirabolic n F.Carrier).subtype)))
      (_hfinσ : IsFiniteLength (MonoidAlgebra ℂ (mirabolic n F.Carrier))
        (Representation.asModule (σ.comp (mirabolic n F.Carrier).subtype))),
      (∀ (C : Rep.{uV} ℂ (mirabolic n F.Carrier))
        (D : Rep.{uW} ℂ (mirabolic n F.Carrier)),
        IsSmooth C.ρ → IsSmooth D.ρ →
        Representation.IsIrreducible C.ρ → Representation.IsIrreducible D.ρ →
        ∃ E : Finset ℂ, ∀ s : ℂ, spectralPoint T.residueCardinality s ∉ E →
          (length C.ρ D.ρ
            (fun g => determinantWeight (normalizedAbsoluteValue T) g.val (-s)) ≠ 0 →
            HasFunctional (N := Mirabolic.upperUnipotent n F.Carrier)
              (θ := θ.comp Mirabolic.upperUnipotentEquiv.toMonoidHom) C.ρ ∧
            HasFunctional (N := Mirabolic.upperUnipotent n F.Carrier)
              (θ := θ'.comp Mirabolic.upperUnipotentEquiv.toMonoidHom) D.ρ) ∧
          (HasFunctional (N := Mirabolic.upperUnipotent n F.Carrier)
              (θ := θ.comp Mirabolic.upperUnipotentEquiv.toMonoidHom) C.ρ →
            HasFunctional (N := Mirabolic.upperUnipotent n F.Carrier)
              (θ := θ'.comp Mirabolic.upperUnipotentEquiv.toMonoidHom) D.ρ →
            length C.ρ D.ρ
              (fun g => determinantWeight (normalizedAbsoluteValue T) g.val (-s)) ≤ 1)) →
      ∃ E : Finset ℂ, ∀ s : ℂ, spectralPoint T.residueCardinality s ∉ E →
        length (ρ.comp (mirabolic n F.Carrier).subtype)
          (σ.comp (mirabolic n F.Carrier).subtype)
          (fun g => determinantWeight (normalizedAbsoluteValue T) g.val (-s)) ≤ 1 := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  intro hρ hσ eρ eσ hfinρ hfinσ hpair
  let ρP := ρ.comp (mirabolic n F.Carrier).subtype
  let σP := σ.comp (mirabolic n F.Carrier).subtype
  let U := Mirabolic.upperUnipotent n F.Carrier
  let θP := θ.comp Mirabolic.upperUnipotentEquiv.toMonoidHom
  let θP' := θ'.comp Mirabolic.upperUnipotentEquiv.toMonoidHom
  let eρP : functionals U θP ρP ≃ₗ[ℂ] ℂ :=
    (mirabolicFunctionalsEquiv θ ρ).symm.trans eρ
  let eσP : functionals U θP' σP ≃ₗ[ℂ] ℂ :=
    (mirabolicFunctionalsEquiv θ' σ).symm.trans eσ
  have hρP : IsSmooth ρP := isSmooth_comp _ continuous_subtype_val hρ
  have hσP : IsSmooth σP := isSmooth_comp _ continuous_subtype_val hσ
  have hfunρ : HasFunctional (N := U) (θ := θP) ρP :=
    (functionalLength_ne_zero_iff _ _ _).mp (by
      rw [functionalLength_eq_one_of_equiv _ _ _ eρP]
      exact one_ne_zero)
  have hfunσ : HasFunctional (N := U) (θ := θP') σP :=
    (functionalLength_ne_zero_iff _ _ _).mp (by
      rw [functionalLength_eq_one_of_equiv _ _ _ eσP]
      exact one_ne_zero)
  have hU := Mirabolic.upperUnipotent_isLimitOfCompactSubgroups F T n
  exact exists_exception_length_le_one_of_finiteLength U U hU hU θP θP'
    (character_isLocallyConstant_of_hasFunctional _ _ _ hρP hfunρ)
    (character_isLocallyConstant_of_hasFunctional _ _ _ hσP hfunσ)
    (spectralPoint T.residueCardinality)
    (fun s g => determinantWeight (normalizedAbsoluteValue T) g.val (-s))
    (Rep.of ρP) (Rep.of σP) hρP hσP hfinρ hfinσ eρP eσP hpair

/-- The minus-parameter mirabolic bound supplies the exact Frobenius weight `1-s`. -/
theorem mirabolic_shift_length_bound
    {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData) (n : ℕ)
    {V : Type uV} {W : Type uW}
    [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    (ρ : Representation ℂ (mirabolic n F.Carrier) V)
    (σ : Representation ℂ (mirabolic n F.Carrier) W)
    (h : ∃ E : Finset ℂ, ∀ s : ℂ, spectralPoint T.residueCardinality s ∉ E →
      length ρ σ (fun g => determinantWeight (normalizedAbsoluteValue T) g.val (-s)) ≤ 1) :
    ∃ E : Finset ℂ, ∀ s : ℂ, spectralPoint T.residueCardinality s ∉ E →
      length ρ σ (fun g => determinantWeight (normalizedAbsoluteValue T) g.val (1 - s)) ≤ 1 := by
  have h' := exists_finite_exception_shift T.residueCardinality T.residueCardinality_gt_one
    (-1) (fun s => length ρ σ
      (fun g => determinantWeight (normalizedAbsoluteValue T) g.val (-s)) ≤ 1) h
  simpa only [neg_add_rev, neg_neg, sub_eq_add_neg] using h'

end Langlands.RankinSelberg
