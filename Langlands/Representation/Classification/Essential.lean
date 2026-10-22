import Langlands.Representation.Twist.RealPower
import Langlands.Representation.MatrixCoefficient.ModuloCenter
import Langlands.Representation.Unitary.Basic
import Langlands.Representation.Smooth.Admissibility.EquivalenceProof

/-!
# Explicit real exponents for square-integrability and unitarizability

These constructions record witnesses for actual twisted representations.
They do not select an exponent or assert its existence or uniqueness.
-/

noncomputable section

open scoped NNReal

namespace Langlands

universe uG uV uW

variable {G : Type uG} [Group G]
variable {V : Type uV} [AddCommGroup V] [Module ℂ V]
variable {W : Type uW} [AddCommGroup W] [Module ℂ W]

/-- A real exponent for which removing the positive-character twist gives an
actual invariant positive definite form. -/
structure UnitaryExponentData (ν : G →* ℝ≥0ˣ) (ρ : Representation ℂ G V) where
  exponent : ℝ
  form : InvariantPositiveForm (realPowerTwist ν (-exponent) ρ)

/-- Unitarizability after removing some real power of the specified positive
character. No existence of an exponent is assumed. -/
def IsEssentiallyUnitarizable (ν : G →* ℝ≥0ˣ) (ρ : Representation ℂ G V) : Prop :=
  Nonempty (UnitaryExponentData ν ρ)

namespace UnitaryExponentData

variable {ν : G →* ℝ≥0ˣ} {ρ : Representation ℂ G V}

/-- The normalized representation is the actual negative-exponent twist. -/
def normalized (d : UnitaryExponentData ν ρ) : Representation ℂ G V :=
  realPowerTwist ν (-d.exponent) ρ

theorem normalized_unitarizable (d : UnitaryExponentData ν ρ) :
    IsUnitarizable d.normalized := ⟨d.form⟩

theorem reconstruct (d : UnitaryExponentData ν ρ) :
    realPowerTwist ν d.exponent d.normalized = ρ :=
  realPowerTwist_cancel_neg ν d.exponent ρ

/-- Twisting by `t` adds `t` to the displayed exponent and transports the same
positive form along the proved equality of normalized actions. -/
def shift (d : UnitaryExponentData ν ρ) (t : ℝ) :
    UnitaryExponentData ν (realPowerTwist ν t ρ) where
  exponent := d.exponent + t
  form := by
    have he : -(d.exponent + t) + t = -d.exponent := by ring
    rw [← realPowerTwist_add, he]
    exact d.form

/-- Transport the displayed exponent and form through an actual equivalence. -/
def ofEquiv {σ : Representation ℂ G W} (d : UnitaryExponentData ν ρ)
    (e : ρ.Equiv σ) : UnitaryExponentData ν σ where
  exponent := d.exponent
  form := d.form.ofEquiv (realPowerTwistEquiv ν (-d.exponent) e).symm

end UnitaryExponentData

theorem isEssentiallyUnitarizable_iff_of_equiv (ν : G →* ℝ≥0ˣ)
    {ρ : Representation ℂ G V} {σ : Representation ℂ G W} (e : ρ.Equiv σ) :
    IsEssentiallyUnitarizable ν ρ ↔ IsEssentiallyUnitarizable ν σ := by
  constructor
  · rintro ⟨d⟩
    exact ⟨d.ofEquiv e⟩
  · rintro ⟨d⟩
    exact ⟨d.ofEquiv e.symm⟩

variable [TopologicalSpace G]

namespace UnitaryCentralCharacter

variable {ρ : Representation ℂ G V} {σ : Representation ℂ G W}

/-- Transport the same central character through an equivariant linear equivalence. -/
def ofEquiv (c : UnitaryCentralCharacter ρ) (e : ρ.Equiv σ) :
    UnitaryCentralCharacter σ where
  character := c.character
  isOpen_ker := c.isOpen_ker
  norm_eq_one := c.norm_eq_one
  acts z w := by
    obtain ⟨v, rfl⟩ := e.toLinearEquiv.surjective w
    change σ z (e.toIntertwiningMap v) = _
    rw [← e.toIntertwiningMap.isIntertwining, c.acts, map_smul]
    rfl

theorem coefficientNorm_ofEquiv (c : UnitaryCentralCharacter ρ) (e : ρ.Equiv σ)
    (ℓ : Module.Dual ℂ W) (w : W) :
    (c.ofEquiv e).coefficientNorm ℓ w =
      c.coefficientNorm (ℓ.comp e.toLinearEquiv.toLinearMap) (e.symm w) := by
  funext q
  induction q using Quotient.inductionOn with
  | h g =>
    change ‖ℓ (σ g w)‖ = ‖ℓ (e.toIntertwiningMap (ρ g (e.symm w)))‖
    rw [e.toIntertwiningMap.isIntertwining]
    simp

end UnitaryCentralCharacter

variable [IsTopologicalGroup G]
variable [MeasurableSpace (G ⧸ Subgroup.center G)]
variable [BorelSpace (G ⧸ Subgroup.center G)]

theorem isSquareIntegrableModCenter_of_equiv
    {ρ : Representation ℂ G V} {σ : Representation ℂ G W} (e : ρ.Equiv σ)
    (μ : MeasureTheory.Measure (G ⧸ Subgroup.center G))
    [MeasureTheory.Measure.IsHaarMeasure μ] (hρ : IsSquareIntegrableModCenter ρ μ) :
    IsSquareIntegrableModCenter σ μ := by
  obtain ⟨hρ, c, hc⟩ := hρ
  refine ⟨isAdmissible_of_equiv e hρ, c.ofEquiv e, ?_⟩
  intro ℓ w
  rw [c.coefficientNorm_ofEquiv e]
  exact hc (contragredientMap e.toIntertwiningMap ℓ) (e.symm w)

theorem isSquareIntegrableModCenter_iff_of_equiv
    {ρ : Representation ℂ G V} {σ : Representation ℂ G W} (e : ρ.Equiv σ)
    (μ : MeasureTheory.Measure (G ⧸ Subgroup.center G))
    [MeasureTheory.Measure.IsHaarMeasure μ] :
    IsSquareIntegrableModCenter ρ μ ↔ IsSquareIntegrableModCenter σ μ :=
  ⟨isSquareIntegrableModCenter_of_equiv e μ,
    isSquareIntegrableModCenter_of_equiv e.symm μ⟩

/-- A witness that removing the exponent gives square-integrability of actual
matrix coefficients modulo the center for the specified Haar measure. -/
structure SquareIntegrableExponentData (ν : G →* ℝ≥0ˣ)
    (ρ : Representation ℂ G V)
    (μ : MeasureTheory.Measure (G ⧸ Subgroup.center G))
    [MeasureTheory.Measure.IsHaarMeasure μ] where
  exponent : ℝ
  squareIntegrable : IsSquareIntegrableModCenter (realPowerTwist ν (-exponent) ρ) μ

/-- Square-integrability modulo the center after removing some real power of
the specified positive character. Irreducibility is a separate class restriction. -/
def IsEssentiallySquareIntegrableModCenter (ν : G →* ℝ≥0ˣ)
    (ρ : Representation ℂ G V)
    (μ : MeasureTheory.Measure (G ⧸ Subgroup.center G))
    [MeasureTheory.Measure.IsHaarMeasure μ] : Prop :=
  Nonempty (SquareIntegrableExponentData ν ρ μ)

namespace SquareIntegrableExponentData

variable {ν : G →* ℝ≥0ˣ} {ρ : Representation ℂ G V}
variable {μ : MeasureTheory.Measure (G ⧸ Subgroup.center G)}
variable [MeasureTheory.Measure.IsHaarMeasure μ]

/-- The actual square-integrable negative-exponent twist, on the original module. -/
def normalized (d : SquareIntegrableExponentData ν ρ μ) : Representation ℂ G V :=
  realPowerTwist ν (-d.exponent) ρ

theorem normalized_squareIntegrable (d : SquareIntegrableExponentData ν ρ μ) :
    IsSquareIntegrableModCenter d.normalized μ := d.squareIntegrable

theorem normalized_admissible (d : SquareIntegrableExponentData ν ρ μ) :
    IsAdmissible d.normalized := d.squareIntegrable.1

theorem reconstruct (d : SquareIntegrableExponentData ν ρ μ) :
    realPowerTwist ν d.exponent d.normalized = ρ :=
  realPowerTwist_cancel_neg ν d.exponent ρ

/-- Smoothness of the original action follows when the given positive
character has open kernel; it is not an extra field of the witness. -/
theorem isSmooth (d : SquareIntegrableExponentData ν ρ μ)
    (hν : IsOpen (ν.ker : Set G)) : IsSmooth ρ :=
  (isSmooth_realPowerTwist_iff ν hν (-d.exponent) ρ).mp d.squareIntegrable.1.1

/-- Real twisting adds its exponent, with the normalization equality proved. -/
def shift (d : SquareIntegrableExponentData ν ρ μ) (t : ℝ) :
    SquareIntegrableExponentData ν (realPowerTwist ν t ρ) μ where
  exponent := d.exponent + t
  squareIntegrable := by
    have he : -(d.exponent + t) + t = -d.exponent := by ring
    rw [← realPowerTwist_add, he]
    exact d.squareIntegrable

/-- Transport an exponent witness without changing its real value. -/
def ofEquiv {σ : Representation ℂ G W} (d : SquareIntegrableExponentData ν ρ μ)
    (e : ρ.Equiv σ) : SquareIntegrableExponentData ν σ μ where
  exponent := d.exponent
  squareIntegrable :=
    isSquareIntegrableModCenter_of_equiv (realPowerTwistEquiv ν (-d.exponent) e) μ
      d.squareIntegrable

end SquareIntegrableExponentData

theorem isEssentiallySquareIntegrableModCenter_iff_of_equiv (ν : G →* ℝ≥0ˣ)
    {ρ : Representation ℂ G V} {σ : Representation ℂ G W} (e : ρ.Equiv σ)
    (μ : MeasureTheory.Measure (G ⧸ Subgroup.center G))
    [MeasureTheory.Measure.IsHaarMeasure μ] :
    IsEssentiallySquareIntegrableModCenter ν ρ μ ↔
      IsEssentiallySquareIntegrableModCenter ν σ μ := by
  constructor
  · rintro ⟨d⟩
    exact ⟨d.ofEquiv e⟩
  · rintro ⟨d⟩
    exact ⟨d.ofEquiv e.symm⟩

end Langlands
