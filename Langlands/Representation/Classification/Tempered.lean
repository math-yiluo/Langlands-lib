import Langlands.Representation.Classification.Essential
import Langlands.Group.GL.NormalizedCharacter
import Langlands.Group.GL.Padic
import Mathlib.MeasureTheory.Measure.Haar.Basic

/-!
# Tempered representations modulo the center

An admissible representation is tempered when it has a unitary central character
and all its matrix coefficients lie in `L^(2+ε)(G/Z)` for every `ε > 0`.
For `GL_n` over a p-adic field the predicates below quantify over all Borel Haar
measures of the actual central quotient, so they carry no measure argument.
-/

noncomputable section

open scoped NNReal

namespace Langlands

universe uG uV uW uF

section Generic

variable {G : Type uG} [Group G] [TopologicalSpace G]
variable {V : Type uV} [AddCommGroup V] [Module ℂ V]
variable {W : Type uW} [AddCommGroup W] [Module ℂ W]
variable [MeasurableSpace (G ⧸ Subgroup.center G)]

/-- Temperedness modulo the center for an admissible complex representation and a
specified Haar measure on the actual central quotient: for some unitary central
character, every absolute smooth matrix coefficient lies in `L^(2+ε)` for every
`ε > 0`. -/
def IsTemperedModCenter (ρ : Representation ℂ G V)
    (μ : MeasureTheory.Measure (G ⧸ Subgroup.center G))
    [MeasureTheory.Measure.IsHaarMeasure μ] : Prop :=
  IsAdmissible ρ ∧ ∃ c : UnitaryCentralCharacter ρ,
    ∀ (ℓ : SmoothDual ρ) (v : V) (ε : ℝ), 0 < ε →
      MeasureTheory.MemLp (c.coefficientNorm ℓ v) (ENNReal.ofReal (2 + ε)) μ

theorem IsTemperedModCenter.isAdmissible {ρ : Representation ℂ G V}
    {μ : MeasureTheory.Measure (G ⧸ Subgroup.center G)}
    [MeasureTheory.Measure.IsHaarMeasure μ] (h : IsTemperedModCenter ρ μ) :
    IsAdmissible ρ := h.1

theorem isTemperedModCenter_of_equiv [IsTopologicalGroup G]
    {ρ : Representation ℂ G V} {σ : Representation ℂ G W} (e : ρ.Equiv σ)
    (μ : MeasureTheory.Measure (G ⧸ Subgroup.center G))
    [MeasureTheory.Measure.IsHaarMeasure μ] (hρ : IsTemperedModCenter ρ μ) :
    IsTemperedModCenter σ μ := by
  obtain ⟨hρ, c, hc⟩ := hρ
  refine ⟨isAdmissible_of_equiv e hρ, c.ofEquiv e, ?_⟩
  intro ℓ w ε hε
  rw [c.coefficientNorm_ofEquiv e]
  exact hc (contragredientMap e.toIntertwiningMap ℓ) (e.symm w) ε hε

theorem isTemperedModCenter_iff_of_equiv [IsTopologicalGroup G]
    {ρ : Representation ℂ G V} {σ : Representation ℂ G W} (e : ρ.Equiv σ)
    (μ : MeasureTheory.Measure (G ⧸ Subgroup.center G))
    [MeasureTheory.Measure.IsHaarMeasure μ] :
    IsTemperedModCenter ρ μ ↔ IsTemperedModCenter σ μ :=
  ⟨isTemperedModCenter_of_equiv e μ, isTemperedModCenter_of_equiv e.symm μ⟩

/-- A witness that removing the exponent gives temperedness modulo the center for
the specified Haar measure. -/
structure TemperedExponentData (ν : G →* ℝ≥0ˣ)
    (ρ : Representation ℂ G V)
    (μ : MeasureTheory.Measure (G ⧸ Subgroup.center G))
    [MeasureTheory.Measure.IsHaarMeasure μ] where
  exponent : ℝ
  tempered : IsTemperedModCenter (realPowerTwist ν (-exponent) ρ) μ

/-- Temperedness modulo the center after removing some real power of the specified
positive character. Irreducibility is a separate class restriction. -/
def IsEssentiallyTemperedModCenter (ν : G →* ℝ≥0ˣ)
    (ρ : Representation ℂ G V)
    (μ : MeasureTheory.Measure (G ⧸ Subgroup.center G))
    [MeasureTheory.Measure.IsHaarMeasure μ] : Prop :=
  Nonempty (TemperedExponentData ν ρ μ)

namespace TemperedExponentData

variable {ν : G →* ℝ≥0ˣ} {ρ : Representation ℂ G V}
variable {μ : MeasureTheory.Measure (G ⧸ Subgroup.center G)}
variable [MeasureTheory.Measure.IsHaarMeasure μ]

/-- The actual tempered negative-exponent twist, on the original module. -/
def normalized (d : TemperedExponentData ν ρ μ) : Representation ℂ G V :=
  realPowerTwist ν (-d.exponent) ρ

theorem normalized_tempered (d : TemperedExponentData ν ρ μ) :
    IsTemperedModCenter d.normalized μ := d.tempered

theorem normalized_admissible (d : TemperedExponentData ν ρ μ) :
    IsAdmissible d.normalized := d.tempered.1

theorem reconstruct (d : TemperedExponentData ν ρ μ) :
    realPowerTwist ν d.exponent d.normalized = ρ :=
  realPowerTwist_cancel_neg ν d.exponent ρ

/-- Smoothness of the original action follows when the positive character has open
kernel; it is not an extra field of the witness. -/
theorem isSmooth [IsTopologicalGroup G] (d : TemperedExponentData ν ρ μ)
    (hν : IsOpen (ν.ker : Set G)) : IsSmooth ρ :=
  (isSmooth_realPowerTwist_iff ν hν (-d.exponent) ρ).mp d.tempered.1.1

/-- The zero-exponent witness of a tempered representation. -/
def ofTempered (h : IsTemperedModCenter ρ μ) : TemperedExponentData ν ρ μ where
  exponent := 0
  tempered := by rwa [neg_zero, realPowerTwist_zero]

/-- Real twisting adds its exponent, with the normalization equality proved. -/
def shift (d : TemperedExponentData ν ρ μ) (t : ℝ) :
    TemperedExponentData ν (realPowerTwist ν t ρ) μ where
  exponent := d.exponent + t
  tempered := by
    have he : -(d.exponent + t) + t = -d.exponent := by ring
    rw [← realPowerTwist_add, he]
    exact d.tempered

/-- Transport an exponent witness without changing its real value. -/
def ofEquiv [IsTopologicalGroup G] {σ : Representation ℂ G W}
    (d : TemperedExponentData ν ρ μ)
    (e : ρ.Equiv σ) : TemperedExponentData ν σ μ where
  exponent := d.exponent
  tempered :=
    isTemperedModCenter_of_equiv (realPowerTwistEquiv ν (-d.exponent) e) μ d.tempered

end TemperedExponentData

theorem isEssentiallyTemperedModCenter_iff_of_equiv [IsTopologicalGroup G] (ν : G →* ℝ≥0ˣ)
    {ρ : Representation ℂ G V} {σ : Representation ℂ G W} (e : ρ.Equiv σ)
    (μ : MeasureTheory.Measure (G ⧸ Subgroup.center G))
    [MeasureTheory.Measure.IsHaarMeasure μ] :
    IsEssentiallyTemperedModCenter ν ρ μ ↔ IsEssentiallyTemperedModCenter ν σ μ := by
  constructor
  · rintro ⟨d⟩
    exact ⟨d.ofEquiv e⟩
  · rintro ⟨d⟩
    exact ⟨d.ofEquiv e.symm⟩

end Generic

namespace PadicField.TopologicalData

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p} (T : F.TopologicalData)

/-- The Borel σ-algebra of the actual central quotient `GL_n(F) / Z` for the
topology of `T`. -/
abbrev centralQuotientMeasurableSpace (n : ℕ) :
    MeasurableSpace
      (GeneralLinear n F.Carrier ⧸ Subgroup.center (GeneralLinear n F.Carrier)) :=
  letI := T.topology
  borel _

theorem centralQuotientBorelSpace (n : ℕ) :
    letI := T.topology
    letI := T.centralQuotientMeasurableSpace n
    BorelSpace
      (GeneralLinear n F.Carrier ⧸ Subgroup.center (GeneralLinear n F.Carrier)) := by
  let := T.topology
  let := T.centralQuotientMeasurableSpace n
  exact ⟨rfl⟩

/-- The central quotient carries a Haar measure, so the predicates below, which
quantify over all of them, are not vacuous. -/
theorem exists_isHaarMeasure_centralQuotient (n : ℕ) :
    letI := T.topology
    letI := T.centralQuotientMeasurableSpace n
    ∃ μ : MeasureTheory.Measure
        (GeneralLinear n F.Carrier ⧸ Subgroup.center (GeneralLinear n F.Carrier)),
      μ.IsHaarMeasure := by
  let := T.topology
  have := T.generalLinearTopologicalGroup n
  have := T.generalLinearLocallyCompactSpace n
  let := T.centralQuotientMeasurableSpace n
  have := T.centralQuotientBorelSpace n
  exact ⟨MeasureTheory.Measure.haarMeasure (Classical.arbitrary _), inferInstance⟩

variable {n : ℕ} {V : Type uV} [AddCommGroup V] [Module ℂ V]
variable {W : Type uW} [AddCommGroup W] [Module ℂ W]

/-- Square-integrability of a representation of `GL_n(F)` modulo the center, for
every Borel Haar measure on the actual central quotient. -/
def IsSquareIntegrable (ρ : Representation ℂ (GeneralLinear n F.Carrier) V) : Prop :=
  letI := T.topology
  haveI := T.generalLinearTopologicalGroup n
  letI := T.centralQuotientMeasurableSpace n
  haveI := T.centralQuotientBorelSpace n
  ∀ (μ : MeasureTheory.Measure
      (GeneralLinear n F.Carrier ⧸ Subgroup.center (GeneralLinear n F.Carrier)))
    [MeasureTheory.Measure.IsHaarMeasure μ], IsSquareIntegrableModCenter ρ μ

/-- Temperedness of a representation of `GL_n(F)` modulo the center, for every
Borel Haar measure on the actual central quotient. -/
def IsTempered (ρ : Representation ℂ (GeneralLinear n F.Carrier) V) : Prop :=
  letI := T.topology
  haveI := T.generalLinearTopologicalGroup n
  letI := T.centralQuotientMeasurableSpace n
  haveI := T.centralQuotientBorelSpace n
  ∀ (μ : MeasureTheory.Measure
      (GeneralLinear n F.Carrier ⧸ Subgroup.center (GeneralLinear n F.Carrier)))
    [MeasureTheory.Measure.IsHaarMeasure μ], IsTemperedModCenter ρ μ

/-- `ρ = ν^s ρ₀` with `ρ₀` square-integrable modulo the center, `ν = |det|`. -/
def IsEssentiallySquareIntegrable
    (ρ : Representation ℂ (GeneralLinear n F.Carrier) V) : Prop :=
  ∃ s : ℝ, T.IsSquareIntegrable (realPowerTwist (T.determinantNorm n) (-s) ρ)

/-- `ρ = ν^s ρ₀` with `ρ₀` tempered, `ν = |det|`. -/
def IsEssentiallyTempered (ρ : Representation ℂ (GeneralLinear n F.Carrier) V) : Prop :=
  ∃ s : ℝ, T.IsTempered (realPowerTwist (T.determinantNorm n) (-s) ρ)

variable {T}

theorem IsSquareIntegrable.isAdmissible
    {ρ : Representation ℂ (GeneralLinear n F.Carrier) V} (h : T.IsSquareIntegrable ρ) :
    letI := T.topology
    IsAdmissible ρ := by
  let := T.topology
  have := T.generalLinearTopologicalGroup n
  let := T.centralQuotientMeasurableSpace n
  have := T.centralQuotientBorelSpace n
  obtain ⟨μ, hμ⟩ := T.exists_isHaarMeasure_centralQuotient n
  exact (h μ).1

theorem IsTempered.isAdmissible
    {ρ : Representation ℂ (GeneralLinear n F.Carrier) V} (h : T.IsTempered ρ) :
    letI := T.topology
    IsAdmissible ρ := by
  let := T.topology
  have := T.generalLinearTopologicalGroup n
  let := T.centralQuotientMeasurableSpace n
  have := T.centralQuotientBorelSpace n
  obtain ⟨μ, hμ⟩ := T.exists_isHaarMeasure_centralQuotient n
  exact (h μ).1

theorem isSquareIntegrable_iff_of_equiv
    {ρ : Representation ℂ (GeneralLinear n F.Carrier) V}
    {σ : Representation ℂ (GeneralLinear n F.Carrier) W} (e : ρ.Equiv σ) :
    T.IsSquareIntegrable ρ ↔ T.IsSquareIntegrable σ := by
  let := T.topology
  have := T.generalLinearTopologicalGroup n
  let := T.centralQuotientMeasurableSpace n
  have := T.centralQuotientBorelSpace n
  exact forall_congr' fun μ => forall_congr' fun _ =>
    isSquareIntegrableModCenter_iff_of_equiv e μ

theorem isTempered_iff_of_equiv
    {ρ : Representation ℂ (GeneralLinear n F.Carrier) V}
    {σ : Representation ℂ (GeneralLinear n F.Carrier) W} (e : ρ.Equiv σ) :
    T.IsTempered ρ ↔ T.IsTempered σ := by
  let := T.topology
  have := T.generalLinearTopologicalGroup n
  let := T.centralQuotientMeasurableSpace n
  have := T.centralQuotientBorelSpace n
  exact forall_congr' fun μ => forall_congr' fun _ =>
    isTemperedModCenter_iff_of_equiv e μ

theorem isEssentiallySquareIntegrable_iff_of_equiv
    {ρ : Representation ℂ (GeneralLinear n F.Carrier) V}
    {σ : Representation ℂ (GeneralLinear n F.Carrier) W} (e : ρ.Equiv σ) :
    T.IsEssentiallySquareIntegrable ρ ↔ T.IsEssentiallySquareIntegrable σ :=
  exists_congr fun s =>
    isSquareIntegrable_iff_of_equiv (realPowerTwistEquiv (T.determinantNorm n) (-s) e)

theorem isEssentiallyTempered_iff_of_equiv
    {ρ : Representation ℂ (GeneralLinear n F.Carrier) V}
    {σ : Representation ℂ (GeneralLinear n F.Carrier) W} (e : ρ.Equiv σ) :
    T.IsEssentiallyTempered ρ ↔ T.IsEssentiallyTempered σ :=
  exists_congr fun s =>
    isTempered_iff_of_equiv (realPowerTwistEquiv (T.determinantNorm n) (-s) e)

theorem IsSquareIntegrable.isEssentiallySquareIntegrable
    {ρ : Representation ℂ (GeneralLinear n F.Carrier) V} (h : T.IsSquareIntegrable ρ) :
    T.IsEssentiallySquareIntegrable ρ :=
  ⟨0, by rwa [neg_zero, realPowerTwist_zero]⟩

theorem IsTempered.isEssentiallyTempered
    {ρ : Representation ℂ (GeneralLinear n F.Carrier) V} (h : T.IsTempered ρ) :
    T.IsEssentiallyTempered ρ :=
  ⟨0, by rwa [neg_zero, realPowerTwist_zero]⟩

/-- Twisting by `ν^t` keeps essential square-integrability, adding `t` to the
exponent. -/
theorem IsEssentiallySquareIntegrable.realPowerTwist
    {ρ : Representation ℂ (GeneralLinear n F.Carrier) V}
    (h : T.IsEssentiallySquareIntegrable ρ) (t : ℝ) :
    T.IsEssentiallySquareIntegrable (realPowerTwist (T.determinantNorm n) t ρ) := by
  obtain ⟨s, hs⟩ := h
  refine ⟨s + t, ?_⟩
  have he : -(s + t) + t = -s := by ring
  rw [← realPowerTwist_add, he]
  exact hs

/-- Twisting by `ν^t` keeps essential temperedness, adding `t` to the exponent. -/
theorem IsEssentiallyTempered.realPowerTwist
    {ρ : Representation ℂ (GeneralLinear n F.Carrier) V}
    (h : T.IsEssentiallyTempered ρ) (t : ℝ) :
    T.IsEssentiallyTempered (realPowerTwist (T.determinantNorm n) t ρ) := by
  obtain ⟨s, hs⟩ := h
  refine ⟨s + t, ?_⟩
  have he : -(s + t) + t = -s := by ring
  rw [← realPowerTwist_add, he]
  exact hs

end PadicField.TopologicalData

end Langlands
