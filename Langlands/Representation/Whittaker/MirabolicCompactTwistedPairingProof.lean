import Langlands.Representation.Whittaker.MirabolicPairingStatement
import Langlands.Representation.Whittaker.MirabolicCompactAdapters
import Langlands.Representation.Whittaker.MirabolicCompactWhittakerUniqueness
import Langlands.Representation.Whittaker.MirabolicQuotientMeasure
import Langlands.Representation.Induction.CompactFormsFunctional
import Langlands.Representation.Whittaker.GeneralLinear
import Langlands.Group.GL.CompactOpen
import Langlands.Group.GL.Padic
import Langlands.Group.GL.NormalizedCharacter
import Langlands.LocalField.Topology

/-!
# The compact mirabolic twisted pairing is one-dimensional

For a p-adic field, every unitary additive character `ψ`, every rank `n` and
every `s : ℂ`, the space of bilinear forms `B` on the actual compact mirabolic
model with `B (τ g f₁) (τ g f₂) = |det g|^(-s) B f₁ f₂` is linearly equivalent to `ℂ`.
-/

noncomputable section

namespace Langlands.Whittaker

open MeasureTheory GeneralLinear GeneralLinear.Mirabolic HarmonicAnalysis Induction
  QuotientIntegration
open scoped ENNReal

universe uF

namespace MirabolicCompactTwistedPairing

/-- A space with a nonzero vector and an injective linear functional is a line. -/
theorem nonempty_linearEquiv_complex {X : Type*} [AddCommGroup X] [Module ℂ X]
    (L : X →ₗ[ℂ] ℂ) (hL : Function.Injective L) {x : X} (hx : x ≠ 0) :
    Nonempty (X ≃ₗ[ℂ] ℂ) := by
  have hLx : L x ≠ 0 := fun h => hx (hL (h.trans (map_zero L).symm))
  refine ⟨LinearEquiv.ofBijective L ⟨hL, fun c => ⟨(c / L x) • x, ?_⟩⟩⟩
  rw [map_smul, smul_eq_mul, div_mul_cancel₀ c hLx]

/-- A scalar character with open kernel is a smooth representation. -/
theorem isSmooth_characterRepresentation {H : Type*} [Group H] [TopologicalSpace H]
    (θ : H →* ℂˣ) (hθ : IsOpen (θ.ker : Set H)) : IsSmooth (characterRepresentation θ) :=
  fun v => ⟨⟨θ.ker, hθ⟩, by
    rw [fixedVectors, Representation.mem_invariants]
    intro k
    change (θ k.val : ℂ) • v = v
    rw [MonoidHom.mem_ker.mp k.property, Units.val_one, one_smul]⟩

section Generic

variable {F : Type uF} [Field F] [TopologicalSpace F] [IsTopologicalDivisionRing F]

/-- The standard character of `ψ.scale (-1)` is the inverse of that of `ψ`. -/
theorem mirabolicCharacter_scale_neg_one_mul (ψ : UnitaryAdditiveCharacter F) (n : ℕ)
    (u : Mirabolic.upperUnipotent n F) :
    (mirabolicCharacter (ψ.scale (-1)) n u : ℂ) * mirabolicCharacter ψ n u = 1 := by
  rw [mirabolicCharacter_eq_product, mirabolicCharacter_eq_product, ← Finset.prod_mul_distrib]
  refine Finset.prod_eq_one fun i _ => ?_
  change ψ.complex ((↑(-1 : Fˣ) : F) * _) * ψ.complex _ = 1
  rw [← AddChar.map_add_eq_mul, Units.val_neg, Units.val_one, neg_one_mul, neg_add_cancel,
    AddChar.map_zero_eq_one]

variable [T2Space F] [NonarchimedeanAddGroup F]
  [∀ m, NonarchimedeanGroup (Langlands.GeneralLinear m F)]
  [∀ m, LocallyCompactSpace (Langlands.GeneralLinear m F)]

/-- Invariant forms pairing the compact model of `ψ` with that of `ψ.scale (-1)` form a
line, given a right-invariant quotient measure with positive finite orbit masses. -/
theorem nonempty_oppositeForms_equiv (ψ : UnitaryAdditiveCharacter F) (n : ℕ)
    (hker : IsOpen ((mirabolicCharacter ψ n).ker : Set (Mirabolic.upperUnipotent n F)))
    [MeasurableSpace (QuotientIntegration.LeftQuotient (Mirabolic.upperUnipotent n F))]
    [BorelSpace (QuotientIntegration.LeftQuotient (Mirabolic.upperUnipotent n F))]
    (ν : Measure (QuotientIntegration.LeftQuotient (Mirabolic.upperUnipotent n F)))
    [IsFiniteMeasureOnCompacts ν]
    (hinv : ∀ g : mirabolic n F, MeasurePreserving (rightTranslate _ g) ν ν)
    (hmass : ∀ J : OpenSubgroup (mirabolic n F), IsCompact (J : Set (mirabolic n F)) →
      0 < ν (compactOpenQuotientOrbit _ J) ∧ ν (compactOpenQuotientOrbit _ J) < ⊤) :
    Nonempty (InvariantBilinear.forms (mirabolicCompactInduced ψ n)
      (mirabolicCompactInduced (ψ.scale (-1)) n) (fun _ => (1 : ℂ)) ≃ₗ[ℂ] ℂ) := by
  have : NonarchimedeanGroup (mirabolic n F) := MirabolicWhittaker.mirabolic_nonarchimedean
  have : LocallyCompactSpace (mirabolic n F) := Mirabolic.locallyCompactSpace
  have hG : ∀ O : Set (mirabolic n F), IsOpen O → (1 : mirabolic n F) ∈ O →
      ∃ K : OpenSubgroup (mirabolic n F), IsCompact (K : Set (mirabolic n F)) ∧
        (K : Set (mirabolic n F)) ⊆ O :=
    fun O hO h1 => compactOpenSubgroupBasis _ O (hO.mem_nhds h1)
  have hσ := isSmooth_characterRepresentation _ hker
  have hθ' := mirabolicCharacter_scale_neg_one_mul ψ n
  obtain ⟨L, hL⟩ := FormsFunctional.exists_injective_formsFunctional hG
    (Mirabolic.upperUnipotent n F) Mirabolic.upperUnipotent_isClosed (mirabolicCharacter ψ n) hσ
    (mirabolicCompactInduced (ψ.scale (-1)) n) (compactInduced_smooth _ _) ν hinv hmass
    (mirabolicCharacter (ψ.scale (-1)) n) hθ'

  have hB := FormsFunctional.exists_standardForm hG (Mirabolic.upperUnipotent n F)
    (mirabolicCharacter ψ n) (mirabolicCharacter (ψ.scale (-1)) n) hσ hθ' ν hinv hmass

  have ht := MirabolicWhittaker.exists_testVector (ψ.scale (-1))
    (MirabolicWhittaker.isOpen_complex_eq_one _) n
  let E : MirabolicWhittaker.compactFunctionals (ψ.scale (-1)) n →ₗ[ℂ] ℂ :=
    (LinearMap.applyₗ ht.choose).comp (Submodule.subtype _)
  have hE : Function.Injective E := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro ℓ hℓ
    exact Subtype.ext (ht.choose_spec ℓ.val ℓ.property hℓ)
  exact nonempty_linearEquiv_complex (E.comp L) (hE.comp hL) (x := ⟨hB.choose, hB.choose_spec.1⟩)
    (fun h0 => hB.choose_spec.2 (congrArg Subtype.val h0))

end Generic

/-- A field with a valuative topology is a nonarchimedean additive group. -/
private theorem valuative_nonarchimedean {K : Type*} [Field K]
    [TopologicalSpace K] [ValuativeRel K] [IsValuativeTopology K] :
    NonarchimedeanAddGroup K where
  is_nonarchimedean U hU := by
    obtain ⟨S, hS, hSU⟩ :=
      (IsLinearTopology.hasBasis_open_submodule
        (ValuativeRel.valuation K).integer (M := K)).mem_iff.mp hU
    exact ⟨⟨S.toAddSubgroup, hS⟩, hSU⟩

/-- The normalized absolute value of a supplied p-adic realization is one on an open
subgroup of units. -/
theorem isOpenNormOne_normalizedAbsoluteValue {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p}
    (T : F.TopologicalData) :
    letI := T.topology
    Shahidi.IsOpenNormOne (RankinSelberg.normalizedAbsoluteValue T) := by
  let := T.topology
  have he : ((Shahidi.absUnits (RankinSelberg.normalizedAbsoluteValue T)).ker : Set F.Carrierˣ) =
      T.normalizedAbsUnits.ker := by
    ext a
    simp only [SetLike.mem_coe, MonoidHom.mem_ker]
    rw [← Units.val_inj, ← Units.val_inj, ← NNReal.coe_inj, ← NNReal.coe_inj]
    exact Iff.rfl
  rw [Shahidi.IsOpenNormOne, he]
  exact T.isOpen_ker_normalizedAbsUnits

end MirabolicCompactTwistedPairing

open MirabolicCompactTwistedPairing

/-- The actual compact mirabolic twisted pairing is one-dimensional. -/
theorem mirabolicCompactTwistedPairing {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)
    (T : F.TopologicalData) (n : ℕ) : MirabolicCompactTwistedPairingStatement.{uF} F T n := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  have := T.fieldT2
  have := valuative_nonarchimedean (K := F.Carrier)
  have : ∀ m, NonarchimedeanGroup (Langlands.GeneralLinear m F.Carrier) :=
    T.generalLinearNonarchimedean
  have : ∀ m, LocallyCompactSpace (Langlands.GeneralLinear m F.Carrier) :=
    T.generalLinearLocallyCompactSpace
  intro ψ s
  have hstd : IsOpen ((standardCharacter ψ n).ker :
      Set (GeneralLinear.upperUnipotent (n + 1) F.Carrier)) := by
    have := T.upperUnipotentNonarchimedean (n + 1)
    exact isOpen_ker_of_continuous_complex_character _ (standardCharacterContinuous ψ n).continuous
  have hker : IsOpen ((mirabolicCharacter ψ n).ker : Set (Mirabolic.upperUnipotent n F.Carrier)) :=
    hstd.preimage Mirabolic.upperUnipotentContinuousEquiv.continuous
  let : MeasurableSpace (QuotientIntegration.LeftQuotient
    (Mirabolic.upperUnipotent n F.Carrier)) := borel _
  have : BorelSpace (QuotientIntegration.LeftQuotient
    (Mirabolic.upperUnipotent n F.Carrier)) := ⟨rfl⟩
  have hν := MirabolicQuotient.exists_measure (F := F.Carrier) n
  have := hν.choose_spec.1
  let eX := (nonempty_oppositeForms_equiv ψ n hker hν.choose hν.choose_spec.2.1
    hν.choose_spec.2.2).some
  exact ⟨(mirabolicFormsDeterminantShift (isOpenNormOne_normalizedAbsoluteValue T) ψ n
    (mirabolicCompactInduced ψ n) (-s) _ (fun _ => (1 : ℂ)) (fun _ => (mul_one _).symm)).trans
    ((InvariantBilinear.equivRight _ _ (mirabolicCharacterChangeEquiv ψ (-1) n)).trans eX)⟩

end Langlands.Whittaker
