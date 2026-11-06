import Langlands.HarmonicAnalysis.PadicAdditiveCharacterSelfDuality
import Langlands.Representation.Whittaker.CharacterChange
import Langlands.Group.GL.Padic

/-! # Independence of p-adic Whittaker genericity from the additive character -/

noncomputable section

namespace Langlands.HarmonicAnalysis

/-- An additive character trivial on an open subgroup is locally constant. -/
theorem isLocallyConstant_addChar_of_open_subgroup
    {A M : Type*} [AddGroup A] [TopologicalSpace A] [IsTopologicalAddGroup A]
    [Monoid M] (χ : AddChar A M) (H : AddSubgroup A)
    (hH : IsOpen (H : Set A)) (hχ : ∀ x ∈ H, χ x = 1) :
    IsLocallyConstant χ := by
  apply (IsLocallyConstant.iff_exists_open _).mpr
  intro x
  refine ⟨(fun y : A => y - x) ⁻¹' (H : Set A),
    hH.preimage (continuous_id.sub continuous_const), ?_, ?_⟩
  · simp
  · intro y hy
    calc
      χ y = χ ((y - x) + x) := by rw [sub_add_cancel]
      _ = χ (y - x) * χ x := χ.map_add_eq_mul _ _
      _ = χ x := by rw [hχ _ hy, one_mul]

end Langlands.HarmonicAnalysis

namespace Langlands.PadicField.TopologicalData

open HarmonicAnalysis

universe uF uV
variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p} (T : F.TopologicalData)

local notation "AdditiveCharacter" =>
  @UnitaryAdditiveCharacter F.Carrier _ T.topology

/-- Every continuous unitary additive character is locally constant. -/
theorem isLocallyConstant_unitaryAdditiveCharacter
    (ψ : AdditiveCharacter) :
    letI := T.topology
    IsLocallyConstant ψ := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  obtain ⟨k, hk⟩ := T.exists_additiveTrivialAt ψ
  exact isLocallyConstant_addChar_of_open_subgroup ψ.toAddChar (T.additiveLattice k)
    (T.isOpen_additiveLattice k) hk

/-- A nontrivial raw character trivial on the integers, with its proved continuity. -/
def unitaryAdditiveCharacterOfTrivialOnIntegers
    (χ : AddChar F.Carrier Circle) (hχ : χ ≠ 1)
    (hO : ∀ x ∈ T.Integers, χ x = 1) : AdditiveCharacter := by
  letI := T.topology
  letI := T.valuativeRel
  letI := T.localField
  exact {
    toAddChar := χ
    nontrivial := hχ
    continuous_toFun := (isLocallyConstant_addChar_of_open_subgroup χ (T.additiveLattice 0)
      (T.isOpen_additiveLattice 0)
      (fun x hx => hO x ((T.mem_additiveLattice_zero x).mp hx))).continuous
  }

@[simp]
theorem unitaryAdditiveCharacterOfTrivialOnIntegers_apply
    (χ : AddChar F.Carrier Circle) (hχ : χ ≠ 1)
    (hO : ∀ x ∈ T.Integers, χ x = 1) (x : F.Carrier) :
    T.unitaryAdditiveCharacterOfTrivialOnIntegers χ hχ hO x = χ x := rfl

/-- Any two continuous nontrivial additive characters differ by a unit scalar. -/
theorem exists_unit_scale_eq (ψ χ : AdditiveCharacter) :
    letI := T.topology
    letI := T.valuativeRel
    letI := T.localField
    ∃ a : F.Carrierˣ, ψ.scale a = χ := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  have hχ : IsLocallyConstant χ.complex :=
    (T.isLocallyConstant_unitaryAdditiveCharacter χ).comp (fun z : Circle => (z : ℂ))
  obtain ⟨a, ha⟩ := T.exists_eq_complex_mul_of_isLocallyConstant ψ χ.complex hχ
  have ha0 : a ≠ 0 := by
    intro hzero
    apply χ.nontrivial
    apply AddChar.ext
    intro x
    apply Subtype.ext
    have h := ha x
    simpa [hzero] using h
  refine ⟨Units.mk0 a ha0, ?_⟩
  apply UnitaryAdditiveCharacter.ext
  intro x
  apply Subtype.ext
  exact (ha x).symm

variable {n : ℕ} {V : Type uV} [AddCommGroup V] [Module ℂ V]
variable (ρ : Representation ℂ (Langlands.GeneralLinear (n + 1) F.Carrier) V)

/-- The actual functional spaces for any two continuous nontrivial characters
are linearly equivalent on the same representation and carrier. -/
def whittakerCharacterEquiv (ψ χ : AdditiveCharacter) :
    letI := T.topology
    Whittaker.glFunctionals ψ n ρ ≃ₗ[ℂ] Whittaker.glFunctionals χ n ρ := by
  letI := T.topology
  letI := T.valuativeRel
  letI := T.localField
  let a := Classical.choose (T.exists_unit_scale_eq ψ χ)
  have ha : ψ.scale a = χ := Classical.choose_spec (T.exists_unit_scale_eq ψ χ)
  exact ha ▸ Whittaker.characterChangeFunctionalEquiv ψ ρ a

/-- Nonzero functional existence is independent of the additive character. -/
theorem hasFunctional_iff_character (ψ χ : AdditiveCharacter) :
    letI := T.topology
    Whittaker.HasFunctional (N := GeneralLinear.upperUnipotent (n + 1) F.Carrier)
      (θ := Whittaker.standardCharacter ψ n) ρ ↔
    Whittaker.HasFunctional (N := GeneralLinear.upperUnipotent (n + 1) F.Carrier)
      (θ := Whittaker.standardCharacter χ n) ρ := by
  let := T.topology
  let e := T.whittakerCharacterEquiv ρ ψ χ
  constructor
  · rintro ⟨ℓ, hℓ⟩
    refine ⟨e ℓ, fun h => hℓ ?_⟩
    exact congrArg Subtype.val (e.map_eq_zero_iff.mp (Subtype.ext h))
  · rintro ⟨ℓ, hℓ⟩
    refine ⟨e.symm ℓ, fun h => hℓ ?_⟩
    exact congrArg Subtype.val (e.symm.map_eq_zero_iff.mp (Subtype.ext h))

/-- Genericity for the supplied matrix topology is independent of the character. -/
theorem isGeneric_iff_character (ψ χ : AdditiveCharacter) :
    letI := T.topology
    letI := T.generalLinearTopology (n + 1)
    Whittaker.IsGeneric ψ n ρ ↔ Whittaker.IsGeneric χ n ρ := by
  let := T.topology
  let := T.generalLinearTopology (n + 1)
  exact and_congr_right fun _ => and_congr_right fun _ => T.hasFunctional_iff_character ρ ψ χ

/-- A nonzero functional for any nontrivial integer-trivial raw character gives
Whittaker genericity for every continuous nontrivial additive character. -/
theorem isGeneric_of_functional_trivialOnIntegers
    (χ : AddChar F.Carrier Circle) (hχ : χ ≠ 1)
    (hO : ∀ x ∈ T.Integers, χ x = 1)
    (ℓ : Module.Dual ℂ V) (hℓ : ℓ ≠ 0)
    (heq : ∀ (u : GeneralLinear.upperUnipotent (n + 1) F.Carrier) (x : V),
      ℓ (ρ u.val x) = (χ (∑ i : Fin n, u.val i.castSucc i.succ) : ℂ) * ℓ x)
    (ψ : AdditiveCharacter) (hI : Representation.IsIrreducible ρ)
    (hA : letI := T.generalLinearTopology (n + 1); IsAdmissible ρ) :
    letI := T.topology
    letI := T.generalLinearTopology (n + 1)
    Whittaker.IsGeneric ψ n ρ := by
  let := T.topology
  let := T.generalLinearTopology (n + 1)
  let χ' := T.unitaryAdditiveCharacterOfTrivialOnIntegers χ hχ hO
  apply (T.isGeneric_iff_character ρ χ' ψ).mp
  exact ⟨hI, hA, ⟨⟨ℓ, heq⟩, hℓ⟩⟩

end Langlands.PadicField.TopologicalData
