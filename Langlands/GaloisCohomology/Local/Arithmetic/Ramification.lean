import Langlands.GaloisCohomology.Local.Arithmetic.Uniqueness
import Langlands.GaloisCohomology.Local.Arithmetic.Units
import Langlands.LocalFactor.Ramification.FiniteTameInertiaProof
import Langlands.LocalFactor.Ramification.InertiaSolvabilityProof
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.FieldTheory.Perfect

/-!
# Ramification groups of a finite Galois extension of local fields

For a finite extension `L/K` of nonarchimedean local fields, the group `L ≃ₐ[K] L` acts on the
ring of integers `𝒪[L]`; the lower ramification groups are the Library's
`Langlands.Ramification.lowerGroup` for this action. This file proves what the local Euler
characteristic needs: `G₀` is the kernel of the action on the residue field, `G/G₀` is cyclic,
`G₀/G₁` is cyclic of order prime to the residue characteristic `p` (it embeds into `𝓀[L]ˣ`
through `σ ↦ σ(ϖ)/ϖ`), and `G₁` is a `p`-group.
-/

noncomputable section

namespace Langlands.GaloisCohomology.Local

open ValuativeRel IsLocalRing

section Ramification

variable (K L : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
  [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
  [Algebra K L] [ValuativeExtension K L] [FiniteDimensional K L]

/-- The action of `L ≃ₐ[K] L` on the ring of integers `𝒪[L]`. -/
@[instance_reducible]
def integerAction : MulSemiringAction (L ≃ₐ[K] L) 𝒪[L] :=
  MulSemiringAction.compHom 𝒪[L] (integerAlgEquiv K L)

/-- The lower ramification group `G_i` of `L/K`: the Library's `lowerGroup` for the action of
`L ≃ₐ[K] L` on `𝒪[L]`, i.e. the automorphisms acting trivially on `𝒪[L] / 𝓂[L]^(i+1)`. -/
def lowerRamificationGroup (i : ℕ) : Subgroup (L ≃ₐ[K] L) :=
  letI := integerAction K L
  Ramification.lowerGroup 𝒪[L] (L ≃ₐ[K] L) i

variable {K L}

theorem mem_lowerRamificationGroup_iff {i : ℕ} {σ : L ≃ₐ[K] L} :
    σ ∈ lowerRamificationGroup K L i ↔
      ∀ x : 𝒪[L], integerAlgEquiv K L σ x - x ∈ 𝓂[L] ^ (i + 1) :=
  Iff.rfl

variable (K L)

theorem lowerRamificationGroup_antitone : Antitone (lowerRamificationGroup K L) := by
  let := integerAction K L
  exact Ramification.lowerGroup_antitone 𝒪[L] (L ≃ₐ[K] L)

instance lowerRamificationGroup_normal (i : ℕ) : (lowerRamificationGroup K L i).Normal := by
  let := integerAction K L
  exact Ramification.lowerGroup_normal 𝒪[L] (L ≃ₐ[K] L) i

theorem lowerRamificationGroup_zero :
    lowerRamificationGroup K L 0 = (residueAlgEquiv K L).ker := by
  ext σ
  rw [MonoidHom.mem_ker, AlgEquiv.ext_iff, mem_lowerRamificationGroup_iff, zero_add, pow_one]
  refine ⟨fun h r ↦ ?_, fun h x ↦ ?_⟩
  · obtain ⟨x, rfl⟩ := residue_surjective r
    rw [residueAlgEquiv_residue, AlgEquiv.one_apply, ← sub_eq_zero, ← map_sub,
      residue_eq_zero_iff]
    exact h x
  · have := h (residue 𝒪[L] x)
    rwa [residueAlgEquiv_residue, AlgEquiv.one_apply, ← sub_eq_zero, ← map_sub,
      residue_eq_zero_iff] at this

theorem residue_integerAlgEquiv_of_mem_zero {σ : L ≃ₐ[K] L}
    (hσ : σ ∈ lowerRamificationGroup K L 0) (x : 𝒪[L]) :
    residue 𝒪[L] (integerAlgEquiv K L σ x) = residue 𝒪[L] x := by
  rw [lowerRamificationGroup_zero, MonoidHom.mem_ker] at hσ
  rw [← residueAlgEquiv_residue, hσ, AlgEquiv.one_apply]

variable {K L} in
theorem algEquiv_eq_of_forall_integer {σ τ : L ≃ₐ[K] L}
    (h : ∀ x : 𝒪[L], integerAlgEquiv K L σ x = integerAlgEquiv K L τ x) : σ = τ := by
  ext y
  by_cases hy : valuation L y ≤ 1
  · exact congrArg Subtype.val (h ⟨y, hy⟩)
  · have hy0 : y ≠ 0 := by rintro rfl; simp at hy
    have hinv : valuation L y⁻¹ ≤ 1 := by
      rw [map_inv₀]
      exact inv_le_one_of_one_le₀ (le_of_lt (not_le.mp hy))
    have := congrArg Subtype.val (h ⟨y⁻¹, hinv⟩)
    simp only [coe_integerAlgEquiv_apply, map_inv₀] at this
    exact inv_injective this

theorem faithfulSMul_integerAction :
    letI := integerAction K L
    FaithfulSMul (L ≃ₐ[K] L) 𝒪[L] :=
  letI := integerAction K L
  ⟨fun h ↦ algEquiv_eq_of_forall_integer h⟩

/-- The lower ramification filtration terminates. -/
theorem exists_lowerRamificationGroup_eq_bot :
    ∃ b : ℕ, ∀ i ≥ b, lowerRamificationGroup K L i = ⊥ := by
  let := integerAction K L
  have := faithfulSMul_integerAction K L
  exact Ramification.exists_lowerGroup_eq_bot 𝒪[L] (L ≃ₐ[K] L)

end Ramification

section Ratio

variable {K L : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
  [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
  [Algebra K L] [ValuativeExtension K L] [FiniteDimensional K L]

theorem irreducible_integerAlgEquiv (σ : L ≃ₐ[K] L) {ϖ : 𝒪[L]} (hϖ : Irreducible ϖ) :
    Irreducible (integerAlgEquiv K L σ ϖ) :=
  (MulEquiv.irreducible_iff (f := (integerAlgEquiv K L σ : 𝒪[L] ≃* 𝒪[L]))).mpr hϖ

/-- The unit `σ(ϖ)/ϖ` for a uniformizer `ϖ` of `L`. -/
def uniformizerRatio {ϖ : 𝒪[L]} (hϖ : Irreducible ϖ) (σ : L ≃ₐ[K] L) : 𝒪[L]ˣ :=
  (IsDiscreteValuationRing.associated_of_irreducible 𝒪[L] hϖ
    (irreducible_integerAlgEquiv σ hϖ)).choose

variable {ϖ : 𝒪[L]} (hϖ : Irreducible ϖ)
include hϖ

theorem mul_uniformizerRatio (σ : L ≃ₐ[K] L) :
    ϖ * uniformizerRatio hϖ σ = integerAlgEquiv K L σ ϖ :=
  (IsDiscreteValuationRing.associated_of_irreducible 𝒪[L] hϖ
    (irreducible_integerAlgEquiv σ hϖ)).choose_spec

theorem uniformizerRatio_eq_iff (σ : L ≃ₐ[K] L) (u : 𝒪[L]ˣ) :
    uniformizerRatio hϖ σ = u ↔ ϖ * u = integerAlgEquiv K L σ ϖ := by
  refine ⟨fun h ↦ h ▸ mul_uniformizerRatio hϖ σ, fun h ↦ Units.ext ?_⟩
  exact mul_left_cancel₀ hϖ.ne_zero ((mul_uniformizerRatio hϖ σ).trans h.symm)

@[simp]
theorem uniformizerRatio_one : uniformizerRatio hϖ (1 : L ≃ₐ[K] L) = 1 := by
  rw [uniformizerRatio_eq_iff, map_one, AlgEquiv.one_apply, Units.val_one, mul_one]

theorem uniformizerRatio_mul (σ τ : L ≃ₐ[K] L) :
    uniformizerRatio hϖ (σ * τ) = uniformizerRatio hϖ σ *
      Units.map (integerAlgEquiv K L σ : 𝒪[L] →* 𝒪[L]) (uniformizerRatio hϖ τ) := by
  rw [uniformizerRatio_eq_iff, map_mul, AlgEquiv.mul_apply, ← mul_uniformizerRatio hϖ τ, map_mul,
    ← mul_uniformizerRatio hϖ σ, Units.val_mul, Units.coe_map, MonoidHom.coe_ofClass, mul_assoc]

/-- `σ ∈ G₀` lies in `G₁` exactly when `σ(ϖ)/ϖ ≡ 1` modulo `𝓂[L]` (the residue field is perfect
of characteristic `p`; the Library's `mem_lowerGroup_one_of_frobenius`). -/
theorem mem_lowerRamificationGroup_one_iff {σ : L ≃ₐ[K] L}
    (hσ : σ ∈ lowerRamificationGroup K L 0) :
    σ ∈ lowerRamificationGroup K L 1 ↔ uniformizerRatio hϖ σ ∈ unitFiltration L 1 := by
  have key : integerAlgEquiv K L σ ϖ - ϖ ∈ 𝓂[L] ^ 2 ↔
      uniformizerRatio hϖ σ ∈ unitFiltration L 1 := by
    rw [mem_unitFiltration, ← mul_uniformizerRatio hϖ σ, mem_maximalIdeal_pow_iff hϖ,
      mem_maximalIdeal_pow_iff hϖ,
      show ϖ * (uniformizerRatio hϖ σ : 𝒪[L]) - ϖ = ϖ * ((uniformizerRatio hϖ σ : 𝒪[L]) - 1) by
        ring,
      pow_two, pow_one, mul_dvd_mul_iff_left hϖ.ne_zero]
  rw [← key]
  refine ⟨fun h ↦ mem_lowerRamificationGroup_iff.mp h ϖ, fun h ↦ ?_⟩
  let := integerAction K L
  have hp : (ringChar 𝓀[L]).Prime := CharP.char_is_prime 𝓀[L] _
  have : Fact (ringChar 𝓀[L]).Prime := ⟨hp⟩
  have hpm : ((ringChar 𝓀[L] : ℕ) : 𝒪[L]) ∈ 𝓂[L] := by
    rw [← residue_eq_zero_iff, map_natCast, ringChar.Nat.cast_ringChar]
  have hfrob : ∀ x : 𝒪[L], ∃ y : 𝒪[L], x - y ^ ringChar 𝓀[L] ∈ 𝓂[L] := by
    intro x
    obtain ⟨r, hr⟩ := surjective_frobenius 𝓀[L] (ringChar 𝓀[L]) (residue 𝒪[L] x)
    obtain ⟨y, rfl⟩ := residue_surjective r
    refine ⟨y, ?_⟩
    rw [← residue_eq_zero_iff, map_sub, map_pow, ← hr, frobenius_def, sub_self]
  exact Ramification.mem_lowerGroup_one_of_frobenius hϖ.maximalIdeal_eq hp hpm hfrob hσ h

omit hϖ in
theorem units_map_mem_of_mem_zero {σ : L ≃ₐ[K] L} (hσ : σ ∈ lowerRamificationGroup K L 0)
    (u : 𝒪[L]ˣ) :
    unitsToResidue L (Units.map (integerAlgEquiv K L σ : 𝒪[L] →* 𝒪[L]) u) =
      unitsToResidue L u := by
  ext
  exact residue_integerAlgEquiv_of_mem_zero K L hσ _

/-- The tame character `G₀ → 𝓀[L]ˣ`, `σ ↦ σ(ϖ)/ϖ mod 𝓂[L]`. -/
def inertiaToResidueUnits : lowerRamificationGroup K L 0 →* 𝓀[L]ˣ where
  toFun σ := unitsToResidue L (uniformizerRatio hϖ (σ : L ≃ₐ[K] L))
  map_one' := by simp
  map_mul' σ τ := by
    rw [Subgroup.coe_mul, uniformizerRatio_mul, map_mul, units_map_mem_of_mem_zero σ.2]

theorem ker_inertiaToResidueUnits :
    (inertiaToResidueUnits hϖ).ker =
      (lowerRamificationGroup K L 1).subgroupOf (lowerRamificationGroup K L 0) := by
  ext σ
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, mem_lowerRamificationGroup_one_iff hϖ σ.2,
    ← ker_unitsToResidue, MonoidHom.mem_ker]
  rfl

/-- `G₀/G₁` embeds into `𝓀[L]ˣ`. -/
def inertiaQuotientToResidueUnits :
    lowerRamificationGroup K L 0 ⧸
        (lowerRamificationGroup K L 1).subgroupOf (lowerRamificationGroup K L 0) →* 𝓀[L]ˣ :=
  (QuotientGroup.kerLift (inertiaToResidueUnits hϖ)).comp
    (QuotientGroup.quotientMulEquivOfEq (ker_inertiaToResidueUnits hϖ).symm).toMonoidHom

theorem inertiaQuotientToResidueUnits_injective :
    Function.Injective (inertiaQuotientToResidueUnits (K := K) hϖ) :=
  fun _ _ hab ↦ (MulEquiv.injective _)
    (QuotientGroup.kerLift_injective (inertiaToResidueUnits hϖ) hab)

end Ratio

section Structure

variable (K L : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
  [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
  [Algebra K L] [ValuativeExtension K L] [FiniteDimensional K L]

theorem isCyclic_lowerRamificationGroup_zero_quotient :
    IsCyclic (lowerRamificationGroup K L 0 ⧸
      (lowerRamificationGroup K L 1).subgroupOf (lowerRamificationGroup K L 0)) := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[L]
  exact isCyclic_of_injective _ (inertiaQuotientToResidueUnits_injective hϖ)

theorem card_lowerRamificationGroup_zero_quotient_dvd :
    Nat.card (lowerRamificationGroup K L 0 ⧸
      (lowerRamificationGroup K L 1).subgroupOf (lowerRamificationGroup K L 0)) ∣
        Nat.card 𝓀[L] - 1 := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[L]
  rw [← Nat.card_units 𝓀[L]]
  exact Subgroup.card_dvd_of_injective _ (inertiaQuotientToResidueUnits_injective hϖ)

variable {K L} in
theorem coprime_card_residueField_sub_one :
    Nat.Coprime (Nat.card 𝓀[L] - 1) (ringChar 𝓀[L]) := by
  let := Fintype.ofFinite 𝓀[L]
  have hq : ringChar 𝓀[L] ∣ Nat.card 𝓀[L] := by
    rw [← CharP.cast_eq_zero_iff 𝓀[L] (ringChar 𝓀[L]), Nat.card_eq_fintype_card]
    exact FiniteField.cast_card_eq_zero _
  have h1 : 1 ≤ Nat.card 𝓀[L] := Nat.card_pos
  refine Nat.Coprime.symm (Nat.dvd_one.mp ?_)
  have ha := Nat.gcd_dvd_left (ringChar 𝓀[L]) (Nat.card 𝓀[L] - 1)
  have hb := Nat.gcd_dvd_right (ringChar 𝓀[L]) (Nat.card 𝓀[L] - 1)
  have := Nat.dvd_sub (ha.trans hq) hb
  rwa [Nat.sub_sub_self h1] at this

theorem coprime_card_lowerRamificationGroup_zero_quotient :
    Nat.Coprime (Nat.card (lowerRamificationGroup K L 0 ⧸
      (lowerRamificationGroup K L 1).subgroupOf (lowerRamificationGroup K L 0)))
        (ringChar 𝓀[K]) := by
  rw [Algebra.ringChar_eq 𝓀[K] 𝓀[L]]
  exact Nat.Coprime.coprime_dvd_left (card_lowerRamificationGroup_zero_quotient_dvd K L)
    coprime_card_residueField_sub_one

/-- The wild inertia group `G₁` is a `p`-group, `p` the residue characteristic (the Library's
`isPGroup_lowerGroup_one_of_terminates`). -/
theorem isPGroup_lowerRamificationGroup_one :
    IsPGroup (ringChar 𝓀[K]) (lowerRamificationGroup K L 1) := by
  rw [Algebra.ringChar_eq 𝓀[K] 𝓀[L]]
  let := integerAction K L
  have hpm : ((ringChar 𝓀[L] : ℕ) : 𝒪[L]) ∈ 𝓂[L] := by
    rw [← residue_eq_zero_iff, map_natCast, ringChar.Nat.cast_ringChar]
  obtain ⟨b, hb⟩ := exists_lowerRamificationGroup_eq_bot K L
  exact Ramification.isPGroup_lowerGroup_one_of_terminates hpm ⟨b, hb b le_rfl⟩

instance isCyclic_quotient_lowerRamificationGroup_zero :
    IsCyclic ((L ≃ₐ[K] L) ⧸ lowerRamificationGroup K L 0) := by
  have : IsCyclic ((L ≃ₐ[K] L) ⧸ (residueAlgEquiv K L).ker) :=
    isCyclic_of_injective (QuotientGroup.kerLift _) (QuotientGroup.kerLift_injective _)
  exact isCyclic_of_surjective
    (QuotientGroup.quotientMulEquivOfEq (lowerRamificationGroup_zero K L).symm).toMonoidHom
    (MulEquiv.surjective _)

end Structure

end Langlands.GaloisCohomology.Local
