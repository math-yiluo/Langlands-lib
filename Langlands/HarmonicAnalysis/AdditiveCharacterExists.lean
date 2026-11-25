import Langlands.HarmonicAnalysis.Basic
import Langlands.Representation.Twist.ContinuousCharacterProof
import Mathlib.Algebra.Module.CharacterModule
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.NumberTheory.LocalField.Basic
import Mathlib.Topology.Algebra.Nonarchimedean.Basic

/-!
# Continuous additive characters of nonarchimedean groups

* `isLocallyConstant_of_continuous_addChar`: a continuous complex additive character of a
  nonarchimedean topological group is locally constant (it is trivial on an open subgroup,
  because `ℂˣ` has no small subgroups).
* A nonarchimedean local field is a nonarchimedean additive group (an instance).
* `nonempty_unitaryAdditiveCharacter`: every nonarchimedean local field, of any characteristic,
  has a continuous non-trivial unitary additive character; `exists_addChar_continuous_ne_one`
  states it for complex-valued characters.

The character is built from a character of the discrete group `F ⧸ 𝒪` that does not vanish at
the class of `r⁻¹`, for an `r` of valuation `< 1`: such a character exists with values in
`ℚ ⧸ ℤ` because `ℚ ⧸ ℤ` is an injective cogenerator (`CharacterModule`), and it is carried into
the circle by `ℚ ⧸ ℤ → ℝ ⧸ ℤ → Circle`.
-/

noncomputable section

open Topology ValuativeRel

namespace Langlands.HarmonicAnalysis

universe u

/-- A continuous complex additive character of a nonarchimedean group is locally constant. -/
theorem isLocallyConstant_of_continuous_addChar {A : Type*} [AddGroup A] [TopologicalSpace A]
    [NonarchimedeanAddGroup A] (ψ : AddChar A ℂ) (hψ : Continuous ψ) : IsLocallyConstant ψ := by
  let O : Set A := {a | ‖ψ a - 1‖ < (1 / 2 : ℝ)}
  have hO : O ∈ 𝓝 (0 : A) :=
    (isOpen_lt (hψ.sub continuous_const).norm continuous_const).mem_nhds (by simp)
  obtain ⟨V, hV⟩ := NonarchimedeanAddGroup.is_nonarchimedean O hO
  have h1 : ∀ v ∈ V, ψ v = 1 := fun v hv =>
    Langlands.complex_eq_one_of_forall_norm_pow_sub_one_lt fun n => by
      rw [← AddChar.map_nsmul_eq_pow]
      exact hV (V.toAddSubgroup.nsmul_mem hv n)
  refine (IsLocallyConstant.iff_exists_open _).2 fun x => ?_
  refine ⟨(fun y => -x + y) ⁻¹' (V : Set A), V.isOpen.preimage (continuous_const.add continuous_id),
    by simp, fun y hy => ?_⟩
  have hy' : ψ (-x + y) = 1 := h1 _ hy
  calc ψ y = ψ (x + (-x + y)) := by rw [add_neg_cancel_left]
    _ = ψ x := by rw [AddChar.map_add_eq_mul, hy', mul_one]

/-- A nonarchimedean local field is a nonarchimedean additive group: the balls
`{x | v x < γ}`, `γ ≠ 0`, are open subgroups forming a basis at `0`. -/
instance nonarchimedeanAddGroup_of_isNonarchimedeanLocalField (F : Type u) [Field F]
    [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] :
    NonarchimedeanAddGroup F where
  is_nonarchimedean U hU := by
    obtain ⟨γ, hγ, hsub⟩ := (IsValuativeTopology.hasBasis_nhds_zero' F).mem_iff.1 hU
    let S : AddSubgroup F :=
      { carrier := {x | valuation F x < γ}
        add_mem' := fun {a b} ha hb =>
          show valuation F (a + b) < γ from
            lt_of_le_of_lt (Valuation.map_add _ a b) (max_lt ha hb)
        zero_mem' := by simpa using zero_lt_iff.2 hγ
        neg_mem' := fun {a} ha => by simpa [Valuation.map_neg] using ha }
    have hS : (S : Set F) ∈ 𝓝 (0 : F) :=
      (IsValuativeTopology.hasBasis_nhds_zero' F).mem_iff.2 ⟨γ, hγ, subset_rfl⟩
    exact ⟨⟨S, S.isOpen_of_mem_nhds hS⟩, hsub⟩

/-- The complex character of a unitary additive character is non-trivial. -/
theorem UnitaryAdditiveCharacter.complex_ne_one {F : Type u} [AddGroup F] [TopologicalSpace F]
    (ψ : UnitaryAdditiveCharacter F) : ψ.complex ≠ 1 := fun h =>
  ψ.nontrivial (AddChar.ext _ _ fun t => Subtype.ext (by
    simpa using DFunLike.congr_fun h t))

variable (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]

/-- Every nonarchimedean local field has a continuous non-trivial unitary additive character. -/
theorem nonempty_unitaryAdditiveCharacter : Nonempty (UnitaryAdditiveCharacter F) := by
  obtain ⟨r, hr, hr1⟩ := Valuation.IsNontrivial.exists_lt_one (v := valuation F)
  let O : AddSubgroup F := (𝒪[F]).toAddSubgroup
  have hx : r⁻¹ ∉ O := fun h => by
    have h' : valuation F r⁻¹ ≤ 1 := h
    rw [map_inv₀, inv_le_one₀ (zero_lt_iff.2 (by simpa using hr))] at h'
    exact absurd hr1 (not_lt.2 h')
  have hx' : ((r⁻¹ : F) : F ⧸ O) ≠ 0 := fun h => hx ((QuotientAddGroup.eq_zero_iff _).1 h)
  obtain ⟨χ, hχ⟩ := CharacterModule.exists_character_apply_ne_zero_of_ne_zero hx'
  let j : AddCircle (1 : ℚ) →+ AddCircle (1 : ℝ) :=
    QuotientAddGroup.map _ _ (Rat.castHom ℝ).toAddMonoidHom (by
      rintro _ ⟨k, rfl⟩
      exact ⟨k, by simp⟩)
  have hj : ∀ x, j x = 0 → x = 0 := by
    intro x
    induction x using QuotientAddGroup.induction_on with
    | H q =>
      intro h
      obtain ⟨k, hk⟩ := (QuotientAddGroup.eq_zero_iff _).1 (show ((q : ℝ) : AddCircle (1 : ℝ)) = 0 from h)
      refine (QuotientAddGroup.eq_zero_iff _).2 ⟨k, ?_⟩
      have : ((k : ℚ) : ℝ) = q := by simpa using hk
      simpa using (by exact_mod_cast this : (k : ℚ) = q)
  let ψ : AddChar F Circle :=
    { toFun := fun t => AddCircle.toCircle (j (χ t))
      map_zero_eq_one' := by simp
      map_add_eq_mul' := fun a b => by
        rw [QuotientAddGroup.mk_add, map_add, map_add, AddCircle.toCircle_add] }
  have hOopen : IsOpen (O : Set F) := O.isOpen_of_mem_nhds
    ((IsValuativeTopology.hasBasis_nhds_zero' F).mem_iff.2
      ⟨1, one_ne_zero, fun _ hx => le_of_lt (α := ValueGroupWithZero F) hx⟩)
  have := QuotientAddGroup.discreteTopology hOopen
  refine ⟨⟨ψ, ?_, fun h => hχ (hj _ ?_)⟩⟩
  · exact (continuous_of_discreteTopology
      (f := fun q : F ⧸ O => AddCircle.toCircle (j (χ q)))).comp QuotientAddGroup.continuous_mk
  · refine AddCircle.injective_toCircle one_ne_zero ?_
    rw [AddCircle.toCircle_zero]
    exact DFunLike.congr_fun h r⁻¹

/-- Every nonarchimedean local field has a continuous non-trivial complex additive character. -/
theorem exists_addChar_continuous_ne_one : ∃ ψ : AddChar F ℂ, Continuous ψ ∧ ψ ≠ 1 := by
  obtain ⟨ψ⟩ := nonempty_unitaryAdditiveCharacter F
  exact ⟨ψ.complex, ψ.continuous_complex, ψ.complex_ne_one⟩

end Langlands.HarmonicAnalysis
