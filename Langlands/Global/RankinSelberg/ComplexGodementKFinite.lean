import Langlands.Global.RankinSelberg.ComplexGodementSmooth

/-! # Compact-finite complex Godement sections -/

noncomputable section

open MeasureTheory Measure
open scoped ContDiff Manifold Matrix.Norms.Operator

namespace Langlands.Global.RankinSelbergGlobal.ComplexGodement

open Langlands.GeneralLinear Langlands.Archimedean Langlands.LocalFactor.Archimedean

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

local instance (n : ℕ) : MeasurableSpace (Langlands.GeneralLinear n ℂ) := borel _
local instance (n : ℕ) : BorelSpace (Langlands.GeneralLinear n ℂ) := ⟨rfl⟩

private abbrev Rect (m : ℕ) := Matrix (Fin m) (Fin (m + 1)) ℂ

/-- The space of continuous, compactly supported tests whose support lies in full row rank. -/
def godementTests (m : ℕ) : Submodule ℂ (Rect m → ℂ) where
  carrier := {Φ | Continuous Φ ∧ HasCompactSupport Φ ∧ ∀ X ∈ tsupport Φ, HasFullRowRank X}
  zero_mem' := ⟨continuous_const, HasCompactSupport.zero, by simp⟩
  add_mem' := by
    intro Φ Ψ hΦ hΨ
    refine ⟨hΦ.1.add hΨ.1, hΦ.2.1.add hΨ.2.1, fun X hX => ?_⟩
    have hsub : tsupport (Φ + Ψ) ⊆ tsupport Φ ∪ tsupport Ψ :=
      tsupport_binop_subset (· + ·) (zero_add 0) Φ Ψ
    rcases hsub hX with h | h
    · exact hΦ.2.2 X h
    · exact hΨ.2.2 X h
  smul_mem' := by
    intro c Φ hΦ
    refine ⟨hΦ.1.const_smul c, hΦ.2.1.smul_left, fun X hX => ?_⟩
    exact hΦ.2.2 X (tsupport_smul_subset_right (fun _ => c) Φ hX)

/-- Right multiplication in the rectangular test variable. -/
def translateTest {m : ℕ} (k : Langlands.GeneralLinear (m + 1) ℂ) (Φ : Rect m → ℂ) : Rect m → ℂ :=
  fun X => Φ (X * k.val)

private def rightMatrixHomeomorph {m : ℕ} (k : Langlands.GeneralLinear (m + 1) ℂ) :
    Rect m ≃ₜ Rect m where
  toFun X := X * k.val
  invFun X := X * k⁻¹.val
  left_inv X := by
    change (X * k.val) * k⁻¹.val = X
    rw [Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.mul_one]
  right_inv X := by
    change (X * k⁻¹.val) * k.val = X
    rw [Matrix.mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.mul_one]
  continuous_toFun := continuous_id.matrix_mul continuous_const
  continuous_invFun := continuous_id.matrix_mul continuous_const

private theorem translateTest_mem {m : ℕ} (k : Langlands.GeneralLinear (m + 1) ℂ)
    {Φ : Rect m → ℂ} (hΦ : Φ ∈ godementTests m) : translateTest k Φ ∈ godementTests m := by
  let e := rightMatrixHomeomorph k
  have hsub : tsupport (translateTest k Φ) ⊆ e ⁻¹' tsupport Φ :=
    closure_minimal (fun X hX => subset_tsupport Φ hX) ((isClosed_tsupport Φ).preimage e.continuous)
  refine ⟨hΦ.1.comp e.continuous,
    HasCompactSupport.of_support_subset_isCompact (e.isCompact_preimage.mpr hΦ.2.1)
      ((subset_tsupport _).trans hsub), fun X hX => ?_⟩
  obtain ⟨Y, hY⟩ := hΦ.2.2 (e X) (hsub hX)
  exact ⟨k.val * Y, by rw [← Matrix.mul_assoc]; exact hY⟩

/-- The integral defines a linear map in the test on the space of compact full-row-rank tests. -/
def godementSectionLinear {m : ℕ} (ν : Measure (Langlands.GeneralLinear m ℂ))
    [IsLocallyFiniteMeasure ν] (d : ComplexCharacterData) {f : Langlands.GeneralLinear m ℂ → ℂ}
    (hf : Continuous f) : godementTests m →ₗ[ℂ] (Langlands.GeneralLinear (m + 1) ℂ → ℂ) where
  toFun Φ := godementSection ν d Φ.val f
  map_add' Φ Ψ := by
    funext g
    have hΦ := integrable_godementSectionIntegrand ν d Φ.2.1 Φ.2.2.1 Φ.2.2.2 hf g
    have hΨ := integrable_godementSectionIntegrand ν d Ψ.2.1 Ψ.2.2.1 Ψ.2.2.2 hf g
    simp only [godementSection, Submodule.coe_add, Pi.add_apply]
    have h : godementSectionIntegrand d (Φ.val + Ψ.val) f g =
        godementSectionIntegrand d Φ.val f g + godementSectionIntegrand d Ψ.val f g := by
      funext x
      simp only [godementSectionIntegrand, Pi.add_apply, add_mul]
    rw [h]
    simp only [Pi.add_apply, integral_add hΦ hΨ, mul_add]
  map_smul' c Φ := by
    funext g
    simp only [godementSection, Submodule.coe_smul, Pi.smul_apply, smul_eq_mul,
      RingHom.id_apply]
    have h : godementSectionIntegrand d (c • Φ.val) f g =
        fun x => c * godementSectionIntegrand d Φ.val f g x := by
      funext x
      simp only [godementSectionIntegrand, Pi.smul_apply, smul_eq_mul, mul_assoc]
    rw [h, integral_const_mul, mul_left_comm]

/-- Right translation of the section is right multiplication on the rectangular test, with
the determinant factor belonging to the translating element. -/
theorem godementSection_right_mul {m : ℕ} (ν : Measure (Langlands.GeneralLinear m ℂ))
    (d : ComplexCharacterData) (Φ : Rect m → ℂ) (f : Langlands.GeneralLinear m ℂ → ℂ)
    (g k : Langlands.GeneralLinear (m + 1) ℂ) :
    godementSection ν d Φ f (g * k) =
      characterWeight d ((m : ℂ) / 2) (determinant k) *
        godementSection ν d (translateTest k Φ) f g := by
  have hrows : trailingRows (g * k).val = trailingRows g.val * k.val :=
    Matrix.submatrix_mul g.val k.val Fin.succ id id Function.bijective_id
  have hK : godementSectionIntegrand d Φ f (g * k) =
      godementSectionIntegrand d (translateTest k Φ) f g := by
    funext h
    simp only [godementSectionIntegrand, hrows, translateTest, Matrix.mul_assoc]
  simp only [godementSection, map_mul, hK]
  ring

/-- Compact finiteness of the test under right multiplication supplies compact finiteness
of the Godement vector. -/
def ComplexGodementKFiniteStatement : Prop :=
  ∀ (m : ℕ) (ν : Measure (Langlands.GeneralLinear m ℂ)) [IsLocallyFiniteMeasure ν]
    [IsMulRightInvariant ν] (d : ComplexCharacterData) (ds : List ComplexCharacterData)
    (Φ : Rect m → ℂ), ContDiff ℝ ∞ Φ → HasCompactSupport Φ →
    (∀ X ∈ tsupport Φ, HasFullRowRank X) →
    FiniteDimensional ℂ (Submodule.span ℂ (Set.range
      fun k : unitaryCompact ℂ (m + 1) => translateTest k.val Φ)) →
    ∀ (f : Langlands.GeneralLinear m ℂ → ℂ), f ∈ complexStandardModule m ds →
      godementSection ν d Φ f ∈
        kFiniteFunctions (complexStandardModule (m + 1) (d :: ds)) (unitaryCompact ℂ (m + 1))

theorem complexGodementKFinite : ComplexGodementKFiniteStatement := by
  intro m ν _ _ d ds Φ hΦ hΦc hfull hfinite f hf
  refine ⟨complexGodementCompactSmooth m ν d ds Φ hΦ hΦc hfull f hf, ?_⟩
  let orbit := fun k : unitaryCompact ℂ (m + 1) => translateTest k.val Φ
  let V := Submodule.span ℂ (Set.range orbit)
  have hle : V ≤ godementTests m := by
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨k, rfl⟩
    exact translateTest_mem k.val ⟨hΦ.continuous, hΦc, hfull⟩
  let T : V →ₗ[ℂ] (Langlands.GeneralLinear (m + 1) ℂ → ℂ) :=
    (godementSectionLinear ν d hf.1.continuous).comp (Submodule.inclusion hle)
  let _ : FiniteDimensional ℂ V := hfinite
  apply (mem_kFiniteVectors_iff _ _ _).mpr
  refine Submodule.finiteDimensional_of_le (S₂ := LinearMap.range T) (Submodule.span_le.mpr ?_)
  rintro _ ⟨k, rfl⟩
  let c := characterWeight d ((m : ℂ) / 2) (determinant k.val)
  have hmem : orbit k ∈ V := Submodule.subset_span ⟨k, rfl⟩
  refine ⟨c • (⟨orbit k, hmem⟩ : V), ?_⟩
  rw [map_smul]
  funext g
  change c * godementSection ν d (translateTest k.val Φ) f g = godementSection ν d Φ f (g * k.val)
  exact (godementSection_right_mul ν d Φ f g k.val).symm

end Langlands.Global.RankinSelbergGlobal.ComplexGodement
