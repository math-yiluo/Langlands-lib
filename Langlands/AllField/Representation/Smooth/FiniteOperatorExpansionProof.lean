import Langlands.Representation.Smooth.FiniteOperatorExpansionProof
import Langlands.AllField.LocalField.Foundation
/-!
# Proof of the finite operator expansion of a smooth representation of `Fˣ`

Finitely many vectors separate a finite-dimensional space of operators, so the
intersection of their open stabilizers acts trivially and `b ↦ σ b` is locally
constant. Left multiplication by `σ (ϖ ^ n)` is an injective endomorphism of the
finite-dimensional bounded span, hence surjective, which puts every `σ b` in the
bounded span. The expansion uses the coordinates of a basis of the operator span.
-/

noncomputable section

namespace Langlands.AllField

universe uF uV uG

section Generic

variable {V : Type uV} [AddCommGroup V] [Module ℂ V]

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

end Generic

section Padic

variable {F : Type uF} [Field F] (T : LocalFieldData F)
variable {V : Type uV} [AddCommGroup V] [Module ℂ V]

/-- The operators of units with normalized absolute value at most one span the
whole finite-dimensional operator span. -/
theorem boundedSpan_eq_span (σ : Representation ℂ Fˣ V)
    [FiniteDimensional ℂ (Submodule.span ℂ (Set.range σ))] :
    Submodule.span ℂ {B : Module.End ℂ V |
        ∃ b : Fˣ, T.normalizedAbs (b : F) ≤ 1 ∧ σ b = B} =
      Submodule.span ℂ (Set.range σ) := by
  set Bd := Submodule.span ℂ {B : Module.End ℂ V |
    ∃ b : Fˣ, T.normalizedAbs (b : F) ≤ 1 ∧ σ b = B} with hBd
  have hle : Bd ≤ Submodule.span ℂ (Set.range σ) := by
    apply Submodule.span_mono
    rintro _ ⟨b, _, rfl⟩
    exact ⟨b, rfl⟩
  have : FiniteDimensional ℂ Bd := Submodule.finiteDimensional_of_le hle
  have hmul (c : Fˣ) (hc : T.normalizedAbs (c : F) ≤ 1)
      (x : Module.End ℂ V) (hx : x ∈ Bd) : σ c * x ∈ Bd := by
    induction hx using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨b, hb, rfl⟩ := hy
      refine Submodule.subset_span ⟨c * b, ?_, by rw [map_mul]⟩
      rw [Units.val_mul, T.normalizedAbs_mul]
      exact (mul_le_of_le_one_left (T.normalizedAbs_nonneg _) hc).trans hb
    | zero => simp
    | add x y _ _ h₁ h₂ => simpa [mul_add] using Bd.add_mem h₁ h₂
    | smul r x _ h => simpa [mul_smul_comm] using Bd.smul_mem r h
  have hq : (1 : ℝ) ≤ T.residueCardinality := by
    exact_mod_cast T.residueCardinality_gt_one.le
  have hq0 : (T.residueCardinality : ℝ) ≠ 0 := by
    exact_mod_cast (lt_trans Nat.zero_lt_one T.residueCardinality_gt_one).ne'
  refine le_antisymm hle (Submodule.span_le.mpr ?_)
  rintro _ ⟨b, rfl⟩
  obtain ⟨n, hn⟩ : ∃ n : ℕ, -T.ord (b : F) ≤ n := ⟨_, Int.self_le_toNat _⟩
  let c : Fˣ := Langlands.LocalFactor.LocalAbelian.uniformizerUnit T ^ (n : ℤ)
  have hcabs : T.normalizedAbs (c : F) = (T.residueCardinality : ℝ) ^ (-(n : ℤ)) :=
    Langlands.LocalFactor.LocalAbelian.uniformizerUnit_zpow_abs T n
  have hc : T.normalizedAbs (c : F) ≤ 1 := by
    rw [hcabs]
    exact zpow_le_one_of_nonpos₀ hq (by omega)
  have hcb : T.normalizedAbs ((c * b : Fˣ) : F) ≤ 1 := by
    rw [Units.val_mul, T.normalizedAbs_mul, hcabs, T.normalizedAbs_of_ne_zero b.ne_zero,
      ← zpow_add₀ hq0]
    exact zpow_le_one_of_nonpos₀ hq (by omega)
  have hinv (x : Module.End ℂ V) : σ c⁻¹ * (σ c * x) = x := by
    rw [← mul_assoc, ← map_mul, inv_mul_cancel, map_one, one_mul]
  let L : Bd →ₗ[ℂ] Bd :=
    { toFun x := ⟨σ c * x.val, hmul c hc x.val x.property⟩
      map_add' x y := by ext1; simp [mul_add]
      map_smul' r x := by ext1; simp }
  have hL : Function.Injective L := by
    intro x y hxy
    apply Subtype.ext
    rw [← hinv x.val, ← hinv y.val]
    exact congrArg (fun z : Bd => σ c⁻¹ * z.val) hxy
  obtain ⟨y, hy⟩ := LinearMap.injective_iff_surjective.mp hL
    ⟨σ (c * b), Submodule.subset_span ⟨c * b, hcb, rfl⟩⟩
  have hyb : y.val = σ b := by
    rw [← hinv y.val]
    have h : σ c * y.val = σ (c * b) := congrArg Subtype.val hy
    rw [h, map_mul, hinv]
  rw [← hyb]
  exact y.property

end Padic

end Langlands.AllField
