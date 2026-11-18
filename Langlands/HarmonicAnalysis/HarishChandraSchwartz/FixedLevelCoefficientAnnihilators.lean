import Langlands.HarmonicAnalysis.HarishChandraSchwartz.VariableExponentAnnihilators
import Langlands.Representation.Jacquet.UniformInducedNilpotence

/-! # Uniform split annihilators for finite sums of fixed-level coefficients -/

noncomputable section

namespace Langlands.HarishChandraSchwartz

open Polynomial

universe uM uA uY uκ

variable {M : Type uM} [Group M] {A : Type uA} [CommGroup A]
  {Y : Type uY} [AddCommGroup Y] [Module ℂ Y]

/-- Coefficients whose source vectors lie in a specified subspace, allowing
arbitrary linear forms and arbitrary finite sums. -/
def coefficientSpaceFrom (J : Representation ℂ M Y) (W : Submodule ℂ Y) :
    Submodule ℂ (M → ℂ) :=
  Submodule.span ℂ {f | ∃ (lam : Y →ₗ[ℂ] ℂ) (y : Y), y ∈ W ∧ f = fun m => lam (J m y)}

/-- Restricting an action to a stable subspace retains exactly the same
simultaneous generalized-eigenvector equations on the unchanged vectors. -/
theorem mem_jointGenEigenspace_subrepresentation_iff
    (T : A →* Module.End ℂ Y) (W : Subrepresentation T) (χ : A → ℂ) (y : W.toSubmodule) :
    y ∈ jointGenEigenspace W.toRepresentation χ ↔
      (y : Y) ∈ jointGenEigenspace T χ := by
  simp only [jointGenEigenspace, Submodule.mem_iInf]
  apply forall_congr'
  intro a
  change y ∈ Module.End.genEigenspace ((T a).restrict (W.apply_mem_toSubmodule a)) (χ a) ⊤ ↔
    (y : Y) ∈ (T a).genEigenspace (χ a) ⊤
  rw [Module.End.genEigenspace_restrict]
  rfl

/-- A finite sum of coefficients with source in a finite-dimensional stable
space has an expansion with at most that space's dimension many exponent labels.
Every label occurs in that same space, and the nilpotence order is bounded by
any bound on its dimension, regardless of the number of coefficient summands. -/
theorem exists_bounded_coefficient_eigenfunctions
    (J : Representation ℂ M Y) (j : A →* M) (a : A)
    (W : Submodule ℂ Y) [FiniteDimensional ℂ W]
    (hW : ∀ a, ∀ y ∈ W, J (j a) y ∈ W) {d : ℕ}
    (hd : Module.finrank ℂ W ≤ d) {f : M → ℂ} (hf : f ∈ coefficientSpaceFrom J W) :
    ∃ (s : Finset (A → ℂ)) (c : (A → ℂ) → M → ℂ),
      s.card ≤ d ∧
      (∀ χ ∈ s, c χ ∈ jointGenEigenspace (componentRightTranslation j) χ) ∧
      (∀ χ ∈ s, ((componentRightTranslation j a - χ a • 1) ^ d) (c χ) = 0) ∧
      (∀ χ ∈ s, W ⊓ jointGenEigenspace (J.comp j) χ ≠ ⊥) ∧
      (∑ χ ∈ s, c χ) = f := by
  classical
  let Wₐ : Subrepresentation (J.comp j) :=
    { toSubmodule := W
      apply_mem_toSubmodule := fun a y hy => hW a y hy }
  let T := Wₐ.toRepresentation
  let := (iSupIndep_jointGenEigenspace T).fintypeNeBotOfFiniteDimensional
  let s : Finset (A → ℂ) := Finset.univ.image
    (Subtype.val : {χ // jointGenEigenspace T χ ≠ ⊥} → (A → ℂ))
  have hmem (χ : A → ℂ) : χ ∈ s ↔ jointGenEigenspace T χ ≠ ⊥ := by
    simp only [s, Finset.mem_image, Finset.mem_univ, true_and, Subtype.exists,
      exists_prop, exists_eq_right]
  have hs : s.card ≤ d :=
    (Finset.card_image_le.trans (by
      simpa only [Finset.card_univ] using
        (iSupIndep_jointGenEigenspace T).subtype_ne_bot_le_finrank)).trans hd
  have hexp : ∀ χ ∈ s, W ⊓ jointGenEigenspace (J.comp j) χ ≠ ⊥ := by
    intro χ hχ
    obtain ⟨y, hy, hy0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot ((hmem χ).mp hχ)
    refine (Submodule.ne_bot_iff _).mpr ⟨(y : Y), ⟨y.property, ?_⟩, ?_⟩
    · exact (mem_jointGenEigenspace_subrepresentation_iff (J.comp j) Wₐ χ y).mp hy
    · exact fun hz => hy0 (Subtype.ext hz)
  suffices ∃ c : (A → ℂ) → M → ℂ,
      (∀ χ ∈ s, c χ ∈ jointGenEigenspace (componentRightTranslation j) χ) ∧
      (∀ χ ∈ s, ((componentRightTranslation j a - χ a • 1) ^ d) (c χ) = 0) ∧
      (∑ χ ∈ s, c χ) = f by
    obtain ⟨c, hc, hk, hsum⟩ := this
    exact ⟨s, c, hs, hc, hk, hexp, hsum⟩
  induction hf using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨lam, y, hy, rfl⟩ := hf
    obtain ⟨v, hv, hsum⟩ := exists_sum_mem_jointGenEigenspace T ⊤
      (fun _ _ _ => Submodule.mem_top) (Submodule.mem_top (x := (⟨y, hy⟩ : W)))
    have hsub : v.support ⊆ s := by
      intro χ hχ
      apply (hmem χ).mpr
      exact (Submodule.ne_bot_iff _).mpr ⟨v χ, (hv χ).2, Finsupp.mem_support_iff.mp hχ⟩
    have hsum' : (∑ χ ∈ s, v χ) = (⟨y, hy⟩ : W) := by
      rw [← hsum, Finsupp.sum]
      exact (Finset.sum_subset hsub (fun χ _ hχ => Finsupp.notMem_support_iff.mp hχ)).symm
    have hv' : ∀ χ, (v χ : Y) ∈ jointGenEigenspace (J.comp j) χ := fun χ =>
      (mem_jointGenEigenspace_subrepresentation_iff (J.comp j) Wₐ χ (v χ)).mp (hv χ).2
    refine ⟨fun χ m => lam (J m (v χ)), ?_, ?_, ?_⟩
    · exact fun χ _ => coefficient_mem_jointGenEigenspace j J lam (hv' χ)
    · intro χ _
      have hk := pow_eq_zero_of_mem_jointGenEigenspace_of_finrank_le
        (J.comp j) W hW hd (v χ).property (hv' χ) a
      have he := aeval_rightFunctions_coefficient J lam (j a)
        ((X - C (χ a)) ^ d) (v χ)
      simp only [map_pow, map_sub, aeval_X, aeval_C, Algebra.algebraMap_eq_smul_one] at he
      change ((HarmonicAnalysis.GroupAction.rightFunctions (j a) - χ a • 1) ^ d) _ = 0
      rw [he]
      funext m
      simp only [MonoidHom.comp_apply] at hk
      simp [hk]
    · funext m
      have hh := congrArg (fun z : W => lam (J m z)) hsum'
      simpa only [Finset.sum_apply, Submodule.coe_sum, map_sum] using hh
  | zero =>
    exact ⟨0, (fun χ _ => Submodule.zero_mem _), (fun χ _ => map_zero _), by simp⟩
  | add f g _ _ hf hg =>
    obtain ⟨c, hc, hk, hsum⟩ := hf
    obtain ⟨b, hb, hl, hsum'⟩ := hg
    refine ⟨c + b, (fun χ hχ => Submodule.add_mem _ (hc χ hχ) (hb χ hχ)), ?_, ?_⟩
    · intro χ hχ
      simp only [Pi.add_apply, map_add, hk χ hχ, hl χ hχ, add_zero]
    · simp only [Pi.add_apply, Finset.sum_add_distrib, hsum, hsum']
  | smul z f _ hf =>
    obtain ⟨c, hc, hk, hsum⟩ := hf
    refine ⟨z • c, (fun χ hχ => Submodule.smul_mem _ z (hc χ hχ)), ?_, ?_⟩
    · intro χ hχ
      simp only [Pi.smul_apply, map_smul, hk χ hχ, smul_zero]
    · simp only [Pi.smul_apply, ← Finset.smul_sum, hsum]

/-- Uniform fixed-level source dimensions and an actual spectral root bound
give uniform split annihilators for arbitrary families of finite sums of
coefficients; neither tensor rank nor a global choice of exponent labels is
required. -/
theorem hasUniformSplitAnnihilators_of_fixedLevel_coefficients
    {κ : Type uκ} {Y : κ → Type uY} [∀ ω, AddCommGroup (Y ω)] [∀ ω, Module ℂ (Y ω)]
    (J : ∀ ω, Representation ℂ M (Y ω)) (j : A →* M) (a : A)
    (W : ∀ ω, Submodule ℂ (Y ω)) [∀ ω, FiniteDimensional ℂ (W ω)]
    (hW : ∀ ω a, ∀ y ∈ W ω, J ω (j a) y ∈ W ω) (d : ℕ)
    (hd : ∀ ω, Module.finrank ℂ (W ω) ≤ d) (F : κ → M → ℂ)
    (hF : ∀ ω, F ω ∈ coefficientSpaceFrom (J ω) (W ω))
    {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ < 1)
    (hbound : ∀ ω χ, W ω ⊓ jointGenEigenspace ((J ω).comp j) χ ≠ ⊥ →
      χ ∉ unitaryExponents A → ‖χ a‖ ≤ θ) :
    HasUniformSplitAnnihilators j a F := by
  classical
  choose s c hs hc hk hexp hsum using fun ω =>
    exists_bounded_coefficient_eigenfunctions (J ω) j a (W ω) (hW ω) (hd ω) (hF ω)
  have h := hasUniformSplitAnnihilators_of_variable_eigenfunctions
    j a s (fun _ χ => χ) c d d hθ0 hθ1 hs hc hk
      (fun ω χ hχ hχU => hbound ω χ (hexp ω χ hχ) hχU)
  simpa only [hsum] using h

end Langlands.HarishChandraSchwartz
