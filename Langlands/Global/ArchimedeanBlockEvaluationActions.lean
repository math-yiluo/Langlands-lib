import Langlands.Global.ArchimedeanBlockStandardEvaluation

/-! # Compact action and scalar evaluation formulas for standard block tensors -/

noncomputable section

open scoped BigOperators TensorProduct

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.ArchimedeanCompactBlocks

open _root_.Langlands.Archimedean
open GeneralLinear (BlockShape)
open AdelicBlockScalarSections (indexedEvaluation indexedEvaluation_injective indexedEvaluation_map_apply)

local notation "G" => Langlands.GeneralLinear

variable (𝕜 : Type) [RCLike 𝕜] {n : ℕ} (B : BlockShape n)

theorem localLeviHalf_ne_zero (m : B.Levi 𝕜) : localLeviHalf 𝕜 B m ≠ 0 := by
  have h (i : Fin B.length) : 0 < ‖(m i).val.det‖ :=
    norm_pos_iff.mpr ((Matrix.isUnit_iff_isUnit_det _).mp (m i).isUnit).ne_zero
  apply Complex.ofReal_ne_zero.mpr
  apply ne_of_gt
  apply Real.sqrt_pos_of_pos
  exact Finset.prod_pos fun i _ => Finset.prod_pos fun j _ =>
    div_pos (pow_pos (pow_pos (h i) _) _) (pow_pos (pow_pos (h j) _) _)

private theorem norm_det_compact {s : ℕ} (g : unitaryCompact 𝕜 s) :
    ‖g.val.val.det‖ = 1 := by
  have h := congrArg Matrix.det ((mem_unitaryCompact_iff 𝕜 s g.val).mp g.property)
  rw [Matrix.det_mul, Matrix.star_eq_conjTranspose, Matrix.det_conjTranspose, Matrix.det_one] at h
  have hn := congrArg norm h
  rw [norm_mul, norm_star, norm_one] at hn
  nlinarith [norm_nonneg g.val.val.det]

theorem localLeviHalf_mul_compact (m : B.Levi 𝕜) (q : ∀ i, unitaryCompact 𝕜 (B.size i)) :
    localLeviHalf 𝕜 B (m * fun i => (q i).val) = localLeviHalf 𝕜 B m := by
  have h (i : Fin B.length) : ‖(m i * (q i).val).val.det‖ = ‖(m i).val.det‖ := by
    rw [Units.val_mul, Matrix.det_mul, norm_mul, norm_det_compact 𝕜 (q i), mul_one]
  simp only [localLeviHalf, Pi.mul_apply, h]

@[simp]
theorem localLeviHalf_one : localLeviHalf 𝕜 B 1 = 1 := by
  simp [localLeviHalf]

namespace StandardBlockEvaluation

variable {𝕜 B} {W : Submodule ℂ (G n 𝕜 → ℂ)}
  {V : ∀ i, Submodule ℂ (G (B.size i) 𝕜 → ℂ)}
  (D : StandardBlockEvaluation 𝕜 B W V)

local notation "K" => unitaryCompact 𝕜 n
local notation "E" => indexedEvaluation (fun i => Submodule.subtype (V i))

theorem levi_value (k : K) (f : W) (m : B.Levi 𝕜) :
    f.val (B.leviEmbedding 𝕜 m * k.val) =
      localLeviHalf 𝕜 B m * E (D.evaluation k f) m := by
  simpa only [BlockShape.leviInParabolic_val, BlockShape.leviProjection_section] using
    D.parabolic_value k f (B.leviInParabolic 𝕜 m)

/-- Right translation of a standard vector corresponds to right multiplication
in the compact evaluation argument. -/
theorem evaluation_right (ρ : Representation ℂ K W)
    (hρ : ∀ (d : K) (x : W) (g : G n 𝕜), (ρ d x).val g = x.val (g * d.val))
    (k d : K) (f : W) : D.evaluation k (ρ d f) = D.evaluation (k * d) f := by
  apply indexedEvaluation_injective (fun i => (V i).subtype) (fun i => (V i).subtype_injective)
  funext m
  have h := D.levi_value k (ρ d f) m
  rw [hρ, mul_assoc] at h
  change f.val (B.leviEmbedding 𝕜 m * (k * d).val) = _ at h
  rw [D.levi_value (k * d) f m] at h
  exact mul_left_cancel₀ (localLeviHalf_ne_zero 𝕜 B m) h.symm

/-- Left Levi compact translation gives the tensor of the block compact actions. -/
theorem evaluation_left
    (σ : ∀ i, Representation ℂ (unitaryCompact 𝕜 (B.size i)) (V i))
    (hσ : ∀ i (d : unitaryCompact 𝕜 (B.size i)) (z : V i) (m : G (B.size i) 𝕜),
      (σ i d z).val m = z.val (m * d.val))
    (q : ∀ i, unitaryCompact 𝕜 (B.size i)) (k : K) (f : W) :
    D.evaluation (compactLeviEmbedding 𝕜 B q * k) f =
      PiTensorProduct.map (fun i => σ i (q i)) (D.evaluation k f) := by
  apply indexedEvaluation_injective (fun i => (V i).subtype) (fun i => (V i).subtype_injective)
  funext m
  rw [indexedEvaluation_map_apply (fun i => (V i).subtype)
    (fun i => σ i (q i)) (fun i y => y * (q i).val) (fun i z y => hσ i (q i) z y)]
  let d : B.Levi 𝕜 := fun i => (q i).val
  let k' := compactLeviEmbedding 𝕜 B q * k
  change E (D.evaluation k' f) m = E (D.evaluation k f) (m * d)
  have h := D.levi_value k' f m
  change f.val (B.leviEmbedding 𝕜 m * (B.leviEmbedding 𝕜 d * k.val)) = _ at h
  rw [← mul_assoc, ← map_mul, D.levi_value k f (m * d), localLeviHalf_mul_compact 𝕜 B m q] at h
  exact mul_left_cancel₀ (localLeviHalf_ne_zero 𝕜 B m) h.symm

/-- Compact tensor evaluations detect every vector of the ambient principal series. -/
theorem evaluation_separates {χ : ℕ → 𝕜ˣ → ℂ} (hW : W ≤ principalSeries 𝕜 n χ)
    (f : W) (hf : ∀ k, D.evaluation k f = 0) : f = 0 := by
  apply Subtype.ext
  apply PrincipalSeries.eq_zero_of_mem_principalSeries_of_eqOn_unitaryCompact (hW f.2)
  intro k hk
  have h := D.levi_value ⟨k, hk⟩ f 1
  simpa only [map_one, one_mul, localLeviHalf_one, hf, map_zero, Pi.zero_apply] using h

/-- A scalar coefficient of a compact evaluation is a finite combination of
left-Levi translates of the original standard function. The coefficients and
Levi points work at every compact argument for the given vector. -/
theorem exists_sum_of_levi_values (ρ : Representation ℂ K W)
    (hρ : ∀ (d : K) (x : W) (g : G n 𝕜), (ρ d x).val g = x.val (g * d.val))
    (f : W) (hf : FiniteVectors.IsFiniteVector ρ f) (ℓ : (⨂[ℂ] i, V i) →ₗ[ℂ] ℂ) :
    ∃ (a : ℕ) (m : Fin a → B.Levi 𝕜) (c : Fin a → ℂ),
      ∀ k : K, ℓ (D.evaluation k f) = ∑ j, c j * f.val (B.leviEmbedding 𝕜 (m j) * k.val) := by
  let S := (FiniteVectors.orbitSpan ρ f).map (D.evaluation 1)
  let : FiniteDimensional ℂ (FiniteVectors.orbitSpan ρ f) := hf
  let : ∀ i, AddCommGroup (V i) := fun i => Submodule.addCommGroup (V i)
  let : AddCommGroup S := Submodule.addCommGroup S
  let : Module ℂ S := Submodule.module S
  let : FiniteDimensional ℂ S := by dsimp only [S]; infer_instance
  let ev (m : B.Levi 𝕜) := (LinearMap.proj m).comp E
  have hsep : ∀ x ∈ S, (∀ m, ev m x = 0) → x = 0 := by
    intro x _ hx
    apply indexedEvaluation_injective (fun i => (V i).subtype) (fun i => (V i).subtype_injective)
    funext m
    rw [map_zero, Pi.zero_apply]
    exact hx m
  obtain ⟨a, m, c, h⟩ := Archimedean.exists_sum_of_separating ev S hsep ℓ
  refine ⟨a, m, fun j => c j * (localLeviHalf 𝕜 B (m j))⁻¹, fun k => ?_⟩
  have hk : D.evaluation k f ∈ S := by
    have hr := D.evaluation_right ρ hρ 1 k f
    rw [one_mul] at hr
    rw [← hr]
    exact ⟨ρ k f, FiniteVectors.action_mem_orbitSpan ρ _ _, rfl⟩
  rw [h _ hk]
  refine Finset.sum_congr rfl fun j _ => ?_
  change c j * E (D.evaluation k f) (m j) =
    c j * (localLeviHalf 𝕜 B (m j))⁻¹ * f.val (B.leviEmbedding 𝕜 (m j) * k.val)
  rw [D.levi_value, mul_assoc (c j), ← mul_assoc ((localLeviHalf 𝕜 B (m j))⁻¹),
    inv_mul_cancel₀ (localLeviHalf_ne_zero 𝕜 B (m j)), one_mul]

end StandardBlockEvaluation

end Langlands.Global.ArchimedeanCompactBlocks
