import Langlands.Geometry.Manifold.LinearLieGroup.Basic
import Mathlib.Geometry.Manifold.Instances.UnitsOfNormedAlgebra
import Mathlib.Order.CompletePartialOrder

/-!
# The unit group as a linear Lie group

For a complete normed real algebra `𝔸`:

* `expChartUnits g` is the exponential chart `x ↦ log (g⁻¹ x)` of `𝔸ˣ` at `g`, and it belongs to
  the maximal atlas of Mathlib's manifold structure on `𝔸ˣ` (`expChartUnits_mem_maximalAtlas`), so
  the exponential charts define the same smooth structure as Mathlib's chart `Units.val`;
* `isExpLieAlgebra_top`: the subgroup `⊤` of `𝔸ˣ` has the exponential Lie algebra `⊤`;
* `contMDiff_units_iff_top` (for finite-dimensional `𝔸`): a function on `𝔸ˣ` is smooth for
  Mathlib's charted space on `𝔸ˣ` exactly when its restriction to `⊤` is smooth for the exponential
  charts of `isExpLieAlgebra_top`; and `contMDiff_units_of_contDiff_val`: a map into `𝔸ˣ` is smooth
  when it is smooth into `𝔸`.

This is the case of `GL_n(ℝ)`, `GL_n(ℂ)` and of the units of every finite-dimensional real algebra.
-/

namespace Langlands.LinearLieGroup

open scoped Manifold ContDiff Topology
open NormedSpace Set

section UnitsChart

variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸]

local notation "𝔢" => expPartialHomeomorph 𝔸

/-- The exponential chart of `𝔸ˣ` at `g`: `x ↦ log (g⁻¹ x)`, with inverse `X ↦ g exp X`. -/
noncomputable def expChartUnits (g : 𝔸ˣ) : OpenPartialHomeomorph 𝔸ˣ 𝔸 where
  toFun x := (𝔢).symm ((g⁻¹ * x : 𝔸ˣ) : 𝔸)
  invFun X := g * expUnit 𝔸 X
  source := {x | ((g⁻¹ * x : 𝔸ˣ) : 𝔸) ∈ (𝔢).target}
  target := (𝔢).source
  map_source' x hx := (𝔢).map_target hx
  map_target' X hX := by
    simp only [mem_ofPred_eq, inv_mul_cancel_left, coe_expUnit]
    exact (𝔢).map_source hX
  left_inv' x hx := by
    have h2 : exp ((𝔢).symm ((g⁻¹ * x : 𝔸ˣ) : 𝔸)) = ((g⁻¹ * x : 𝔸ˣ) : 𝔸) := (𝔢).right_inv hx
    apply Units.ext
    show (g : 𝔸) * exp ((𝔢).symm ((g⁻¹ * x : 𝔸ˣ) : 𝔸)) = x
    rw [h2, ← Units.val_mul, mul_inv_cancel_left]
  right_inv' X hX := by
    simp only [inv_mul_cancel_left, coe_expUnit]
    exact (𝔢).left_inv hX
  open_source :=
      (𝔢).open_target.preimage (Units.continuous_val.comp (continuous_const.mul continuous_id))
  open_target := (𝔢).open_source
  continuousOn_toFun := (𝔢).continuousOn_symm.comp
    (Units.continuous_val.comp (continuous_const.mul continuous_id)).continuousOn (fun _ hx => hx)
  continuousOn_invFun := (continuous_const.mul (continuous_expUnit 𝔸)).continuousOn

/-- `g` is in the source of the exponential chart at `g`. -/
theorem mem_expChartUnits_source (g : 𝔸ˣ) : g ∈ (expChartUnits g).source := by
  show ((g⁻¹ * g : 𝔸ˣ) : 𝔸) ∈ (𝔢).target
  simpa using one_mem_expPartialHomeomorph_target 𝔸

/-- The exponential chart at `g` sends `g` to `0`. -/
theorem expChartUnits_self (g : 𝔸ˣ) : expChartUnits g g = 0 := by
  show (𝔢).symm ((g⁻¹ * g : 𝔸ˣ) : 𝔸) = 0
  simpa using expPartialHomeomorph_symm_one 𝔸

/-- The inverse of the exponential chart at `g` is `X ↦ g exp X`. -/
theorem expChartUnits_symm_apply (g : 𝔸ˣ) (X : 𝔸) :
    (((expChartUnits g).symm X : 𝔸ˣ) : 𝔸) = g * exp X := rfl

/-- The exponential charts of `𝔸ˣ` belong to the maximal atlas of Mathlib's manifold structure on
`𝔸ˣ` (whose single chart is the inclusion into `𝔸`): both transition maps are smooth. -/
theorem expChartUnits_mem_maximalAtlas (g : 𝔸ˣ) (n : WithTop ℕ∞) :
    expChartUnits g ∈ IsManifold.maximalAtlas 𝓘(ℝ, 𝔸) n 𝔸ˣ := by
  rw [IsManifold.mem_maximalAtlas_iff]
  intro e' he'
  obtain rfl : e' = _ := he'
  have h1 : (expChartUnits g).symm ≫ₕ
      Units.isOpenEmbedding_val.toOpenPartialHomeomorph (Units.val : 𝔸ˣ → 𝔸) ∈
      contDiffGroupoid n 𝓘(ℝ, 𝔸) := by
    rw [contDiffGroupoid, mem_groupoid_of_pregroupoid]
    constructor
    · simp only [contDiffPregroupoid, modelWithCornersSelf_coe, modelWithCornersSelf_coe_symm,
        Function.id_comp, Function.comp_id, preimage_id_eq, range_id, inter_univ]
      exact (contDiff_const.mul (contDiff_exp 𝔸)).contDiffOn.congr (fun X _ => rfl)
    · simp only [contDiffPregroupoid, modelWithCornersSelf_coe, modelWithCornersSelf_coe_symm,
        Function.id_comp, Function.comp_id, preimage_id_eq, range_id, inter_univ]
      set e0 := Units.isOpenEmbedding_val.toOpenPartialHomeomorph (Units.val : 𝔸ˣ → 𝔸)
      have hmaps : MapsTo (fun a : 𝔸 => ((g⁻¹ : 𝔸ˣ) : 𝔸) * a)
          ((expChartUnits g).symm ≫ₕ e0).symm.source (𝔢).target := by
        intro a ha
        rw [OpenPartialHomeomorph.symm_source, OpenPartialHomeomorph.trans_target] at ha
        have hr : ((e0.symm a : 𝔸ˣ) : 𝔸) = a := e0.right_inv ha.1
        have := ha.2
        simp only [mem_preimage] at this
        change (((g⁻¹ * e0.symm a : 𝔸ˣ) : 𝔸)) ∈ (𝔢).target at this
        rwa [Units.val_mul, hr] at this
      refine ((contDiffOn_expPartialHomeomorph_symm 𝔸).comp
        (contDiff_const.mul contDiff_id).contDiffOn hmaps).congr ?_
      intro a ha
      rw [OpenPartialHomeomorph.symm_source, OpenPartialHomeomorph.trans_target] at ha
      have hr : ((e0.symm a : 𝔸ˣ) : 𝔸) = a := e0.right_inv ha.1
      show (𝔢).symm (((g⁻¹ * e0.symm a : 𝔸ˣ) : 𝔸)) = _
      rw [Units.val_mul, hr]; rfl
  refine ⟨h1, ?_⟩
  have := (contDiffGroupoid n 𝓘(ℝ, 𝔸)).symm h1
  rwa [OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm, OpenPartialHomeomorph.symm_symm] at this

end UnitsChart

/-- The whole unit group `𝔸ˣ` has the exponential Lie algebra `𝔸`. -/
theorem isExpLieAlgebra_top {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] :
    IsExpLieAlgebra (⊤ : Subgroup 𝔸ˣ) (⊤ : Submodule ℝ 𝔸) where
  expUnit_mem _ _ := Subgroup.mem_top _
  exists_nhds := ⟨(expPartialHomeomorph 𝔸).source, (expPartialHomeomorph 𝔸).open_source,
    zero_mem_expPartialHomeomorph_source 𝔸, subset_rfl, fun _ _ _ => Submodule.mem_top⟩

end Langlands.LinearLieGroup

namespace Langlands.LinearLieGroup

open scoped Manifold ContDiff Topology
open NormedSpace Set

variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸]

/-- A map from a normed space into `𝔸ˣ` is smooth for Mathlib's manifold structure on `𝔸ˣ` when its
composition with `Units.val` is smooth (the inclusion is the only chart). -/
theorem contMDiff_units_of_contDiff_val {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (p : V → 𝔸ˣ) (hp : ContDiff ℝ ∞ (fun x => ((p x : 𝔸ˣ) : 𝔸))) :
    ContMDiff 𝓘(ℝ, V) 𝓘(ℝ, 𝔸) ∞ p := by
  rw [contMDiff_iff_target]
  refine ⟨?_, fun y => ?_⟩
  · rw [Units.isOpenEmbedding_val.isEmbedding.continuous_iff]
    exact hp.continuous
  · have : (extChartAt 𝓘(ℝ, 𝔸) y) ∘ p = fun x => ((p x : 𝔸ˣ) : 𝔸) := by
      funext x
      simp [extChartAt]
    rw [this]
    exact hp.contMDiff.contMDiffOn

/-- **The exponential structure on `⊤` is Mathlib's structure on `𝔸ˣ`.** A function `f : 𝔸ˣ → F` is
smooth for Mathlib's charted space on `𝔸ˣ` if and only if its restriction to `⊤ : Subgroup 𝔸ˣ` is
smooth for the exponential charts. Both sides say that `Y ↦ f (g exp Y)` is smooth for every `g`:
the right side by `IsExpLieAlgebra.contMDiff_iff_expG`, the left side because the exponential charts
of `𝔸ˣ` are in Mathlib's maximal atlas. -/
theorem contMDiff_units_iff_top [FiniteDimensional ℝ 𝔸] {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] (f : 𝔸ˣ → F) :
    ContMDiff 𝓘(ℝ, 𝔸) 𝓘(ℝ, F) ∞ f ↔
      (letI := (isExpLieAlgebra_top (𝔸 := 𝔸)).chartedSpace;
        ContMDiff 𝓘(ℝ, (⊤ : Submodule ℝ 𝔸)) 𝓘(ℝ, F) ∞ fun x : (⊤ : Subgroup 𝔸ˣ) => f x) := by
  rw [isExpLieAlgebra_top.contMDiff_iff_expG]
  constructor
  · intro hf g
    have hu : ContMDiff 𝓘(ℝ, (⊤ : Submodule ℝ 𝔸)) 𝓘(ℝ, 𝔸) ∞
        (fun Y : (⊤ : Submodule ℝ 𝔸) => (g : 𝔸ˣ) * expUnit 𝔸 (Y : 𝔸)) :=
      contMDiff_units_of_contDiff_val _ (by
        simp only [Units.val_mul, coe_expUnit]
        exact contDiff_const.mul
          ((contDiff_exp 𝔸).comp (Submodule.subtypeL (⊤ : Submodule ℝ 𝔸)).contDiff))
    exact (hf.comp hu).contDiff
  · intro hf x
    rw [← contMDiffWithinAt_univ,
      contMDiffWithinAt_iff_source_of_mem_maximalAtlas (expChartUnits_mem_maximalAtlas x ∞)
        (mem_expChartUnits_source x)]
    simp only [preimage_univ, univ_inter, modelWithCornersSelf_coe, range_id,
      OpenPartialHomeomorph.extend_coe, OpenPartialHomeomorph.extend_coe_symm,
      modelWithCornersSelf_coe_symm, Function.comp_id, Function.id_comp, contMDiffWithinAt_univ,
      expChartUnits_self]
    let c : 𝔸 →L[ℝ] (⊤ : Submodule ℝ 𝔸) :=
      (ContinuousLinearMap.id ℝ 𝔸).codRestrict ⊤ fun _ => Submodule.mem_top
    have e : f ∘ (expChartUnits x).symm =
        (fun Y : (⊤ : Submodule ℝ 𝔸) =>
          f (((⟨x, Subgroup.mem_top x⟩ : (⊤ : Subgroup 𝔸ˣ)) *
            isExpLieAlgebra_top.expG Y : (⊤ : Subgroup 𝔸ˣ)) : 𝔸ˣ)) ∘ c := by
      funext X
      rfl
    rw [e]
    exact ((hf ⟨x, Subgroup.mem_top x⟩).comp c.contDiff).contMDiff.contMDiffAt

end Langlands.LinearLieGroup
