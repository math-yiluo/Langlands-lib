import Langlands.GroupScheme.General.SmoothAffinePointLieGroup
import Langlands.GroupScheme.Rational.SubgroupProductGeometry
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff

/-! # Square roots of norm-one points near the identity -/

noncomputable section

universe u v

open CategoryTheory AlgebraicGeometry Filter Topology
open scoped Manifold ContDiff CategoryTheory.MonObj

namespace Langlands.GroupScheme.QuadraticToralReduction

set_option backward.isDefEq.respectTransparency false

private theorem exists_squareLocalHomeomorph
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {A : Type v} [Group A] [TopologicalSpace A] [ChartedSpace E A]
    [LieGroup 𝓘(ℝ, E) ∞ A] :
    ∃ e : OpenPartialHomeomorph A A, 1 ∈ e.source ∧ ∀ x ∈ e.source, e x = x * x := by
  let I := 𝓘(ℝ, E)
  let f : A → A := fun x => x * x
  have hf₁ : f 1 = 1 := mul_one 1
  have hf : ContMDiff I I ∞ f := contMDiff_id.mul contMDiff_id
  have hmul := (contMDiff_mul (G := A) I ∞).mdifferentiableAt (by simp)
    (x := ((1, 1) : A × A))
  have hD (v : TangentSpace I (1 : A)) : mfderiv% f 1 v = v + v := by
    have h := mfderiv_comp_apply (I := I) (I' := I.prod I) (I'' := I)
      (x := (1 : A)) (f := fun x => (x, x)) (g := fun p : A × A => p.1 * p.2)
      hmul (mdifferentiableAt_id.prodMk mdifferentiableAt_id) v
    change mfderiv% f 1 v = _ at h
    have hdiag : (mfderiv I (I.prod I) (fun x : A => (x, x)) 1) v = (v, v) := by
      have h := mfderiv_prodMk (I := I) (I' := I) (I'' := I) (x := (1 : A))
        mdifferentiableAt_id mdifferentiableAt_id
      change mfderiv I (I.prod I) (fun x : A => (x, x)) 1 = _ at h
      rw [h, mfderiv_id]
      rfl
    rw [h, hdiag, mfderiv_prod_eq_add_apply hmul]
    erw [show (fun z : A => z * 1) = id from funext mul_one,
      show (fun z : A => 1 * z) = id from funext one_mul, mfderiv_id]
    rfl
  let c := chartAt E (1 : A)
  let g := writtenInExtChartAt I I 1 f
  have hI : Set.range I = Set.univ := by simp [I]
  have hcd : ContDiffAt ℝ ∞ g (c 1) := by
    have h := (contMDiffAt_iff.mp (hf 1)).2
    rw [hI, contDiffWithinAt_univ] at h
    exact h
  have hfd : fderiv ℝ g (c 1) = mfderiv% f 1 := by
    rw [mfderiv, ite_eq_left (hf.mdifferentiableAt (by simp))]
    rw [hI, fderivWithin_univ]
    rfl
  let eD : E ≃L[ℝ] E := {
    toLinearEquiv := LinearEquiv.smulOfNeZero ℝ E 2 (by norm_num)
    continuous_toFun := continuous_const_smul _
    continuous_invFun := continuous_const_smul _ }
  have hd : HasFDerivAt g (eD : E →L[ℝ] E) (c 1) := by
    convert (hcd.differentiableAt (by simp)).hasFDerivAt using 1
    rw [hfd]
    ext v
    change (2 : ℝ) • v = mfderiv% f 1 v
    rw [hD, two_smul]
  let j := hcd.toOpenPartialHomeomorph g hd (by simp)
  let O := c.source ∩ f ⁻¹' c.source
  let c₀ := c.restr O
  let e := (c₀.trans j).trans c.symm
  have hsrc : (1 : A) ∈ c.source := mem_chart_source _ _
  have hj : c 1 ∈ j.source := hcd.mem_toOpenPartialHomeomorph_source hd (by simp)
  have happly (x : A) (hx : x ∈ c.source) : j (c x) = c (f x) := by
    change g (c x) = _
    have hchart : (extChartAt I (1 : A)).symm (c x) = x := c.left_inv hx
    dsimp only [g, writtenInExtChartAt, Function.comp_apply]
    rw [hf₁, hchart]
    rfl
  have hO : IsOpen O := c.open_source.inter (c.open_source.preimage hf.continuous)
  have hmem : (1 : A) ∈ e.source := by
    refine ⟨⟨⟨hsrc, ?_⟩, hj⟩, ?_⟩
    · rw [hO.interior_eq]
      refine ⟨hsrc, ?_⟩
      change f 1 ∈ c.source
      rw [hf₁]
      exact hsrc
    · change j (c 1) ∈ c.target
      rw [happly 1 hsrc, hf₁]
      exact c.map_source hsrc
  refine ⟨e, hmem, fun x hx => ?_⟩
  change c.symm (j (c x)) = f x
  have hfx : f x ∈ c.source := (interior_subset hx.1.1.2).2
  rw [happly x hx.1.1.1, c.left_inv hfx]

/-- A norm-one point sufficiently close to the identity has a square root
on which the given continuous automorphism acts by inversion. -/
theorem exists_normOneSquareNeighborhood
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {A : Type v} [Group A] [TopologicalSpace A] [ChartedSpace E A]
    [LieGroup 𝓘(ℝ, E) ∞ A]
    (φ : A ≃* A) (hφ : Continuous φ) :
    ∃ V : Set A, IsOpen V ∧ (1 : A) ∈ V ∧
      ∀ y ∈ V, φ y = y⁻¹ → ∃ s : A, s * s = y ∧ φ s = s⁻¹ := by
  obtain ⟨e, he₁, he⟩ := exists_squareLocalHomeomorph (E := E) (A := A)
  let D := e.source ∩ φ ⁻¹' e.source ∩ Inv.inv ⁻¹' e.source
  have hD : IsOpen D := (e.open_source.inter (e.open_source.preimage hφ)).inter
    (e.open_source.preimage ((contMDiff_inv (G := A) 𝓘(ℝ, E) ∞).continuous))
  have hD₁ : (1 : A) ∈ D := by simpa [D] using he₁
  have hO : IsOpen (e '' D) := e.isOpen_image_of_subset_source hD (fun _ h => h.1.1)
  refine ⟨e '' D, hO, ⟨1, hD₁, ?_⟩, ?_⟩
  · rw [he 1 he₁, mul_one]
  · rintro y ⟨s, hs, rfl⟩ hy
    refine ⟨s, (he s hs.1.1).symm, e.injOn hs.1.2 hs.2 ?_⟩
    rw [he _ hs.1.2, he _ hs.2, ← map_mul, ← he _ hs.1.1, hy, he _ hs.1.1,
      mul_inv_rev]

end Langlands.GroupScheme.QuadraticToralReduction
