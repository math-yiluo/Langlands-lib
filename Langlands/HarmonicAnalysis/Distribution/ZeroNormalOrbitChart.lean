import Langlands.HarmonicAnalysis.Distribution.ChartJacobianDensity

/-! # Orbit charts on zero-normal fibers -/

noncomputable section

open Set
open scoped ContDiff

set_option autoImplicit false

namespace Langlands.HarmonicAnalysis

variable {O Z N : Type*}
  [NormedAddCommGroup O] [NormedAddCommGroup Z] [NormedAddCommGroup N]

local notation "Coord" => ((O × Z) × N)

/-- The chart sends each zero-normal fiber into the fiber with the same slice coordinate. -/
def PreservesZeroNormalFibers (Ψ : OpenPartialHomeomorph Coord Coord) : Prop :=
  ∀ p : O × Z, (p, 0) ∈ Ψ.source → Ψ (p, 0) = (((Ψ (p, 0)).1.1, p.2), 0)

/-- The induced open partial homeomorphism on one orbit fiber of the zero-normal plane. -/
def zeroNormalOrbitChart (Ψ : OpenPartialHomeomorph Coord Coord)
    (hΨ : PreservesZeroNormalFibers Ψ) (hΨi : PreservesZeroNormalFibers Ψ.symm) (z : Z) :
    OpenPartialHomeomorph O O := by
  let sectionAt (t : O) : Coord := ((t, z), 0)
  have hs : Continuous sectionAt := (continuous_id.prodMk continuous_const).prodMk continuous_const
  have h (t : O) (ht : sectionAt t ∈ Ψ.source) :
      Ψ (sectionAt t) = sectionAt (Ψ (sectionAt t)).1.1 := hΨ (t, z) ht
  have hi (t : O) (ht : sectionAt t ∈ Ψ.target) :
      Ψ.symm (sectionAt t) = sectionAt (Ψ.symm (sectionAt t)).1.1 := hΨi (t, z) ht
  exact
    { toFun := fun t => (Ψ (sectionAt t)).1.1
      invFun := fun t => (Ψ.symm (sectionAt t)).1.1
      source := sectionAt ⁻¹' Ψ.source
      target := sectionAt ⁻¹' Ψ.target
      map_source' := fun {t} ht => by
        change sectionAt (Ψ (sectionAt t)).1.1 ∈ Ψ.target
        rw [← h t ht]
        exact Ψ.map_source ht
      map_target' := fun {t} ht => by
        change sectionAt (Ψ.symm (sectionAt t)).1.1 ∈ Ψ.source
        rw [← hi t ht]
        exact Ψ.map_target ht
      left_inv' := fun {t} ht => by
        rw [← h t ht, Ψ.left_inv ht]
      right_inv' := fun {t} ht => by
        rw [← hi t ht, Ψ.right_inv ht]
      continuousOn_toFun := (Ψ.continuousOn.comp hs.continuousOn fun _ ht => ht).fst.fst
      continuousOn_invFun := (Ψ.symm.continuousOn.comp hs.continuousOn fun _ ht => ht).fst.fst
      open_source := Ψ.open_source.preimage hs
      open_target := Ψ.open_target.preimage hs }

@[simp]
theorem zeroNormalOrbitChart_apply (Ψ : OpenPartialHomeomorph Coord Coord)
    (hΨ : PreservesZeroNormalFibers Ψ) (hΨi : PreservesZeroNormalFibers Ψ.symm) (z : Z) (t : O) :
    zeroNormalOrbitChart Ψ hΨ hΨi z t = (Ψ ((t, z), 0)).1.1 := rfl

@[simp]
theorem zeroNormalOrbitChart_symm_apply (Ψ : OpenPartialHomeomorph Coord Coord)
    (hΨ : PreservesZeroNormalFibers Ψ) (hΨi : PreservesZeroNormalFibers Ψ.symm) (z : Z) (t : O) :
    (zeroNormalOrbitChart Ψ hΨ hΨi z).symm t = (Ψ.symm ((t, z), 0)).1.1 := rfl

@[simp]
theorem zeroNormalOrbitChart_source (Ψ : OpenPartialHomeomorph Coord Coord)
    (hΨ : PreservesZeroNormalFibers Ψ) (hΨi : PreservesZeroNormalFibers Ψ.symm) (z : Z) :
    (zeroNormalOrbitChart Ψ hΨ hΨi z).source = (fun t => ((t, z), 0)) ⁻¹' Ψ.source := rfl

@[simp]
theorem zeroNormalOrbitChart_target (Ψ : OpenPartialHomeomorph Coord Coord)
    (hΨ : PreservesZeroNormalFibers Ψ) (hΨi : PreservesZeroNormalFibers Ψ.symm) (z : Z) :
    (zeroNormalOrbitChart Ψ hΨ hΨi z).target = (fun t => ((t, z), 0)) ⁻¹' Ψ.target := rfl

variable [NormedSpace ℝ O] [NormedSpace ℝ Z] [NormedSpace ℝ N]

private def orbitInclusion : O →L[ℝ] Coord :=
  (ContinuousLinearMap.inl ℝ (O × Z) N).comp (ContinuousLinearMap.inl ℝ O Z)

private def orbitProjection : Coord →L[ℝ] O :=
  (ContinuousLinearMap.fst ℝ O Z).comp (ContinuousLinearMap.fst ℝ (O × Z) N)

/-- The orbit block of the derivative at a point of the zero-normal plane. -/
def zeroNormalOrbitDerivative (Ψ : Coord → Coord) (p : O × Z) : O →L[ℝ] O :=
  orbitProjection.comp ((fderiv ℝ Ψ (p, 0)).comp orbitInclusion)

@[simp]
theorem zeroNormalOrbitDerivative_apply (Ψ : Coord → Coord) (p : O × Z) (v : O) :
    zeroNormalOrbitDerivative Ψ p v = (fderiv ℝ Ψ (p, 0) ((v, 0), 0)).1.1 := rfl

theorem hasFDerivAt_zeroNormalOrbitChart {Ψ : OpenPartialHomeomorph Coord Coord}
    (hs : ContDiffOn ℝ ∞ Ψ Ψ.source) (hΨ : PreservesZeroNormalFibers Ψ)
    (hΨi : PreservesZeroNormalFibers Ψ.symm) (z : Z) {t : O} (ht : ((t, z), 0) ∈ Ψ.source) :
    HasFDerivAt (zeroNormalOrbitChart Ψ hΨ hΨi z) (zeroNormalOrbitDerivative Ψ (t, z)) t := by
  have hj : HasFDerivAt (fun s : O => ((s, z), (0 : N))) orbitInclusion t := by
    have h₁ := (hasFDerivAt_id (𝕜 := ℝ) t).prodMk (hasFDerivAt_const (𝕜 := ℝ) z t)
    refine (h₁.prodMk (hasFDerivAt_const (𝕜 := ℝ) (0 : N) t)).congr_fderiv ?_
    ext1 v
    rfl
  have hd := (hs.contDiffAt (Ψ.open_source.mem_nhds ht)).differentiableAt (by simp)
  exact orbitProjection.hasFDerivAt.comp t (hd.hasFDerivAt.comp t hj)

theorem contDiffOn_zeroNormalOrbitChart {Ψ : OpenPartialHomeomorph Coord Coord}
    (hs : ContDiffOn ℝ ∞ Ψ Ψ.source) (hΨ : PreservesZeroNormalFibers Ψ)
    (hΨi : PreservesZeroNormalFibers Ψ.symm) (z : Z) :
    ContDiffOn ℝ ∞ (zeroNormalOrbitChart Ψ hΨ hΨi z) (zeroNormalOrbitChart Ψ hΨ hΨi z).source :=
  (hs.comp ((contDiff_id.prodMk contDiff_const).prodMk contDiff_const).contDiffOn
    (fun _ ht => ht)).fst.fst

/-- Absolute Jacobian for the change of variables in the orbit coordinate. -/
def zeroNormalOrbitJacobian (Ψ : Coord → Coord) (p : O × Z) : ℝ :=
  |(zeroNormalOrbitDerivative Ψ p).det|

theorem zeroNormalOrbitJacobian_pos {Ψ : OpenPartialHomeomorph Coord Coord}
    (hs : ContDiffOn ℝ ∞ Ψ Ψ.source) (hi : ContDiffOn ℝ ∞ Ψ.symm Ψ.target)
    (hΨ : PreservesZeroNormalFibers Ψ) (hΨi : PreservesZeroNormalFibers Ψ.symm)
    {p : O × Z} (hp : (p, 0) ∈ Ψ.source) : 0 < zeroNormalOrbitJacobian Ψ p := by
  let e := zeroNormalOrbitChart Ψ hΨ hΨi p.2
  have h := chartAbsJacobian_pos (e := e)
    (contDiffOn_zeroNormalOrbitChart hs hΨ hΨi p.2)
    (contDiffOn_zeroNormalOrbitChart (Ψ := Ψ.symm) hi hΨi hΨ p.2)
    (ContinuousLinearEquiv.refl ℝ O) (x := p.1) hp
  change 0 < |((ContinuousLinearMap.id ℝ O).comp (fderiv ℝ e p.1)).det| at h
  rwa [ContinuousLinearMap.id_comp, (hasFDerivAt_zeroNormalOrbitChart hs hΨ hΨi p.2 hp).fderiv] at h

theorem contDiffOn_zeroNormalOrbitJacobian [FiniteDimensional ℝ O]
    {Ψ : OpenPartialHomeomorph Coord Coord} (hs : ContDiffOn ℝ ∞ Ψ Ψ.source)
    (hi : ContDiffOn ℝ ∞ Ψ.symm Ψ.target)
    (hΨ : PreservesZeroNormalFibers Ψ) (hΨi : PreservesZeroNormalFibers Ψ.symm) :
    ContDiffOn ℝ ∞ (zeroNormalOrbitJacobian Ψ) {p | (p, 0) ∈ Ψ.source} := by
  let pre := (ContinuousLinearMap.compL ℝ O Coord Coord).flip (orbitInclusion (Z := Z) (N := N))
  let post := ContinuousLinearMap.compL ℝ O Coord O (orbitProjection (Z := Z) (N := N))
  have hf : ContDiffOn ℝ ∞ (fun p : O × Z => fderiv ℝ Ψ (p, 0)) {p | (p, 0) ∈ Ψ.source} :=
    (hs.fderiv_of_isOpen Ψ.open_source (by simp)).comp
      (contDiff_id.prodMk contDiff_const).contDiffOn (fun _ hp => hp)
  have h : ContDiffOn ℝ ∞ (zeroNormalOrbitDerivative Ψ) {p | (p, 0) ∈ Ψ.source} :=
    (post.comp pre).contDiff.comp_contDiffOn hf
  exact (Langlands.Analysis.contDiff_continuousLinearMap_det.comp_contDiffOn h).abs
    (fun p hp => abs_pos.mp (zeroNormalOrbitJacobian_pos hs hi hΨ hΨi hp))

end Langlands.HarmonicAnalysis
