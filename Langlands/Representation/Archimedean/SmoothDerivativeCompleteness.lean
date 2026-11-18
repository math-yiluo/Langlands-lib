import Langlands.Representation.Archimedean.SmoothDerivativeTopology
import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.UniformLimitsDeriv
import Mathlib.Geometry.Manifold.Instances.UnitsOfNormedAlgebra

/-! # Closed derivative coordinates for smooth vectors of groups of units -/

noncomputable section

open scoped Manifold ContDiff Topology
open Filter Set

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Archimedean.DerivativeSmoothVectors

section UniformStructure

variable {𝔤 : Type*} [NormedAddCommGroup 𝔤] [NormedSpace ℝ 𝔤]
  {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ 𝔤 H)
  {G : Type*} [Group G] [TopologicalSpace G] [ChartedSpace H G] [LieGroup I ∞ G]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] (π : G →* (E →L[ℂ] E))

/-- The coordinate uniformity induces the existing genuine word-derivative topology. -/
instance derivativeUniformSpace : UniformSpace (DerivativeSmoothVectors I π) :=
  UniformSpace.comap (derivativeCoordinates I π) inferInstance

theorem isUniformInducing_derivativeCoordinates :
    IsUniformInducing (derivativeCoordinates I π) :=
  ⟨rfl⟩

instance : IsUniformAddGroup (DerivativeSmoothVectors I π) :=
  IsUniformInducing.isUniformAddGroup (derivativeCoordinates I π)
    (isUniformInducing_derivativeCoordinates I π)

end UniformStructure

variable {A : Type*} [NormedRing A] [CompleteSpace A]

private def unitDomain (A : Type*) [NormedRing A] : Set A :=
  Set.range (Units.val : Aˣ → A)

private theorem isOpen_unitDomain : IsOpen (unitDomain A) :=
  Units.isOpenEmbedding_val.isOpen_range

private def unitChart (A : Type*) [NormedRing A] [CompleteSpace A] :
    OpenPartialHomeomorph Aˣ A :=
  Units.isOpenEmbedding_val.toOpenPartialHomeomorph Units.val

private theorem unitChart_symm_val (g : Aˣ) : (unitChart A).symm (g : A) = g :=
  Units.isOpenEmbedding_val.toOpenPartialHomeomorph_left_inv Units.val

variable [NormedAlgebra ℝ A] in
private theorem contMDiffOn_unitChart_symm :
    ContMDiffOn 𝓘(ℝ, A) 𝓘(ℝ, A) ∞ (unitChart A).symm (unitDomain A) :=
  contMDiffOn_isOpenEmbedding_symm (I := 𝓘(ℝ, A)) Units.isOpenEmbedding_val

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  (R : Aˣ →* (E →L[ℂ] E))

private def orbitInCoordinates (v : E) (x : A) : E :=
  R ((unitChart A).symm x) v

private theorem orbitInCoordinates_val (v : E) (g : Aˣ) :
    orbitInCoordinates R v (g : A) = R g v := by
  rw [orbitInCoordinates, unitChart_symm_val]

variable [NormedAlgebra ℝ A]

private theorem contDiffOn_orbitInCoordinates {v : E}
    (hv : IsSmoothVector 𝓘(ℝ, A) R v) :
    ContDiffOn ℝ ∞ (orbitInCoordinates R v) (unitDomain A) :=
  (hv.comp_contMDiffOn contMDiffOn_unitChart_symm).contDiffOn

private theorem hasFDerivAt_orbitInCoordinates {v : E}
    (hv : IsSmoothVector 𝓘(ℝ, A) R v) (g : Aˣ) :
    HasFDerivAt (orbitInCoordinates R v)
      (((R g).restrictScalars ℝ).comp
        ((mfderiv 𝓘(ℝ, A) 𝓘(ℝ, E) (orbitMap R v) 1).comp
          (ContinuousLinearMap.mul ℝ A (g⁻¹ : Aˣ).val))) (g : A) := by
  let f := orbitInCoordinates R v
  have hf : DifferentiableAt ℝ f (1 : A) :=
    ((contDiffOn_orbitInCoordinates R hv).contDiffAt
      (isOpen_unitDomain.mem_nhds ⟨(1 : Aˣ), rfl⟩)).differentiableAt (by simp)
  have hval : mfderiv 𝓘(ℝ, A) 𝓘(ℝ, A) (Units.val : Aˣ → A) (1 : Aˣ) =
      ContinuousLinearMap.id ℝ A :=
    mfderiv_extChartAt_self (I := 𝓘(ℝ, A)) (x := (1 : Aˣ))
  have heq : orbitMap R v = f ∘ Units.val := by
    funext u
    exact (orbitInCoordinates_val R v u).symm
  have hderiv : mfderiv 𝓘(ℝ, A) 𝓘(ℝ, E) (orbitMap R v) 1 = fderiv ℝ f 1 := by
    rw [heq, mfderiv_comp (1 : Aˣ) hf.mdifferentiableAt
      ((Units.contMDiff_val (n := ∞)).mdifferentiableAt (by simp)), hval,
      mfderiv_eq_fderiv]
    change (fderiv ℝ f 1).comp (ContinuousLinearMap.id ℝ A) = fderiv ℝ f 1
    exact ContinuousLinearMap.comp_id _
  let T := ContinuousLinearMap.mul ℝ A (g⁻¹ : Aˣ).val
  have hT : T (g : A) = 1 := Units.inv_mul g
  have hfg : HasFDerivAt f (fderiv ℝ f 1) (T (g : A)) := hT.symm ▸ hf.hasFDerivAt
  rw [hderiv]
  apply (((R g).restrictScalars ℝ).hasFDerivAt.comp (g : A)
    (hfg.comp (g : A) T.hasFDerivAt)).congr_of_eventuallyEq
  filter_upwards [isOpen_unitDomain.mem_nhds (show (g : A) ∈ unitDomain A from ⟨g, rfl⟩)]
    with x hx
  obtain ⟨u, rfl⟩ := hx
  change f (u : A) = R g (f ((g⁻¹ * u : Aˣ) : A))
  simp only [f, orbitInCoordinates_val, ← mul_apply_eq_comp, ← map_mul,
    mul_inv_cancel_left]

private theorem hasFDerivAt_orbitInCoordinates_one {v : E}
    (hv : IsSmoothVector 𝓘(ℝ, A) R v) :
    HasFDerivAt (orbitInCoordinates R v) (mfderiv 𝓘(ℝ, A) 𝓘(ℝ, E) (orbitMap R v) 1)
      (1 : A) := by
  let D : A →L[ℝ] E := mfderiv 𝓘(ℝ, A) 𝓘(ℝ, E) (orbitMap R v) 1
  have hD : ((R (1 : Aˣ)).restrictScalars ℝ).comp
      (D.comp (ContinuousLinearMap.mul ℝ A ((1 : Aˣ)⁻¹).val)) = D := by
    ext1 X
    change R (1 : Aˣ) (D (((1 : Aˣ)⁻¹).val * X)) = D X
    rw [inv_one, Units.val_one, one_mul, map_one, one_apply_eq_self]
  have h := hasFDerivAt_orbitInCoordinates R hv 1
  change HasFDerivAt (orbitInCoordinates R v) _ (1 : A) at h
  rwa [show mfderiv 𝓘(ℝ, A) 𝓘(ℝ, E) (orbitMap R v) 1 = D from rfl, hD] at h

variable [FiniteDimensional ℝ A]

private def orbitJet {ι : Type*} [Fintype ι] (b : Module.Basis ι ℝ A)
    (v : ι → E) (x : A) : A →L[ℝ] E :=
  ∑ i, (((b.coord i).toContinuousLinearMap).comp
    (ContinuousLinearMap.mul ℝ A (((unitChart A).symm x)⁻¹ : Aˣ).val)).smulRight
      (orbitInCoordinates R (v i) x)

private theorem orbitJet_apply {ι : Type*} [Fintype ι] (b : Module.Basis ι ℝ A)
    (v : ι → E) (x Y : A) :
    orbitJet R b v x Y =
      ∑ i, b.coord i ((((unitChart A).symm x)⁻¹ : Aˣ).val * Y) •
        orbitInCoordinates R (v i) x := by
  simp [orbitJet]

private theorem continuousAt_orbitJet {ι : Type*} [Fintype ι] (b : Module.Basis ι ℝ A)
    (hR : IsContinuousRepresentation R) {x : A} (hx : x ∈ unitDomain A) (v : ι → E) :
    ContinuousAt (fun q : A × (ι → E) => orbitJet R b q.2 q.1) (x, v) := by
  have hlift : ContinuousAt (unitChart A).symm x :=
    (contMDiffOn_unitChart_symm.continuousOn x hx).continuousAt
      (isOpen_unitDomain.mem_nhds hx)
  have hp : ContinuousAt (fun q : A × (ι → E) => (unitChart A).symm q.1) (x, v) :=
    hlift.comp continuousAt_fst
  apply continuousAt_clm_apply.mpr
  intro Y
  simp_rw [orbitJet_apply]
  apply tendsto_finsetSum
  intro i _
  apply ContinuousAt.smul (M := ℝ)
  · exact ((b.coord i).toContinuousLinearMap.continuous.continuousAt.comp
      ((Units.continuous_coe_inv.continuousAt.comp hp).mul continuousAt_const))
  · exact hR.continuousAt.comp
      (hp.prodMk ((continuous_apply i).continuousAt.comp continuousAt_snd))

private theorem orbitJet_lieDerivative_apply {ι : Type*} [Fintype ι]
    (b : Module.Basis ι ℝ A) (v : E) (g : Aˣ) (Y : A) :
    orbitJet R b (fun i => lieDerivative 𝓘(ℝ, A) R (b i) v) (g : A) Y =
      R g (lieDerivative 𝓘(ℝ, A) R ((g⁻¹ : Aˣ).val * Y) v) := by
  rw [orbitJet_apply, unitChart_symm_val]
  simp only [orbitInCoordinates_val]
  let D : A →L[ℝ] E := mfderiv 𝓘(ℝ, A) 𝓘(ℝ, E) (orbitMap R v) 1
  let T := ((R g).restrictScalars ℝ).comp D
  let Z := (g⁻¹ : Aˣ).val * Y
  change ∑ i, b.coord i Z • T (b i) = T Z
  simpa only [map_sum, map_smul, Module.Basis.coord_apply] using congrArg T (b.sum_repr Z)

private theorem hasFDerivAt_orbitJet {ι : Type*} [Fintype ι] (b : Module.Basis ι ℝ A)
    {v : E} (hv : IsSmoothVector 𝓘(ℝ, A) R v) (g : Aˣ) :
    HasFDerivAt (orbitInCoordinates R v)
      (orbitJet R b (fun i => lieDerivative 𝓘(ℝ, A) R (b i) v) (g : A)) (g : A) := by
  convert hasFDerivAt_orbitInCoordinates R hv g using 1
  ext Y
  exact orbitJet_lieDerivative_apply R b v g Y

private theorem contDiffOn_orbitJet_apply {ι : Type*} [Fintype ι] (b : Module.Basis ι ℝ A)
    {k : ℕ} {v : ι → E}
    (hv : ∀ i, ContDiffOn ℝ k (orbitInCoordinates R (v i)) (unitDomain A)) (Y : A) :
    ContDiffOn ℝ k (fun x => orbitJet R b v x Y) (unitDomain A) := by
  have hInv : ContDiffOn ℝ ∞ (fun x : A => (((unitChart A).symm x)⁻¹ : Aˣ).val)
      (unitDomain A) :=
    ((Units.contMDiff_val.comp (contMDiff_inv _ _)).comp_contMDiffOn
      contMDiffOn_unitChart_symm).contDiffOn
  simp_rw [orbitJet_apply]
  apply ContDiffOn.sum
  intro i _
  exact ((b.coord i).toContinuousLinearMap.contDiff.comp_contDiffOn
    ((hInv.of_le (by simp)).mul contDiffOn_const)).smul (hv i)

private theorem tendstoLocallyUniformlyOn_orbitJet {ι κ : Type*} [Fintype ι]
    (b : Module.Basis ι ℝ A) (hR : IsContinuousRepresentation R)
    {l : Filter κ} {v : κ → ι → E} {w : ι → E} (h : Tendsto v l (𝓝 w)) :
    TendstoLocallyUniformlyOn (fun a => orbitJet R b (v a)) (orbitJet R b w) l
      (unitDomain A) := by
  refine tendstoLocallyUniformlyOn_iff_filter.mpr ?_
  intro x hx
  rw [isOpen_unitDomain.nhdsWithin_eq hx]
  refine tendstoUniformlyOnFilter_iff_tendsto.mpr ?_
  let p : Filter (κ × A) := l ×ˢ 𝓝 x
  let F : A × (ι → E) → (A →L[ℝ] E) := fun q => orbitJet R b q.2 q.1
  have hc : Tendsto F (𝓝 (x, w)) (𝓝 (F (x, w))) :=
    (continuousAt_orbitJet R b hR hx w).tendsto
  have hx' : Tendsto (fun q : κ × A => q.2) p (𝓝 x) := tendsto_snd
  have hv : Tendsto (fun q : κ × A => v q.1) p (𝓝 w) :=
    h.comp (show Tendsto (fun q : κ × A => q.1) p l from tendsto_fst)
  have ha : Tendsto (fun q : κ × A => F (q.2, v q.1)) p (𝓝 (F (x, w))) :=
    hc.comp (hx'.prodMk_nhds hv)
  have hb : Tendsto (fun q : κ × A => F (q.2, w)) p (𝓝 (F (x, w))) :=
    hc.comp (hx'.prodMk_nhds tendsto_const_nhds)
  exact (hb.prodMk_nhds ha).mono_right (nhds_le_uniformity _)

/-- Limits of all genuine Lie-word coordinates are coordinates of a smooth vector. -/
theorem isClosed_range_derivativeCoordinates_units (hR : IsContinuousRepresentation R) :
    IsClosed (Set.range (derivativeCoordinates 𝓘(ℝ, A) R)) := by
  classical
  apply isClosed_of_closure_subset
  intro w hw
  let D := DerivativeSmoothVectors 𝓘(ℝ, A) R
  let coords := derivativeCoordinates 𝓘(ℝ, A) R
  let l : Filter D := comap coords (𝓝 w)
  have : NeBot l := by
    change NeBot (comap coords (𝓝 w))
    rw [Filter.comap_neBot_iff]
    intro U hU
    obtain ⟨x, hx, ⟨v, rfl⟩⟩ := (mem_closure_iff_nhds.mp hw) U hU
    exact ⟨v, hx⟩
  have hcoords : ∀ s, Tendsto (fun v : D => coords v s) l (𝓝 (w s)) :=
    tendsto_pi_nhds.mp tendsto_comap
  let b := Module.finBasis ℝ A
  have hderiv (s : List A) (g : Aˣ) :
      HasFDerivAt (orbitInCoordinates R (w s)) (orbitJet R b (fun i => w (b i :: s)) g) g := by
    apply hasFDerivAt_of_tendstoLocallyUniformlyOn (l := l) isOpen_unitDomain
      (tendstoLocallyUniformlyOn_orbitJet R b hR
        (tendsto_pi_nhds.mpr fun i => hcoords (b i :: s)))
      (f := fun v => orbitInCoordinates R (coords v s))
    · rintro v _ ⟨u, rfl⟩
      let sv := smoothIteratedLieDerivative 𝓘(ℝ, A) R s (toSmooth 𝓘(ℝ, A) R v)
      simp only [coords, derivativeCoordinates_apply, iteratedLieDerivative_cons]
      change HasFDerivAt (orbitInCoordinates R (iteratedLieDerivative 𝓘(ℝ, A) R s _))
        (orbitJet R b (fun i => lieDerivative 𝓘(ℝ, A) R (b i)
          (iteratedLieDerivative 𝓘(ℝ, A) R s _)) (u : A)) (u : A)
      rw [← smoothIteratedLieDerivative_apply]
      exact hasFDerivAt_orbitJet R b sv.property u
    · rintro _ ⟨u, rfl⟩
      simp only [orbitInCoordinates_val]
      exact ((R u).continuous.tendsto (w s)).comp (hcoords s)
    · exact ⟨g, rfl⟩
  have hsmooth (k : ℕ) (s : List A) :
      ContDiffOn ℝ k (orbitInCoordinates R (w s)) (unitDomain A) := by
    induction k generalizing s with
    | zero =>
        rw [Nat.cast_zero, contDiffOn_zero]
        intro x hx
        obtain ⟨g, rfl⟩ := hx
        exact (hderiv s g).continuousAt.continuousWithinAt
    | succ k ih =>
        rw [Nat.cast_succ, contDiffOn_succ_iff_fderiv_apply isOpen_unitDomain.uniqueDiffOn]
        refine ⟨?_, by simp, fun Y => ?_⟩
        · rintro _ ⟨g, rfl⟩
          exact (hderiv s g).differentiableAt.differentiableWithinAt
        · apply (contDiffOn_orbitJet_apply R b (fun i => ih (b i :: s)) Y).congr
          rintro _ ⟨g, rfl⟩
          exact congrFun (congrArg DFunLike.coe
            ((hderiv s g).hasFDerivWithinAt.fderivWithin
              (isOpen_unitDomain.uniqueDiffOn _ ⟨g, rfl⟩))) Y
  have hv (s : List A) : IsSmoothVector 𝓘(ℝ, A) R (w s) := by
    have h : ContDiffOn ℝ ∞ (orbitInCoordinates R (w s)) (unitDomain A) :=
      contDiffOn_infty.mpr fun k => hsmooth k s
    have heq : orbitMap R (w s) = orbitInCoordinates R (w s) ∘ Units.val := by
      funext g
      exact (orbitInCoordinates_val R (w s) g).symm
    unfold IsSmoothVector
    rw [heq]
    exact h.contMDiffOn.comp_contMDiff Units.contMDiff_val fun g => ⟨g, rfl⟩
  have hshift (X : A) (s : List A) :
      lieDerivative 𝓘(ℝ, A) R X (w s) = w (X :: s) := by
    have hAt := hderiv s (1 : Aˣ)
    have hAt' := hasFDerivAt_orbitInCoordinates_one R (hv s)
    have heq : orbitJet R b (fun i => w (b i :: s)) (1 : A) X =
        lieDerivative 𝓘(ℝ, A) R X (w s) := by
      exact congrArg (fun L : A →L[ℝ] E => L X) (hAt.unique hAt')
    rw [← heq]
    have hlim := (continuousAt_orbitJet R b hR (show (1 : A) ∈ unitDomain A from
      ⟨(1 : Aˣ), rfl⟩) (fun i => w (b i :: s))).tendsto.comp
        (tendsto_const_nhds.prodMk_nhds (tendsto_pi_nhds.mpr fun i =>
          hcoords (b i :: s)))
    have hcalc (v : D) : orbitJet R b (fun i => coords v (b i :: s)) 1 X = coords v (X :: s) := by
      simp only [coords, derivativeCoordinates_apply, iteratedLieDerivative_cons]
      simpa only [Units.val_one, inv_one, one_mul, map_one, one_apply_eq_self]
        using orbitJet_lieDerivative_apply R b
          (iteratedLieDerivative 𝓘(ℝ, A) R s (toSmooth 𝓘(ℝ, A) R v)) 1 X
    have h := (ContinuousLinearMap.apply ℝ E X).continuous.tendsto _ |>.comp hlim
    change Tendsto (fun v : D => orbitJet R b (fun i => coords v (b i :: s)) 1 X)
      l (𝓝 (orbitJet R b (fun i => w (b i :: s)) 1 X)) at h
    simp_rw [hcalc] at h
    exact tendsto_nhds_unique h (hcoords (X :: s))
  let v := (toSmooth 𝓘(ℝ, A) R).symm ⟨w [], hv []⟩
  refine ⟨v, funext fun s => ?_⟩
  change coords v s = w s
  induction s with
  | nil =>
      simp [coords, v]
  | cons X s ih =>
      rw [derivativeCoordinates_apply, iteratedLieDerivative_cons]
      rw [derivativeCoordinates_apply] at ih
      rw [ih, hshift]

/-- Smooth vectors of a jointly continuous representation on a complex Banach space
are complete for the genuine word-derivative uniformity. -/
theorem completeSpace_of_isContinuousRepresentation_units [CompleteSpace E]
    (hR : IsContinuousRepresentation R) :
    CompleteSpace (DerivativeSmoothVectors 𝓘(ℝ, A) R) :=
  (isUniformInducing_derivativeCoordinates 𝓘(ℝ, A) R).completeSpace
    (isClosed_range_derivativeCoordinates_units R hR).isComplete

end Langlands.Archimedean.DerivativeSmoothVectors
