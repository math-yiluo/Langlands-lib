import Langlands.Automorphic.GroupSchemeManifoldSmooth

/-! # Reconstructing actual finite-level adelic functions from smooth slices -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry NumberField
open scoped Classical CategoryTheory.MonObj Manifold ContDiff

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Automorphic.GroupSchemeFunctions

open Langlands.Global

variable (F : Type u) [Field F] [NumberField F]
  (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffine G.X.left] {d : ℕ}

/-- The unchanged smooth-function carrier on the actual infinite adelic group. -/
abbrev InfinitePlotSmoothFunctions :=
  G.plotSmoothFunctions (CommAlgCat.of F (InfiniteAdeleRing F))
    (B := mixedEmbedding.mixedSpace F)
    (InfiniteAdeleRing.ringEquiv_mixedSpace F).toRingHom

/-- Evaluate the slice at the actual infinite and finite projections. -/
def evaluatePlotSmoothSlices
    (s : FiniteAdelicGroupPoints F G → InfinitePlotSmoothFunctions F G)
    (x : AdelicGroupPoints F G) : ℂ :=
  (s (AdelicGroupPoints.finite F G x)).val (AdelicGroupPoints.infinite F G x)

@[simp]
theorem evaluatePlotSmoothSlices_pair
    (s : FiniteAdelicGroupPoints F G → InfinitePlotSmoothFunctions F G)
    (a : InfiniteAdelicGroupPoints F G) (b : FiniteAdelicGroupPoints F G) :
    evaluatePlotSmoothSlices F G s (AdelicGroupPoints.pair F G a b) = (s b).val a := by
  simp [evaluatePlotSmoothSlices]

/-- A common open finite stabilizer makes the smooth slice family jointly continuous. -/
theorem continuous_evaluatePlotSmoothSlices
    (hsmooth : SmoothOfRelativeDimension d G.X.hom)
    (s : FiniteAdelicGroupPoints F G → InfinitePlotSmoothFunctions F G)
    (L : OpenSubgroup (FiniteAdelicGroupPoints F G))
    (hL : ∀ (b : FiniteAdelicGroupPoints F G) (l : L), s (b * l.val) = s b) :
    Continuous (evaluatePlotSmoothSlices F G s) := by
  let := fun v : NumberField.InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
  let := InfiniteAdelicGroupPoints.smoothChartedSpace F G hsmooth
  rw [continuous_iff_continuousAt]
  intro x
  let b := AdelicGroupPoints.finite F G x
  have ho : IsOpen {y : AdelicGroupPoints F G |
      b⁻¹ * AdelicGroupPoints.finite F G y ∈ L} :=
    L.isOpen.preimage (continuous_const.mul (AdelicGroupPoints.finite F G).continuous)
  have hx : x ∈ {y : AdelicGroupPoints F G |
      b⁻¹ * AdelicGroupPoints.finite F G y ∈ L} := by
    change b⁻¹ * b ∈ L
    simp
  have hb : Continuous (s b).val :=
    ((InfiniteAdelicGroupPoints.isPlotSmooth_iff_contMDiff F G hsmooth _).mp
      (s b).property).continuous
  have hc := (hb.comp (AdelicGroupPoints.infinite F G).continuous).continuousAt (x := x)
  apply hc.congr
  filter_upwards [ho.mem_nhds hx] with y hy
  have h := hL b ⟨b⁻¹ * AdelicGroupPoints.finite F G y, hy⟩
  simp only [mul_inv_cancel_left] at h
  change (s b).val _ = (s (AdelicGroupPoints.finite F G y)).val _
  rw [h]
  rfl

/-- Actual smooth slices with rational covariance and a specified open finite level. -/
def finiteLevelPlotSmoothSliceFamilies (L : OpenSubgroup (FiniteAdelicGroupPoints F G)) :
    Submodule ℂ (FiniteAdelicGroupPoints F G → InfinitePlotSmoothFunctions F G) where
  carrier := {s |
    (∀ (b : FiniteAdelicGroupPoints F G) (l : L), s (b * l.val) = s b) ∧
    ∀ (γ : RationalGroupPoints F G) (b : FiniteAdelicGroupPoints F G)
      (a : InfiniteAdelicGroupPoints F G),
      (s (AdelicGroupPoints.finite F G (AdelicGroupPoints.rational F G γ) * b)).val
        (AdelicGroupPoints.infinite F G (AdelicGroupPoints.rational F G γ) * a) = (s b).val a}
  zero_mem' := by constructor <;> intros <;> rfl
  add_mem' {s t} hs ht := by
    constructor
    · intro b l
      change s (b * l.val) + t (b * l.val) = s b + t b
      rw [hs.1 b l, ht.1 b l]
    · intro γ b a
      change
        (s (AdelicGroupPoints.finite F G (AdelicGroupPoints.rational F G γ) * b)).val
          (AdelicGroupPoints.infinite F G (AdelicGroupPoints.rational F G γ) * a) +
        (t (AdelicGroupPoints.finite F G (AdelicGroupPoints.rational F G γ) * b)).val
          (AdelicGroupPoints.infinite F G (AdelicGroupPoints.rational F G γ) * a) =
        (s b).val a + (t b).val a
      rw [hs.2 γ b a, ht.2 γ b a]
  smul_mem' c s hs := by
    constructor
    · intro b l
      change c • s (b * l.val) = c • s b
      rw [hs.1 b l]
    · intro γ b a
      change c •
        (s (AdelicGroupPoints.finite F G (AdelicGroupPoints.rational F G γ) * b)).val
          (AdelicGroupPoints.infinite F G (AdelicGroupPoints.rational F G γ) * a) =
        c • (s b).val a
      rw [hs.2 γ b a]

abbrev FiniteLevelPlotSmoothSliceFamilies (L : OpenSubgroup (FiniteAdelicGroupPoints F G)) :=
  finiteLevelPlotSmoothSliceFamilies F G L

/-- Reconstruct the actual continuous rational-invariant function. -/
def reconstructContinuousPlotSlices
    (hsmooth : SmoothOfRelativeDimension d G.X.hom)
    (L : OpenSubgroup (FiniteAdelicGroupPoints F G)) :
    FiniteLevelPlotSmoothSliceFamilies F G L →ₗ[ℂ] ContinuousRationalFunctions F G where
  toFun s := ⟨⟨evaluatePlotSmoothSlices F G s.val, by
    intro γ x
    change evaluatePlotSmoothSlices F G s.val (AdelicGroupPoints.rational F G γ * x) =
      evaluatePlotSmoothSlices F G s.val x
    simpa only [evaluatePlotSmoothSlices, map_mul] using
      s.property.2 γ (AdelicGroupPoints.finite F G x) (AdelicGroupPoints.infinite F G x)⟩,
    continuous_evaluatePlotSmoothSlices F G hsmooth s.val L s.property.1⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Reconstruction retains the original smooth predicates and the same open stabilizer. -/
def reconstructFinitePlotSmoothSlices
    (hsmooth : SmoothOfRelativeDimension d G.X.hom)
    (L : OpenSubgroup (FiniteAdelicGroupPoints F G)) :
    FiniteLevelPlotSmoothSliceFamilies F G L →ₗ[ℂ] FinitePlotSmoothRationalFunctions F G where
  toFun s := ⟨reconstructContinuousPlotSlices F G hsmooth L s, by
    constructor
    · apply (mem_infinitePlotSmoothSubrepresentation F G _).mpr
      intro b
      have heq : infiniteSlice F G b (reconstructContinuousPlotSlices F G hsmooth L s) =
          (s.val b).val := by
        funext a
        exact evaluatePlotSmoothSlices_pair F G s.val a b
      rw [heq]
      exact (s.val b).property
    · refine ⟨L, ?_⟩
      intro l
      apply Subtype.ext
      apply Subtype.ext
      funext x
      change evaluatePlotSmoothSlices F G s.val (x * AdelicGroupPoints.ofFinite F G l.val) =
        evaluatePlotSmoothSlices F G s.val x
      simp only [evaluatePlotSmoothSlices, map_mul,
        AdelicGroupPoints.finite_ofFinite, AdelicGroupPoints.infinite_ofFinite, mul_one]
      rw [s.property.1 _ l]⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp]
theorem evaluate_reconstructFinitePlotSmoothSlices
    (hsmooth : SmoothOfRelativeDimension d G.X.hom)
    (L : OpenSubgroup (FiniteAdelicGroupPoints F G))
    (s : FiniteLevelPlotSmoothSliceFamilies F G L)
    (a : InfiniteAdelicGroupPoints F G) (b : FiniteAdelicGroupPoints F G) :
    evaluate F G (reconstructFinitePlotSmoothSlices F G hsmooth L s).val
      (AdelicGroupPoints.pair F G a b) = (s.val b).val a :=
  evaluatePlotSmoothSlices_pair F G s.val a b

/-- The original smooth infinite slice of a finite-smooth adelic function. -/
def finitePlotSmoothSlice (b : FiniteAdelicGroupPoints F G) :
    FinitePlotSmoothRationalFunctions F G →ₗ[ℂ] InfinitePlotSmoothFunctions F G where
  toFun f := ⟨infiniteSlice F G b f.val,
    (mem_infinitePlotSmoothSubrepresentation F G f.val).mp f.property.1 b⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp]
theorem finitePlotSmoothSlice_apply (b : FiniteAdelicGroupPoints F G)
    (f : FinitePlotSmoothRationalFunctions F G) (a : InfiniteAdelicGroupPoints F G) :
    (finitePlotSmoothSlice F G b f).val a =
      evaluate F G f.val (AdelicGroupPoints.pair F G a b) := rfl

@[simp]
theorem finitePlotSmoothSlice_reconstruct
    (hsmooth : SmoothOfRelativeDimension d G.X.hom)
    (L : OpenSubgroup (FiniteAdelicGroupPoints F G))
    (s : FiniteLevelPlotSmoothSliceFamilies F G L) (b : FiniteAdelicGroupPoints F G) :
    finitePlotSmoothSlice F G b (reconstructFinitePlotSmoothSlices F G hsmooth L s) =
      s.val b := by
  apply Subtype.ext
  funext a
  exact evaluate_reconstructFinitePlotSmoothSlices F G hsmooth L s a b

/-- Actual slices determine the original adelic function. -/
theorem finitePlotSmoothSlice_injective :
    Function.Injective (fun f : FinitePlotSmoothRationalFunctions F G =>
      fun b => finitePlotSmoothSlice F G b f) := by
  intro f g h
  apply Subtype.ext
  apply Subtype.ext
  apply Subtype.ext
  funext x
  have he := congrArg (fun s =>
    (s (AdelicGroupPoints.finite F G x) : InfinitePlotSmoothFunctions F G).val
      (AdelicGroupPoints.infinite F G x)) h
  change evaluate F G f.val x = evaluate F G g.val x
  simpa only [finitePlotSmoothSlice_apply, AdelicGroupPoints.pair_projections] using he

/-- Extract the covariant family at any specified open finite level fixing the function. -/
def plotSlicesAtLevel (L : OpenSubgroup (FiniteAdelicGroupPoints F G))
    (f : FinitePlotSmoothRationalFunctions F G)
    (hf : f.val ∈ levelSubmodule F G L.toSubgroup) :
    FiniteLevelPlotSmoothSliceFamilies F G L :=
  ⟨fun b => finitePlotSmoothSlice F G b f, by
    constructor
    · intro b l
      apply Subtype.ext
      funext a
      have h := congrArg (fun g : ContinuousRationalFunctions F G =>
        evaluate F G g (AdelicGroupPoints.pair F G a b)) (hf l)
      change evaluate F G f.val (AdelicGroupPoints.pair F G a b *
        AdelicGroupPoints.ofFinite F G l.val) =
        evaluate F G f.val (AdelicGroupPoints.pair F G a b) at h
      simpa only [finitePlotSmoothSlice_apply, AdelicGroupPoints.ofFinite_eq_pair,
        AdelicGroupPoints.pair_mul, mul_one] using h
    · intro γ b a
      have h := f.val.val.property γ (AdelicGroupPoints.pair F G a b)
      change evaluate F G f.val (AdelicGroupPoints.rational F G γ *
        AdelicGroupPoints.pair F G a b) = evaluate F G f.val (AdelicGroupPoints.pair F G a b) at h
      rw [← AdelicGroupPoints.pair_projections F G (AdelicGroupPoints.rational F G γ),
        AdelicGroupPoints.pair_mul] at h
      exact h⟩

@[simp]
theorem reconstruct_plotSlicesAtLevel
    (hsmooth : SmoothOfRelativeDimension d G.X.hom)
    (L : OpenSubgroup (FiniteAdelicGroupPoints F G))
    (f : FinitePlotSmoothRationalFunctions F G)
    (hf : f.val ∈ levelSubmodule F G L.toSubgroup) :
    reconstructFinitePlotSmoothSlices F G hsmooth L (plotSlicesAtLevel F G L f hf) = f := by
  apply finitePlotSmoothSlice_injective F G
  funext b
  dsimp only
  rw [finitePlotSmoothSlice_reconstruct]
  rfl

end Langlands.Automorphic.GroupSchemeFunctions
