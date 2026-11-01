import Langlands.Global.AdelicParabolicInduction
import Mathlib.Topology.ContinuousMap.LocallyConvex

/-! # Compact-open topology on actual half-twisted adelic sections -/

noncomputable section

universe uF uV uW uX

namespace Langlands.Global.AdelicParabolicInduction

open NumberField Langlands.GeneralLinear AdelicBlockParabolic
open Filter Topology
open scoped Topology

variable (F : Type uF) [Field F] [NumberField F] {n : ℕ} (B : BlockShape n)
variable {V : Type uV} {W : Type uW} {X : Type uX}
variable [NormedAddCommGroup V] [NormedSpace ℂ V]
variable [NormedAddCommGroup W] [NormedSpace ℂ W]
variable [NormedAddCommGroup X] [NormedSpace ℂ X]

/-- A dedicated copy of the actual smooth sections, with a compact-open topology. -/
def CompactOpenSections (σ : Representation ℂ (FullLevi F B) V) :=
  SmoothSections F B σ

namespace CompactOpenSections

variable (σ : Representation ℂ (FullLevi F B) V)

instance : AddCommGroup (CompactOpenSections F B σ) :=
  inferInstanceAs (AddCommGroup (SmoothSections F B σ))

instance : Module ℂ (CompactOpenSections F B σ) :=
  inferInstanceAs (Module ℂ (SmoothSections F B σ))

instance : Module ℝ (CompactOpenSections F B σ) :=
  inferInstanceAs (Module ℝ (SmoothSections F B σ))

instance : IsScalarTower ℝ ℂ (CompactOpenSections F B σ) :=
  inferInstanceAs (IsScalarTower ℝ ℂ (SmoothSections F B σ))

/-- Forget only the selected function-space topology. -/
def toSmooth : CompactOpenSections F B σ ≃ₗ[ℂ] SmoothSections F B σ :=
  LinearEquiv.refl ℂ (SmoothSections F B σ)

/-- The same actual section, realized as a continuous function. -/
def toContinuousMap : CompactOpenSections F B σ →ₗ[ℂ] C(AdelicGL F n, V) :=
  (smoothToContinuousMap F B σ).comp (toSmooth F B σ).toLinearMap

@[simp]
theorem toContinuousMap_apply (f : CompactOpenSections F B σ) (x : AdelicGL F n) :
    toContinuousMap F B σ f x = evaluate F B σ (toSmooth F B σ f).val x := rfl

theorem toContinuousMap_injective : Function.Injective (toContinuousMap F B σ) :=
  (smoothToContinuousMap_injective F B σ).comp (toSmooth F B σ).injective

instance : TopologicalSpace (CompactOpenSections F B σ) :=
  TopologicalSpace.induced (toContinuousMap F B σ) inferInstance

theorem isEmbedding_toContinuousMap : IsEmbedding (toContinuousMap F B σ) :=
  Function.Injective.isEmbedding_induced (toContinuousMap_injective F B σ)

instance : IsTopologicalAddGroup (CompactOpenSections F B σ) :=
  (isEmbedding_toContinuousMap F B σ).isInducing.isTopologicalAddGroup
    (toContinuousMap F B σ)

instance : ContinuousSMul ℂ (CompactOpenSections F B σ) :=
  continuousSMul_induced (toContinuousMap F B σ)

instance : ContinuousSMul ℝ (CompactOpenSections F B σ) :=
  continuousSMul_induced ((toContinuousMap F B σ).restrictScalars ℝ)

instance : T2Space (CompactOpenSections F B σ) :=
  (isEmbedding_toContinuousMap F B σ).t2Space

instance : LocallyConvexSpace ℝ (CompactOpenSections F B σ) :=
  LocallyConvexSpace.induced ((toContinuousMap F B σ).restrictScalars ℝ)

/-- Faithful continuous linear realization with its defining compact-open topology. -/
def toContinuousMapCLM : CompactOpenSections F B σ →L[ℂ] C(AdelicGL F n, V) :=
  ⟨toContinuousMap F B σ, (isEmbedding_toContinuousMap F B σ).continuous⟩

/-- Point evaluation is continuous and complex linear. -/
def evalCLM (x : AdelicGL F n) : CompactOpenSections F B σ →L[ℂ] V :=
  (ContinuousMap.evalCLM ℂ x).comp (toContinuousMapCLM F B σ)

@[simp]
theorem evalCLM_apply (x : AdelicGL F n) (f : CompactOpenSections F B σ) :
    evalCLM F B σ x f = evaluate F B σ (toSmooth F B σ f).val x := rfl

/-- The existing full adelic action, on the dedicated copy of the same sections. -/
def rightAction : Representation ℂ (AdelicGL F n) (CompactOpenSections F B σ) :=
  smoothInduced F B σ

@[simp]
theorem toContinuousMap_rightAction (g : AdelicGL F n)
    (f : CompactOpenSections F B σ) (x : AdelicGL F n) :
    toContinuousMap F B σ (rightAction F B σ g f) x =
      toContinuousMap F B σ f (x * g) := rfl

/-- Every fixed right translation is continuous in the chosen topology. -/
theorem continuous_rightAction (g : AdelicGL F n) :
    Continuous (rightAction F B σ g) := by
  apply continuous_induced_rng.mpr
  let r : C(AdelicGL F n, AdelicGL F n) :=
    ⟨fun x => x * g, continuous_id.mul continuous_const⟩
  exact (ContinuousMap.continuous_precomp r).comp
    (isEmbedding_toContinuousMap F B σ).continuous

/-- Fixed right translation as a continuous complex linear operator. -/
def rightTranslation (g : AdelicGL F n) :
    CompactOpenSections F B σ →L[ℂ] CompactOpenSections F B σ :=
  ⟨rightAction F B σ g, continuous_rightAction F B σ g⟩

/-- Inverse right translation gives the actual inverse homeomorphism. -/
def rightTranslationHomeomorph (g : AdelicGL F n) :
    CompactOpenSections F B σ ≃ₜ CompactOpenSections F B σ where
  toFun := rightAction F B σ g
  invFun := rightAction F B σ g⁻¹
  left_inv f := (rightAction F B σ).inv_self_apply g f
  right_inv f := (rightAction F B σ).self_inv_apply g f
  continuous_toFun := continuous_rightAction F B σ g
  continuous_invFun := continuous_rightAction F B σ g⁻¹

/-- Convergence is exactly uniform convergence on every compact subset of the actual group. -/
theorem tendsto_iff_uniformOn_compact {ι : Type*} {l : Filter ι}
    {f : ι → CompactOpenSections F B σ} {s : CompactOpenSections F B σ} :
    Tendsto f l (𝓝 s) ↔ ∀ K : Set (AdelicGL F n), IsCompact K →
      TendstoUniformlyOn (fun i => toContinuousMap F B σ (f i))
        (toContinuousMap F B σ s) l K := by
  rw [(isEmbedding_toContinuousMap F B σ).tendsto_nhds_iff,
    ContinuousMap.tendsto_iff_forall_isCompact_tendstoUniformlyOn]
  rfl

variable {σ}

/-- Coefficient postcomposition on the same actual sections. -/
def map {τ : Representation ℂ (FullLevi F B) W} (T : σ.IntertwiningMap τ)
    (hT : Continuous T) : CompactOpenSections F B σ →ₗ[ℂ] CompactOpenSections F B τ :=
  (smoothInducedMap F B T hT).toLinearMap

@[simp]
theorem toContinuousMap_map {τ : Representation ℂ (FullLevi F B) W}
    (T : σ.IntertwiningMap τ) (hT : Continuous T)
    (f : CompactOpenSections F B σ) (x : AdelicGL F n) :
    toContinuousMap F B τ (map F B T hT f) x =
      T (toContinuousMap F B σ f x) := rfl

theorem continuous_map {τ : Representation ℂ (FullLevi F B) W}
    (T : σ.IntertwiningMap τ) (hT : Continuous T) :
    Continuous (map F B T hT) := by
  apply continuous_induced_rng.mpr
  exact (ContinuousMap.continuous_postcomp ⟨T, hT⟩).comp
    (isEmbedding_toContinuousMap F B σ).continuous

/-- A continuous coefficient intertwiner induces a continuous linear section map. -/
def mapCLM {τ : Representation ℂ (FullLevi F B) W}
    (T : σ.IntertwiningMap τ) (hT : Continuous T) :
    CompactOpenSections F B σ →L[ℂ] CompactOpenSections F B τ :=
  ⟨map F B T hT, continuous_map F B T hT⟩

@[simp]
theorem mapCLM_id (σ : Representation ℂ (FullLevi F B) V) :
    mapCLM F B (Representation.IntertwiningMap.id σ) continuous_id =
      ContinuousLinearMap.id ℂ (CompactOpenSections F B σ) := by
  apply ContinuousLinearMap.ext
  intro f
  exact congrArg (fun T => T f) (smoothInducedMap_id F B σ)

@[simp]
theorem mapCLM_comp {τ : Representation ℂ (FullLevi F B) W}
    {υ : Representation ℂ (FullLevi F B) X}
    (T : σ.IntertwiningMap τ) (S : τ.IntertwiningMap υ)
    (hT : Continuous T) (hS : Continuous S) :
    mapCLM F B (S.comp T) (hS.comp hT) =
      (mapCLM F B S hS).comp (mapCLM F B T hT) := by
  apply ContinuousLinearMap.ext
  intro f
  exact congrArg (fun A => A f) (smoothInducedMap_comp F B T S hT hS)

theorem mapCLM_rightAction {τ : Representation ℂ (FullLevi F B) W}
    (T : σ.IntertwiningMap τ) (hT : Continuous T) (g : AdelicGL F n)
    (f : CompactOpenSections F B σ) :
    mapCLM F B T hT (rightAction F B σ g f) =
      rightAction F B τ g (mapCLM F B T hT f) :=
  Representation.IntertwiningMap.isIntertwining
    (smoothInduced F B σ) (smoothInduced F B τ) (smoothInducedMap F B T hT) g f

end CompactOpenSections

end Langlands.Global.AdelicParabolicInduction
