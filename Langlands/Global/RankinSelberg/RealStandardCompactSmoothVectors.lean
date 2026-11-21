import Langlands.Analysis.ClosedSubmoduleSmoothness
import Langlands.Analysis.CompactParameterSmoothness
import Langlands.Global.RankinSelberg.RealStandardCompactBanachAction
import Mathlib.Geometry.Manifold.MFDeriv.SpecificFunctions

/-! # Smooth vectors of the compact Banach real standard module -/

noncomputable section

open Langlands.Archimedean Langlands.GeneralLinear Langlands.LocalFactor.Archimedean
open Set
open scoped ContDiff Manifold Matrix.Norms.Operator

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal.RealStandardCompactBanach

variable {n : ℕ}

local notation "G" => Langlands.GeneralLinear n ℝ
local notation "M" => Matrix (Fin n) (Fin n) ℝ
local notation "U" => Matrix.unitaryGroup (Fin n) ℝ
local notation "I" => matrixModel ℝ n
local notation "S" ds => realStandardModule n ds
local notation "E" ds => Carrier n ds
local notation "R" ds => representation (n := n) ds
local notation "V" ds => Archimedean.smoothVectors I (R ds)

open Classical in
private def orbitInMatrices (ds : List RealBlock) (f : S ds) (A : M) : E ds :=
  if hA : IsUnit A then (R ds) hA.unit (embed ds f) else 0

private theorem orbitInMatrices_val (ds : List RealBlock) (f : S ds) (g : G) :
    orbitInMatrices ds f g.val = (R ds) g (embed ds f) := by
  simp [orbitInMatrices, g.isUnit]

/-- Every original smooth standard vector has a smooth orbit in the compact Banach norm. -/
theorem isSmoothVector_embed (ds : List RealBlock) (f : S ds) :
    Archimedean.IsSmoothVector I (R ds) (embed ds f) := by
  let Ω : Set M := {A | IsUnit A}
  have hΩ : IsOpen Ω := isOpen_setOf_isUnit_matrix
  let j : C(U, M) :=
    ⟨fun k => (Unitary.toUnits k).val, Units.continuous_val.comp continuous_unitary_toUnits⟩
  have hj (k : U) : j k ∈ Ω := (Unitary.toUnits k).isUnit
  let H : M × M → ℂ := fun p => unitsExtension f.val (p.2 * p.1)
  have hH : ContDiffOn ℝ ∞ H (Ω ×ˢ Ω) :=
    (contDiffOn_unitsExtension f.property.1.1).comp
      (contDiff_snd.mul contDiff_fst).contDiffOn (fun p hp => hp.2.mul hp.1)
  have hval (A : M) (hA : A ∈ Ω) (k : U) :
      (orbitInMatrices ds f A).val k = H (A, j k) := by
    obtain ⟨g, rfl⟩ := hA
    rw [orbitInMatrices_val, representation_apply, embed_val, extensionOfProfile_restriction]
    change f.val (Unitary.toUnits k * g) =
      unitsExtension f.val ((Unitary.toUnits k).val * g.val)
    rw [← Units.val_mul, unitsExtension_val]
  have hAmbient : ContDiffOn ℝ ∞ (fun A => (orbitInMatrices ds f A).val) Ω :=
    Langlands.Analysis.contDiffOn_infty_compactFamily_of_joint j hΩ hΩ hj hH hval
  have hOrbit : ContDiffOn ℝ ∞ (orbitInMatrices ds f) Ω :=
    Langlands.Analysis.contDiffOn_infty_of_closedSubmodule
      (p := (closureSubmodule (n := n) ds).restrictScalars ℝ)
      (LinearMap.range (compactRestriction (n := n) ds)).isClosed_topologicalClosure hΩ hAmbient
  have h := hOrbit.contMDiffOn.comp_contMDiff (Units.contMDiff_val (𝕜 := ℝ) (n := ∞))
    (fun g : G => g.isUnit)
  exact h.congr (fun g => (orbitInMatrices_val ds f g).symm)

/-- Evaluation of a compact Banach profile is a bounded linear functional. -/
def profileEval (ds : List RealBlock) (k : U) : (E ds) →L[ℂ] ℂ :=
  (ContinuousMap.evalCLM ℂ k).comp (closureSubmodule ds).subtypeL

@[simp]
theorem profileEval_apply (ds : List RealBlock) (k : U) (v : E ds) :
    profileEval ds k v = v.val k := rfl

@[simp]
theorem profileEval_one_orbit (ds : List RealBlock) (v : E ds) (g : G) :
    profileEval ds 1 ((R ds) g v) = extensionOfProfile ds v.val g := by
  rw [profileEval_apply, representation_apply, map_one, one_mul]

/-- The standard-module right derivative along a real matrix. -/
def differentiate (ds : List RealBlock) (X : M) (f : S ds) : S ds :=
  ⟨rightDerivative I X f.val, rightDerivative_mem_realStandardModule_of_mem f.property X⟩

@[simp]
theorem differentiate_val (ds : List RealBlock) (X : M) (f : S ds) :
    (differentiate ds X f).val = rightDerivative I X f.val := rfl

/-- The Banach Lie derivative identifies with the scalar right derivative. -/
theorem lieDerivative_embed (ds : List RealBlock) (X : M) (f : S ds) :
    lieDerivative I (R ds) X (embed ds f) = embed ds (differentiate ds X f) := by
  apply Subtype.ext
  apply ContinuousMap.ext
  intro k
  let L : (E ds) →L[ℝ] ℂ := (profileEval ds k).restrictScalars ℝ
  let O : G → E ds := orbitMap (R ds) (embed ds f)
  have hL : MDifferentiableAt 𝓘(ℝ, E ds) 𝓘(ℝ, ℂ) L (O 1) := L.mdifferentiableAt
  have hO : MDifferentiableAt I 𝓘(ℝ, E ds) O (1 : G) :=
    (isSmoothVector_embed ds f).mdifferentiableAt (by simp)
  have hchain := mfderiv_comp (1 : G) hL hO
  rw [ContinuousLinearMap.mfderiv_eq] at hchain
  have hfun : L ∘ O = fun g => f.val (Unitary.toUnits k * g) := by
    funext g
    change ((R ds) g (embed ds f)).val k = _
    rw [representation_apply, embed_val, extensionOfProfile_restriction]
  change (L.comp (mfderiv I 𝓘(ℝ, E ds) O 1)) X =
    mfderiv I 𝓘(ℝ, ℂ) (fun g => f.val (Unitary.toUnits k * g)) 1 X
  rw [← hchain, hfun]
  rfl

private theorem continuous_extendedEval (ds : List RealBlock) (g : G) :
    Continuous (fun v : E ds => extensionOfProfile ds v.val g) := by
  simp only [← profileEval_one_orbit]
  exact (profileEval ds 1).continuous.comp ((R ds) g).continuous

private theorem continuous_extendedBlockFourier (ds : List RealBlock) (p : ℕ) (k : ℤ) (g : G) :
    Continuous (fun v : E ds => blockFourierCoefficient n p k (extensionOfProfile ds v.val) g) := by
  unfold blockFourierCoefficient
  refine intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
    (f := fun (v : E ds) (θ : ℝ) =>
      extensionOfProfile ds v.val (blockRotation n p θ * g) *
        Complex.exp (-((k : ℂ) * (θ : ℂ) * Complex.I))) ?_ _ _
  have h : Continuous (fun x : (E ds) × ℝ => (x.1.val, blockRotation n p x.2 * g)) :=
    (continuous_subtype_val.comp continuous_fst).prodMk
      (((continuous_blockRotation n p).comp continuous_snd).mul continuous_const)
  exact ((continuous_extensionOfProfile ds).comp h).mul (Complex.continuous_exp.comp (by fun_prop))

/-- Extension of the profile of a smooth vector is a smooth standard function. -/
theorem extensionOfProfile_mem_of_smooth (ds : List RealBlock) (v : V ds) :
    extensionOfProfile ds v.val.val ∈ S ds := by
  have hs : ContMDiff I 𝓘(ℝ, ℂ) ∞ (fun g : G => profileEval ds 1 ((R ds) g v.val)) :=
    ((profileEval ds 1).restrictScalars ℝ).contDiff.contMDiff.comp v.property
  rw [mem_realStandardModule_iff, mem_principalSeries_iff]
  refine ⟨⟨by simpa only [profileEval_one_orbit] using hs, ?_⟩, ?_⟩
  · intro a u g
    let g' := (Iwasawa.diagonalUnits a : G) * u.val * g
    let c := principalSeriesCharacter ℝ n (realPositionCharacter ds) a
    have he : (fun w : E ds => extensionOfProfile ds w.val g') =
        fun w => c * extensionOfProfile ds w.val g :=
      (denseRange_embed ds).equalizer (continuous_extendedEval ds g')
        (continuous_const.mul (continuous_extendedEval ds g)) (funext fun f => by
          simp only [Function.comp_apply, embed_val, extensionOfProfile_restriction]
          exact f.property.1.2 a u g)
    exact congrFun he v.val
  · intro p d hd k hk g
    have he : (fun w : E ds => blockFourierCoefficient n p k (extensionOfProfile ds w.val) g) =
        fun _ => 0 :=
      (denseRange_embed ds).equalizer (continuous_extendedBlockFourier ds p k g)
        continuous_const (funext fun f => by
          simp only [Function.comp_apply, embed_val, extensionOfProfile_restriction]
          exact f.property.2 p d hd k hk g)
    exact congrFun he v.val

/-- The original standard module identifies with all genuine smooth vectors of the
compact Banach completion. -/
def smoothEquiv (ds : List RealBlock) : (S ds) ≃ₗ[ℂ] V ds :=
  LinearEquiv.ofBijective
    ((embed ds).codRestrict (V ds) (isSmoothVector_embed ds))
    (by
      refine ⟨fun f f' h => embed_injective ds (congrArg Subtype.val h), ?_⟩
      intro v
      refine ⟨⟨extensionOfProfile ds v.val.val, extensionOfProfile_mem_of_smooth ds v⟩, ?_⟩
      apply Subtype.ext
      apply Subtype.ext
      apply ContinuousMap.ext
      intro k
      exact extensionOfProfile_compact ds v.val.val k)

@[simp]
theorem smoothEquiv_val (ds : List RealBlock) (f : S ds) :
    (smoothEquiv ds f).val = embed ds f := rfl

/-- The equivalence preserves actual group translation and the real Lie action. -/
def RealStandardCompactSmoothVectorsStatement : Prop :=
  ∀ (m : ℕ) (ds : List RealBlock),
    ∃ e : realStandardModule m ds ≃ₗ[ℂ]
        Archimedean.smoothVectors (matrixModel ℝ m) (representation (n := m) ds),
      (∀ f, (e f).val = embed ds f) ∧
      (∀ g f, (e (translate ds g f)).val = representation ds g (e f).val) ∧
      ∀ X f, (e (differentiate ds X f)).val =
        lieDerivative (matrixModel ℝ m) (representation ds) X (e f).val

theorem realStandardCompactSmoothVectors : RealStandardCompactSmoothVectorsStatement := by
  intro n ds
  exact ⟨smoothEquiv ds, smoothEquiv_val ds,
    fun g f => (representation_embed ds g f).symm, fun X f => (lieDerivative_embed ds X f).symm⟩

end Langlands.Global.RankinSelbergGlobal.RealStandardCompactBanach
