import Langlands.Global.RankinSelberg.RealStandardCompactSmoothVectors
import Langlands.Representation.Archimedean.SmoothCasselmanWallachStatement

/-! # Compact-finite vectors of the Banach real standard module -/

noncomputable section

open Langlands.Archimedean Langlands.GeneralLinear Langlands.LocalFactor.Archimedean
open Set
open scoped ContDiff Manifold Matrix.Norms.Operator TensorProduct

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal.RealStandardCompactBanach

variable {n : ℕ}

local notation "G" => Langlands.GeneralLinear n ℝ
local notation "M" => Matrix (Fin n) (Fin n) ℝ
local notation "U" => Matrix.unitaryGroup (Fin n) ℝ
local notation "K" => unitaryCompact ℝ n
local notation "I" => matrixModel ℝ n
local notation "S" ds => realStandardModule n ds
local notation "R" ds => representation (n := n) ds
local notation "D" ds => DerivativeSmoothVectors I (R ds)
local notation "KFin" ds => smoothKFinite ℝ n (R ds)
local notation "V" ds => kFiniteFunctions (S ds) K

/-- The original standard module in the genuine derivative carrier. -/
def derivativeEquiv (ds : List RealBlock) : (S ds) ≃ₗ[ℂ] D ds :=
  (smoothEquiv ds).trans (DerivativeSmoothVectors.toSmooth I (R ds)).symm

@[simp]
theorem toSmooth_derivativeEquiv (ds : List RealBlock) (f : S ds) :
    (DerivativeSmoothVectors.toSmooth I (R ds) (derivativeEquiv ds f)).val = embed ds f := by
  simp [derivativeEquiv]

theorem derivativeEquiv_translate (ds : List RealBlock) (g : G) (f : S ds) :
    derivativeEquiv ds (translate ds g f) =
      DerivativeSmoothVectors.representation I (R ds) g (derivativeEquiv ds f) := by
  apply (DerivativeSmoothVectors.toSmooth I (R ds)).injective
  apply Subtype.ext
  simp only [DerivativeSmoothVectors.toSmooth_representation, smoothRepresentation_apply,
    toSmooth_derivativeEquiv, representation_embed]

theorem derivativeEquiv_differentiate (ds : List RealBlock) (X : M) (f : S ds) :
    derivativeEquiv ds (differentiate ds X f) =
      DerivativeSmoothVectors.operator I (R ds) X (derivativeEquiv ds f) := by
  apply (DerivativeSmoothVectors.toSmooth I (R ds)).injective
  apply Subtype.ext
  simp only [DerivativeSmoothVectors.toSmooth_operator, smoothLieDerivative_apply,
    toSmooth_derivativeEquiv, lieDerivative_embed]

private def reconstruction (ds : List RealBlock) :
    Representation.IntertwiningMap
      ((DerivativeSmoothVectors.representation I (R ds)).comp (Unitary.toUnits : U →* G))
      ((Whittaker.rightTranslation ℂ G).comp (Unitary.toUnits : U →* G)) where
  toLinearMap := (S ds).subtype.comp (derivativeEquiv ds).symm.toLinearMap
  isIntertwining' k := by
    apply LinearMap.ext
    intro v
    obtain ⟨f, rfl⟩ := (derivativeEquiv ds).surjective v
    change ((derivativeEquiv ds).symm
        (DerivativeSmoothVectors.representation I (R ds) (Unitary.toUnits k)
          (derivativeEquiv ds f))).val =
      Whittaker.rightTranslation ℂ G (Unitary.toUnits k)
        ((derivativeEquiv ds).symm (derivativeEquiv ds f)).val
    rw [← derivativeEquiv_translate, LinearEquiv.symm_apply_apply, LinearEquiv.symm_apply_apply]
    rfl

private theorem reconstruction_injective (ds : List RealBlock) :
    Function.Injective (reconstruction (n := n) ds) :=
  Subtype.val_injective.comp (derivativeEquiv ds).symm.injective

private theorem range_rightTranslation_unitary (f : G → ℂ) :
    range (fun k : U => Whittaker.rightTranslation ℂ G (Unitary.toUnits k) f) =
      range (fun k : K => Whittaker.rightTranslation ℂ G k.val f) := by
  ext F
  constructor
  · rintro ⟨k, rfl⟩
    exact ⟨⟨Unitary.toUnits k, k.property⟩, rfl⟩
  · rintro ⟨k, rfl⟩
    let u : U := ⟨k.val.val, k.property⟩
    have hu : Unitary.toUnits u = k.val := Units.ext rfl
    exact ⟨u, congrArg (fun g => Whittaker.rightTranslation ℂ G g f) hu⟩

/-- Compact finiteness of a transported vector is exactly compact finiteness
of the original scalar standard function. -/
theorem derivativeEquiv_mem_compactFinite_iff (ds : List RealBlock) (f : S ds) :
    derivativeEquiv ds f ∈ (KFin ds) ↔ f.val ∈ kFiniteVectors (Whittaker.rightTranslation ℂ G) K := by
  have he : reconstruction ds (derivativeEquiv ds f) = f.val :=
    congrArg Subtype.val ((derivativeEquiv ds).symm_apply_apply f)
  have h := FiniteVectors.isFiniteVector_map_iff (reconstruction ds)
    (reconstruction_injective ds) (derivativeEquiv ds f)
  rw [he] at h
  rw [mem_kFiniteVectors_iff]
  change FiniteVectors.IsFiniteVector
      ((DerivativeSmoothVectors.representation I (R ds)).comp (Unitary.toUnits : U →* G))
        (derivativeEquiv ds f) ↔
      FiniteDimensional ℂ (Submodule.span ℂ
        (range fun k : K => Whittaker.rightTranslation ℂ G k.val f.val))
  rw [← range_rightTranslation_unitary]
  exact h.symm

/-- The original compact-finite standard module gives all compact-finite
genuine smooth vectors of its Banach completion. -/
def compactFiniteEquiv (ds : List RealBlock) : (V ds) ≃ₗ[ℂ] KFin ds := by
  let b : (V ds) →ₗ[ℂ] S ds := Submodule.inclusion inf_le_left
  let e : (V ds) →ₗ[ℂ] KFin ds :=
    ((derivativeEquiv ds).toLinearMap.comp b).codRestrict (KFin ds)
      (fun f => (derivativeEquiv_mem_compactFinite_iff ds (b f)).2 f.property.2)
  refine LinearEquiv.ofBijective e ⟨?_, ?_⟩
  · intro f f' h
    have hD : derivativeEquiv ds (b f) = derivativeEquiv ds (b f') :=
      congrArg (fun v : KFin ds => v.val) h
    exact Subtype.ext (congrArg (fun u : S ds => u.val) ((derivativeEquiv ds).injective hD))
  · intro v
    obtain ⟨f, hf⟩ := (derivativeEquiv ds).surjective v.val
    have hK : f.val ∈ kFiniteVectors (Whittaker.rightTranslation ℂ G) K :=
      (derivativeEquiv_mem_compactFinite_iff ds f).1 (hf ▸ v.property)
    exact ⟨⟨f.val, f.property, hK⟩, Subtype.ext hf⟩

@[simp]
theorem compactFiniteEquiv_val (ds : List RealBlock) (f : V ds) :
    (compactFiniteEquiv ds f).val = derivativeEquiv ds ⟨f.val, f.property.1⟩ := rfl

/-- The inclusion after the compact-finite equivalence preserves the actual
compact action and each real matrix Lie operator. -/
theorem isSmoothGKIntertwiner_compactFiniteEquiv (ds : List RealBlock) :
    IsSmoothGKIntertwiner ℝ n (R ds) (realStandardRep n ds) (realStandardLie n ds)
      ((KFin ds).subtype.comp (compactFiniteEquiv ds).toLinearMap) := by
  constructor
  · intro k f
    let f₀ : S ds := ⟨f.val, f.property.1⟩
    have h : (⟨(realStandardRep n ds k f).val, (realStandardRep n ds k f).property.1⟩ :
        S ds) = translate ds (Unitary.toUnits k) f₀ :=
      Subtype.ext (realStandardRep_apply_coe n ds k f)
    change derivativeEquiv ds _ =
      DerivativeSmoothVectors.representation I (R ds) (Unitary.toUnits k) (derivativeEquiv ds f₀)
    exact (congrArg (derivativeEquiv ds) h).trans
      (derivativeEquiv_translate ds (Unitary.toUnits k) f₀)
  · intro X f
    let f₀ : S ds := ⟨f.val, f.property.1⟩
    let q := realStandardLie n ds (1 ⊗ₜ[ℝ] X) f
    have h : (⟨q.val, q.property.1⟩ : S ds) = differentiate ds X f₀ :=
      Subtype.ext (realStandardLie_one_tmul_apply_coe n ds X f)
    change derivativeEquiv ds _ =
      DerivativeSmoothVectors.operator I (R ds) X (derivativeEquiv ds f₀)
    exact (congrArg (derivativeEquiv ds) h).trans (derivativeEquiv_differentiate ds X f₀)

/-- The compact Banach representation realizes the full original compact-finite standard module
with its prescribed Lie and compact actions. -/
def RealStandardCompactFiniteStatement : Prop :=
  ∀ (m : ℕ) (ds : List RealBlock),
    let R₀ := representation (n := m) ds
    ∃ e : kFiniteFunctions (realStandardModule m ds) (unitaryCompact ℝ m) ≃ₗ[ℂ]
        smoothKFinite ℝ m R₀,
      IsSmoothGKIntertwiner ℝ m R₀ (realStandardRep m ds) (realStandardLie m ds)
        ((smoothKFinite ℝ m R₀).subtype.comp e.toLinearMap)

theorem realStandardCompactFinite : RealStandardCompactFiniteStatement :=
  fun _ ds => ⟨compactFiniteEquiv ds, isSmoothGKIntertwiner_compactFiniteEquiv ds⟩

end Langlands.Global.RankinSelbergGlobal.RealStandardCompactBanach
