import Langlands.Global.RankinSelberg.RealGodementCompactPicture
import Langlands.Representation.Archimedean.RealCartanCompactSupport
import Langlands.Representation.Archimedean.RealStandardModuleGKModule

/-! # The compact sup-norm completion of a real standard module -/

noncomputable section

open Langlands.Archimedean Langlands.GeneralLinear Langlands.LocalFactor.Archimedean
open PrincipalSeriesExtension GramFormula RealJacquetFrobenius
open Set
open scoped ContDiff Matrix.Norms.Operator Manifold

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal.RealStandardCompactBanach

variable {n : ℕ}

local notation "G" => Langlands.GeneralLinear n ℝ
local notation "U" => Matrix.unitaryGroup (Fin n) ℝ
local notation "Cₖ" => C(Matrix.unitaryGroup (Fin n) ℝ, ℂ)
local notation "S" ds => realStandardModule n ds

/-- The restriction of a smooth real standard vector to the compact group. -/
def compactRestriction (ds : List RealBlock) : (S ds) →ₗ[ℂ] Cₖ where
  toFun f := ⟨fun k => f.val (Unitary.toUnits k), f.property.1.1.continuous.comp continuous_unitary_toUnits⟩
  map_add' _ _ := ContinuousMap.ext fun _ => rfl
  map_smul' _ _ := ContinuousMap.ext fun _ => rfl

@[simp] theorem compactRestriction_apply (ds : List RealBlock) (f : S ds) (k : U) :
    compactRestriction ds f k = f.val (Unitary.toUnits k) := rfl

/-- The Banach carrier is the closure of the smooth compact restrictions. -/
def closureSubmodule (ds : List RealBlock) : Submodule ℂ Cₖ :=
  (LinearMap.range (compactRestriction (n := n) ds)).topologicalClosure

abbrev Carrier (n : ℕ) (ds : List RealBlock) := ↥(closureSubmodule (n := n) ds)

instance (ds : List RealBlock) : CompleteSpace (Carrier n ds) :=
  (LinearMap.range (compactRestriction (n := n) ds)).isClosed_topologicalClosure.isComplete.completeSpace_coe

/-- The smooth-source map into the compact Banach completion. -/
def embed (ds : List RealBlock) : (S ds) →ₗ[ℂ] Carrier n ds :=
  (Submodule.inclusion (LinearMap.range (compactRestriction (n := n) ds)).le_topologicalClosure).comp
    (compactRestriction ds).rangeRestrict

@[simp] theorem embed_val (ds : List RealBlock) (f : S ds) : (embed ds f).val = compactRestriction ds f := rfl

theorem denseRange_embed (ds : List RealBlock) : DenseRange (embed (n := n) ds) := by
  have hrange : Subtype.val '' range (embed (n := n) ds) = range (compactRestriction (n := n) ds) := by
    rw [← range_comp]
    rfl
  intro f
  rw [closure_subtype, hrange]
  exact f.property

/-- Right translation preserves the original smooth real standard module. -/
def translate (ds : List RealBlock) (g : G) : (S ds) →ₗ[ℂ] S ds :=
  ((Whittaker.rightTranslation ℂ G g).comp (S ds).subtype).codRestrict (S ds)
    (fun f => rightTranslation_mem_realStandardModule_of_mem f.property g)

@[simp] theorem translate_apply (ds : List RealBlock) (g : G) (f : S ds) (x : G) :
    (translate ds g f).val x = f.val (x * g) := rfl

private def positionExponents (n : ℕ) (ds : List RealBlock) : Fin n → ℂ :=
  shiftedExponent n (realPositionExponent ds)

/-- A continuous function on the compact group, extended to the whole group
with the position exponents. -/
def extensionOfProfile (ds : List RealBlock) (φ : Cₖ) : G → ℂ :=
  extension (positionExponents n ds) φ

@[simp] theorem extensionOfProfile_compact (ds : List RealBlock) (φ : Cₖ) (k : U) :
    extensionOfProfile ds φ (Unitary.toUnits k) = φ k := extension_unitary _ _ _

/-- Extending the compact restriction recovers the original smooth standard vector. -/
theorem extensionOfProfile_restriction (ds : List RealBlock) (f : S ds) :
    extensionOfProfile ds (compactRestriction ds f) = f.val := by
  have hF := RealGodement.compactPictureExtension_mem_principalSeries f.property.1
    (fun _ _ => rfl)
  exact eq_of_eqOn_unitaryCompact_of_mem_principalSeries hF f.property.1
    (RealGodement.compactPictureExtension_eqOn ds f.val)

theorem embed_injective (ds : List RealBlock) : Function.Injective (embed (n := n) ds) := by
  intro f g h
  apply Subtype.ext
  rw [← extensionOfProfile_restriction ds f, ← extensionOfProfile_restriction ds g]
  exact congrArg (extensionOfProfile ds) (congrArg Subtype.val h)

private def multiplier (ds : List RealBlock) (g : G) : ℂ :=
  gramExpression (positionExponents n ds) 1 (complexify g.val)

private theorem continuous_multiplier (ds : List RealBlock) : Continuous (multiplier (n := n) ds) := by
  have h := (contDiffOn_gramExpression (positionExponents n ds) 1).continuousOn
  exact h.comp_continuous Units.continuous_val fun g => g.isUnit

/-- Extension is jointly continuous in the profile and group argument. -/
theorem continuous_extensionOfProfile (ds : List RealBlock) :
    Continuous (fun p : Cₖ × G => extensionOfProfile ds p.1 p.2) := by
  change Continuous (fun p : Cₖ × G => multiplier ds p.2 * p.1 (signedOrthogonalPart p.2))
  exact ((continuous_multiplier ds).comp continuous_snd).mul
    (continuous_eval.comp (continuous_fst.prodMk
      (RealCartanCompactSupport.continuous_signedOrthogonalPart.comp continuous_snd)))

private def multiplierOnCompact (ds : List RealBlock) (g : G) : Cₖ :=
  ⟨fun k => multiplier ds (Unitary.toUnits k * g),
    (continuous_multiplier ds).comp (continuous_unitary_toUnits.mul continuous_const)⟩

private def ambientValue (ds : List RealBlock) (g : G) (φ : Cₖ) : Cₖ := by
  have hmul : Continuous (fun k : U => Unitary.toUnits k * g) :=
    continuous_unitary_toUnits.mul continuous_const
  have hφ : Continuous (fun x : G => φ (signedOrthogonalPart x)) :=
    φ.continuous.comp RealCartanCompactSupport.continuous_signedOrthogonalPart
  have h := ((continuous_multiplier ds).mul hφ).comp hmul
  exact ⟨fun k => extensionOfProfile ds φ (Unitary.toUnits k * g), h⟩

private def ambientLinear (ds : List RealBlock) (g : G) : Cₖ →ₗ[ℂ] Cₖ where
  toFun := ambientValue ds g
  map_add' φ ψ := ContinuousMap.ext fun k => by
    let q := signedOrthogonalPart (Unitary.toUnits k * g)
    let b := multiplier ds (Unitary.toUnits k * g)
    change b * (φ q + ψ q) = b * φ q + b * ψ q
    rw [mul_add]
  map_smul' c φ := ContinuousMap.ext fun k => by
    let q := signedOrthogonalPart (Unitary.toUnits k * g)
    let b := multiplier ds (Unitary.toUnits k * g)
    change b * (c * φ q) = c * (b * φ q)
    rw [mul_left_comm]

private theorem norm_ambientValue_le (ds : List RealBlock) (g : G) (φ : Cₖ) :
    ‖ambientValue ds g φ‖ ≤ ‖multiplierOnCompact ds g‖ * ‖φ‖ := by
  let b := multiplierOnCompact ds g
  apply (ContinuousMap.norm_le (ambientValue ds g φ) (mul_nonneg (norm_nonneg b) (norm_nonneg φ))).2
  intro k
  let q := signedOrthogonalPart (Unitary.toUnits k * g)
  change ‖b k * φ q‖ ≤ ‖b‖ * ‖φ‖
  rw [norm_mul]
  exact mul_le_mul (b.norm_coe_le_norm k) (φ.norm_coe_le_norm q) (norm_nonneg _) (norm_nonneg b)

private def ambientTranslation (ds : List RealBlock) (g : G) : Cₖ →L[ℂ] Cₖ :=
  (ambientLinear ds g).mkContinuous ‖multiplierOnCompact ds g‖ (norm_ambientValue_le ds g)

private theorem ambientTranslation_restriction (ds : List RealBlock) (g : G) (f : S ds) :
    ambientTranslation ds g (compactRestriction ds f) = compactRestriction ds (translate ds g f) := by
  ext k
  change extensionOfProfile ds (compactRestriction ds f) (Unitary.toUnits k * g) = _
  rw [extensionOfProfile_restriction]
  rfl

private theorem ambientTranslation_mem (ds : List RealBlock) (g : G) (v : Carrier n ds) :
    ambientTranslation ds g v.val ∈ closureSubmodule ds := by
  have h : MapsTo (ambientTranslation ds g) (range (compactRestriction ds)) (range (compactRestriction ds)) := by
    rintro _ ⟨f, rfl⟩
    exact ⟨translate ds g f, (ambientTranslation_restriction ds g f).symm⟩
  exact (h.closure (ambientTranslation ds g).continuous) v.property

private def translation (ds : List RealBlock) (g : G) : Carrier n ds →L[ℂ] Carrier n ds :=
  (ambientTranslation ds g).restrict (fun v hv => ambientTranslation_mem ds g ⟨v, hv⟩)

private theorem translation_embed (ds : List RealBlock) (g : G) (f : S ds) :
    translation ds g (embed ds f) = embed ds (translate ds g f) :=
  Subtype.ext (ambientTranslation_restriction ds g f)

private theorem ext_of_embed (ds : List RealBlock) {P Q : Carrier n ds →L[ℂ] Carrier n ds}
    (h : ∀ f : S ds, P (embed ds f) = Q (embed ds f)) : P = Q :=
  ContinuousLinearMap.ext (congrFun
    ((denseRange_embed ds).equalizer P.continuous Q.continuous (funext h)))

/-- The jointly continuous right action on the compact Banach standard module. -/
def representation (ds : List RealBlock) : G →* (Carrier n ds →L[ℂ] Carrier n ds) where
  toFun := translation ds
  map_one' := by
    apply ext_of_embed ds
    intro f
    rw [translation_embed]
    apply congrArg (embed ds)
    apply Subtype.ext
    funext x
    exact congrArg f.val (mul_one x)
  map_mul' g h := by
    apply ext_of_embed ds
    intro f
    simp only [mul_apply_eq_comp, translation_embed]
    apply congrArg (embed ds)
    apply Subtype.ext
    funext x
    exact congrArg f.val (mul_assoc x g h).symm

@[simp] theorem representation_embed (ds : List RealBlock) (g : G) (f : S ds) :
    representation ds g (embed ds f) = embed ds (translate ds g f) := translation_embed ds g f

@[simp] theorem representation_apply (ds : List RealBlock) (g : G) (v : Carrier n ds) (k : U) :
    (representation ds g v).val k = extensionOfProfile ds v.val (Unitary.toUnits k * g) := rfl

/-- Joint continuity of the actual extended action. -/
theorem isContinuousRepresentation (ds : List RealBlock) :
    IsContinuousRepresentation (representation (n := n) ds) := by
  change Continuous (fun p : G × Carrier n ds => representation ds p.1 p.2)
  apply Continuous.subtype_mk
  apply ContinuousMap.continuous_of_continuous_uncurry
  change Continuous (fun p : (G × Carrier n ds) × U => extensionOfProfile ds p.1.2.val
    (Unitary.toUnits p.2 * p.1.1))
  let T := (G × Carrier n ds) × U
  have hφ : Continuous (fun p : T => p.1.2.val) :=
    continuous_subtype_val.comp (continuous_snd.comp continuous_fst)
  have hg : Continuous (fun p : T => Unitary.toUnits p.2 * p.1.1) :=
    (continuous_unitary_toUnits.comp continuous_snd).mul (continuous_fst.comp continuous_fst)
  have hPart : Continuous (fun p : T => signedOrthogonalPart (Unitary.toUnits p.2 * p.1.1)) :=
    RealCartanCompactSupport.continuous_signedOrthogonalPart.comp hg
  have hEval : Continuous (fun p : T => p.1.2.val (signedOrthogonalPart (Unitary.toUnits p.2 * p.1.1))) :=
    continuous_eval.comp (hφ.prodMk hPart)
  change Continuous (fun p : T => multiplier ds (Unitary.toUnits p.2 * p.1.1) *
    p.1.2.val (signedOrthogonalPart (Unitary.toUnits p.2 * p.1.1)))
  exact ((continuous_multiplier ds).comp hg).mul hEval

/-- The actual extended right action is jointly continuous for each real standard module. -/
def RealStandardCompactBanachActionStatement : Prop :=
  ∀ (n : ℕ) (ds : List RealBlock),
    IsContinuousRepresentation (representation (n := n) ds)

theorem realStandardCompactBanachAction : RealStandardCompactBanachActionStatement :=
  fun n ds => isContinuousRepresentation (n := n) ds

end Langlands.Global.RankinSelbergGlobal.RealStandardCompactBanach
