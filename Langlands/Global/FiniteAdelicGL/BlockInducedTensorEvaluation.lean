import Langlands.Global.FiniteAdelicGL.CompactProduct
import Langlands.Global.FiniteAdelicGL.LocalBlockCompactEvaluation
import Langlands.Global.FiniteAdelicGL.RestrictedTensor
import Langlands.Representation.RestrictedTensor.PointwiseEvaluation

/-!
# Restricted tensors in finite adelic block induction

Pointwise evaluation of the local induced sections gives a finite adelic
smooth section. Its parabolic action is the restricted tensor of the actual
normalized local parabolic actions.
-/

noncomputable section

open scoped Classical TensorProduct

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 120000

universe u uV

namespace Langlands.Global.FiniteAdelicGL

open Langlands.GeneralLinear Langlands.RestrictedTensor CompletionPadic

variable (F : Type u) [Field F] [NumberField F] {n : ℕ} (B : BlockShape n)
variable {V : FinitePlace F → Fin B.length → Type uV}
variable [∀ v i, AddCommGroup (V v i)] [∀ v i, Module ℂ (V v i)]
variable (σ : ∀ (v : FinitePlace F) (i : Fin B.length),
  Representation ℂ (FiniteLocalGL F (B.size i) v) (V v i))

local notation "A" => (fun v => LocalBlockInduced F B v (σ v))
local notation "W" => (fun v => PiTensorProduct ℂ (V v))
local notation "ρ" => (fun v => PadicField.canonicalNormalizedProductInduced (padicField v) B (σ v))
local notation "τ" => (fun v => localBlockInducing F B v (σ v))
local notation "P" => (AdelicBlockParabolic.Finite F B)
local notation "G" => (FiniteAdelicGL F n)

local instance localInducedGroup (v : FinitePlace F) : AddCommGroup (A v) :=
  Submodule.addCommGroup _

/-- Compatible references for local sections and the corresponding block coefficients. -/
structure BlockInducedReferences where
  exceptional : Finset (FinitePlace F)
  blockReference : ∀ v i, V v i
  sectionReference : ∀ v, A v
  blockReference_fixed : ∀ v ∉ exceptional, ∀ i (k : localIntegral F (B.size i) v),
    σ v i k.val (blockReference v i) = blockReference v i
  sectionReference_fixed : ∀ v ∉ exceptional, ∀ k : localIntegral F n v,
    ρ v k.val (sectionReference v) = sectionReference v
  sectionReference_evaluation : ∀ v ∉ exceptional, ∀ k : localIntegral F n v,
    localBlockCompactEvaluation F B v (σ v) k (sectionReference v) =
      PiTensorProduct.tprod ℂ (blockReference v)

namespace BlockInducedReferences

variable {F B σ} (D : BlockInducedReferences F B σ)

/-- The reference coefficient at a place is the tensor of its block references. -/
abbrev coefficientReference (v : FinitePlace F) : W v :=
  PiTensorProduct.tprod ℂ (D.blockReference v)

/-- The source is the actual restricted tensor of local induced sections. -/
abbrev Source := Space ℂ A D.exceptional D.sectionReference

/-- The coefficient space is the actual restricted tensor of local block tensors. -/
abbrev Coefficients := Space ℂ W D.exceptional D.coefficientReference

/-- The genuine finite adelic action on the source. -/
abbrev sourceRepresentation : Representation ℂ G D.Source :=
  tensorRepresentation F n ρ D.exceptional D.sectionReference
    (fun v hv k hk => D.sectionReference_fixed v hv ⟨k, hk⟩)

theorem sourceRepresentation_isSmooth : Langlands.IsSmooth D.sourceRepresentation := by
  apply isSmooth_tensorRepresentation
  intro v
  have h := (padicField v).canonicalTopologicalData.isSmooth_normalizedProductInduced B (σ v)
  change @Langlands.IsSmooth ℂ (FiniteLocalGL F n v) (A v) _ _ _ _
    ((padicField v).canonicalGeneralLinearTopology n) (ρ v) at h
  exact (congrArg (fun top =>
    @Langlands.IsSmooth ℂ (FiniteLocalGL F n v) (A v) _ _ _ _ top (ρ v))
    (localGL_topology_eq F v n)).mpr h

local notation "Pᵥ" => (fun v => B.parabolic (FiniteCompletion F v))
local notation "Hᵥ" => (fun v => Subgroup.comap (Subgroup.subtype (Pᵥ v))
  (localIntegralSubgroup F v n))

private def parabolicRestrictedProjection :
    P →* RestrictedGroup Pᵥ Hᵥ where
  toFun p := ⟨fun v => localParabolicProjection F B v p,
    (eventually_localIntegral F n p.val).mono fun _ hv => hv⟩
  map_one' := by
    apply RestrictedProduct.ext
    intro v
    exact (localParabolicProjection F B v).map_one
  map_mul' p q := by
    apply RestrictedProduct.ext
    intro v
    exact (localParabolicProjection F B v).map_mul p q

private theorem parabolic_reference_fixed (v : FinitePlace F) (hv : v ∉ D.exceptional)
    (p : Pᵥ v) (hp : p ∈ Hᵥ v) :
    τ v p (D.coefficientReference v) = D.coefficientReference v := by
  change p.val ∈ localIntegral F n v at hp
  rw [localBlockInducing_apply_of_integral F B v (σ v) p hp,
    coefficientReference, B.blockTensor_tprod]
  congr 1
  funext i
  exact D.blockReference_fixed v hv i
    ⟨_, localLeviProjection_mem_integral F B v p hp i⟩

/-- The parabolic acts by the actual restricted product of the normalized
local coefficient actions. -/
def parabolicAction : Representation ℂ P D.Coefficients :=
  (representation Hᵥ τ D.exceptional D.coefficientReference
    D.parabolic_reference_fixed).comp (parabolicRestrictedProjection (F := F) (B := B))

private def localEvaluation (v : FinitePlace F) (g : FiniteLocalGL F n v) :
    A v →ₗ[ℂ] W v where
  toFun f := f.val.val g
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private theorem reference_evaluation_eventually (g : G) :
    ∀ᶠ v in Filter.cofinite,
      localEvaluation (F := F) (B := B) (σ := σ) v (localProjection F n v g)
          (D.sectionReference v) = D.coefficientReference v :=
  (D.exceptional.eventually_cofinite_notMem.and (eventually_localIntegral F n g)).mono
    fun v hv => D.sectionReference_evaluation v hv.1 ⟨localProjection F n v g, hv.2⟩

/-- Evaluate a restricted tensor at an actual finite adelic matrix. -/
def evaluationAt (g : G) : D.Source →ₗ[ℂ] D.Coefficients :=
  RestrictedTensor.map D.exceptional D.exceptional D.sectionReference D.coefficientReference
    (fun v => localEvaluation (F := F) (B := B) (σ := σ) v (localProjection F n v g))
    (D.reference_evaluation_eventually g)

theorem evaluationAt_parabolic_mul (p : P) (g : G) :
    D.evaluationAt (p.val * g) = (D.parabolicAction p).comp (D.evaluationAt g) := by
  change RestrictedTensor.map _ _ _ _ _ _ =
    (RestrictedTensor.map D.exceptional D.exceptional D.coefficientReference D.coefficientReference
      (fun v => τ v (localParabolicProjection F B v p)) _).comp (RestrictedTensor.map _ _ _ _ _ _)
  rw [RestrictedTensor.map_comp]
  have h : (fun v => localEvaluation (F := F) (B := B) (σ := σ) v
      (localProjection F n v (p.val * g))) =
      fun v => (τ v (localParabolicProjection F B v p)).comp
        (localEvaluation (F := F) (B := B) (σ := σ) v (localProjection F n v g)) := by
    funext v
    apply LinearMap.ext
    intro f
    change f.val.val (localProjection F n v (p.val * g)) = _
    rw [map_mul]
    exact f.val.property (localParabolicProjection F B v p) (localProjection F n v g)
  simp only [h]

theorem evaluationAt_comp_sourceRepresentation (g d : G) :
    (D.evaluationAt g).comp (D.sourceRepresentation d) = D.evaluationAt (g * d) := by
  change (RestrictedTensor.map D.exceptional D.exceptional D.sectionReference D.coefficientReference
      (fun v => localEvaluation (F := F) (B := B) (σ := σ) v (localProjection F n v g)) _).comp
    (RestrictedTensor.map D.exceptional D.exceptional D.sectionReference D.sectionReference
      (fun v => ρ v (localProjection F n v d)) _) = _
  rw [RestrictedTensor.map_comp]
  have h : (fun v => (localEvaluation (F := F) (B := B) (σ := σ) v
      (localProjection F n v g)).comp (ρ v (localProjection F n v d))) =
      fun v => localEvaluation (F := F) (B := B) (σ := σ) v
        (localProjection F n v (g * d)) := by
    funext v
    apply LinearMap.ext
    intro f
    change f.val.val (localProjection F n v g * localProjection F n v d) =
      f.val.val (localProjection F n v (g * d))
    rw [map_mul]
  simp only [evaluationAt, h]

/-- The restriction to the standard integral group is the compact pointwise
evaluation, with no enlargement of the exceptional set. -/
theorem evaluationAt_compact (k : standardIntegral F n) (x : D.Source) :
    D.evaluationAt k.val x =
      pointwiseEvaluation (fun v => localBlockCompactEvaluation F B v (σ v)) D.exceptional
        D.sectionReference D.coefficientReference D.sectionReference_evaluation x
        (standardIntegralProductEquiv F n k) := by
  have h : ∀ v ∉ D.exceptional,
      localEvaluation (F := F) (B := B) (σ := σ) v (localProjection F n v k.val)
        (D.sectionReference v) = D.coefficientReference v := by
    intro v hv
    exact D.sectionReference_evaluation v hv (standardIntegralProductEquiv F n k v)
  unfold evaluationAt
  rw [map_eq_mapWithBound _ _ _ _ _ _ D.exceptional (Finset.Subset.refl _) h]
  rfl

local notation "Pfin" => (B.parabolic (FiniteAdeles F))

private def covariantPointwiseMap :
    D.Source →ₗ[ℂ] Induction.EquivariantFunctions Pfin D.parabolicAction := by
  let ev : D.Source →ₗ[ℂ] (G → D.Coefficients) := LinearMap.pi fun g => D.evaluationAt g
  refine ev.codRestrict (Representation.coindV (Pfin).subtype D.parabolicAction) ?_
  intro x p g
  change D.evaluationAt (p.val * g) x = D.parabolicAction p (D.evaluationAt g x)
  exact LinearMap.congr_fun (D.evaluationAt_parabolic_mul p g) x

private theorem covariantPointwiseMap_smooth (x : D.Source) :
    D.covariantPointwiseMap x ∈ smoothVectors (Induction.equivariantAction Pfin D.parabolicAction) := by
  obtain ⟨U, hU⟩ := D.sourceRepresentation_isSmooth x
  refine ⟨U, fun k => ?_⟩
  apply Subtype.ext
  funext g
  change D.evaluationAt (g * k.val) x = D.evaluationAt g x
  rw [← D.evaluationAt_comp_sourceRepresentation, LinearMap.comp_apply]
  exact congrArg (D.evaluationAt g) (hU k)

/-- Pointwise evaluation gives an actual intertwiner into the smooth induction
on the finite adelic group from its block parabolic. -/
def pointwiseInducedMap : D.sourceRepresentation.IntertwiningMap
    (Induction.smoothInduced Pfin D.parabolicAction) where
  toLinearMap := D.covariantPointwiseMap.codRestrict
    (smoothVectors (Induction.equivariantAction Pfin D.parabolicAction))
    D.covariantPointwiseMap_smooth
  isIntertwining' d := by
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    apply Subtype.ext
    funext g
    exact LinearMap.congr_fun (D.evaluationAt_comp_sourceRepresentation g d) x

@[simp]
theorem pointwiseInducedMap_eval (x : D.Source) (g : G) :
    Induction.eval (B.parabolic (FiniteAdeles F)) D.parabolicAction (D.pointwiseInducedMap x) g =
      D.evaluationAt g x := rfl

theorem pointwiseInducedMap_injective (hD : ∀ v ∉ D.exceptional, D.coefficientReference v ≠ 0) :
    Function.Injective D.pointwiseInducedMap := by
  intro x y hxy
  apply pointwiseEvaluation_injective (fun v => localBlockCompactEvaluation F B v (σ v))
    D.exceptional D.sectionReference D.coefficientReference D.sectionReference_evaluation
    (fun v => eq_zero_of_localBlockCompactEvaluation_zero F B v (σ v)) hD
  funext k
  let p := (standardIntegralProductEquiv F n).symm k
  have h := congrArg (fun f => Induction.eval (B.parabolic (FiniteAdeles F)) D.parabolicAction
    f p.val) hxy
  rwa [pointwiseInducedMap_eval, pointwiseInducedMap_eval, D.evaluationAt_compact,
    D.evaluationAt_compact, ContinuousMulEquiv.apply_symm_apply] at h

end BlockInducedReferences

end Langlands.Global.FiniteAdelicGL
