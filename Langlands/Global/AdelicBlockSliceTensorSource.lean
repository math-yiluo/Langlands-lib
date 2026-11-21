import Langlands.Global.AdelicBlockScalarEnvelopingAction
import Langlands.Representation.Parabolic.InducedSliceEvaluation

/-! # Inducing tensors from the actual smooth scalar sections -/

noncomputable section

open scoped TensorProduct

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 1200000
set_option maxRecDepth 4000

universe u v

namespace Langlands.Global.AdelicBlockScalarSections

open Automorphic GeneralLinear ArchimedeanGL

variable (F : Type u) [Field F] [NumberField F] {n : ℕ} (B : BlockShape n)
  (S : ∀ i : Fin B.length, OperatorRealization F (B.size i))
variable {A V : Type v} [AddCommGroup A] [Module ℂ A] [AddCommGroup V] [Module ℂ V]

local notation "G" => FiniteAdelicGL F n
local notation "K" => standardInfiniteCompact F n
local notation "H" => SmoothFunctions F n
local notation "W" => smoothCompactFiniteSections F B S
local notation "Wf" => FiniteSmoothRealizedSections F B S

local instance sliceTensorFiniteGroup : AddCommGroup Wf := Submodule.addCommGroup _
local instance sliceTensorSectionGroup : AddCommGroup W := Submodule.addCommGroup _
local instance sliceTensorInfiniteGroup : AddCommGroup H := Submodule.addCommGroup _

/-- The linear map taking all finite-indexed infinite slices of a scalar section. -/
def smoothSliceFamily : W →ₗ[ℂ] (G → H) := LinearMap.pi (smoothScalarSlice F B S)

@[simp]
theorem smoothSliceFamily_apply (f : W) (g : G) :
    smoothSliceFamily F B S f g = smoothScalarSlice F B S g f := rfl

theorem smoothSliceFamily_injective : Function.Injective (smoothSliceFamily F B S) :=
  smoothScalarSlice_injective F B S

variable (e : FiniteAdelicGL F n → A →ₗ[ℂ] V)

private def coefficientSlices (a : A) : (V →ₗ[ℂ] H) →ₗ[ℂ] (G → H) :=
  LinearMap.pi (φ := fun _ : G => H) fun g =>
    { toFun := fun c => c (e g a)
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }

/-- Infinite coefficient families whose pairing with every finite input is
realized by an actual smooth scalar block section. -/
def sliceTensorCoefficients : Submodule ℂ (V →ₗ[ℂ] H) :=
  ⨅ a : A, (LinearMap.range (smoothSliceFamily F B S)).comap (coefficientSlices F e a)

theorem mem_sliceTensorCoefficients_iff (c : V →ₗ[ℂ] H) :
    c ∈ sliceTensorCoefficients F B S e ↔
      ∀ a, ∃ f : W, ∀ g, smoothScalarSlice F B S g f = c (e g a) := by
  simp only [sliceTensorCoefficients, Submodule.mem_iInf, Submodule.mem_comap, LinearMap.mem_range]
  constructor <;> intro h a
  · obtain ⟨f, hf⟩ := h a
    exact ⟨f, congrFun hf⟩
  · obtain ⟨f, hf⟩ := h a
    exact ⟨f, funext hf⟩

local notation "I" => sliceTensorCoefficients F B S e

local instance sliceTensorCoefficientGroup : AddCommGroup I := Submodule.addCommGroup _

private theorem slices_mem_range (t : A ⊗[ℂ] I) :
    InducedSliceEvaluation.slices e (I).subtype t ∈ LinearMap.range (smoothSliceFamily F B S) := by
  let j : A ⊗[ℂ] I →ₗ[ℂ] (G → H) := InducedSliceEvaluation.slices e (I).subtype
  change j t ∈ LinearMap.range (smoothSliceFamily F B S)
  induction t using TensorProduct.inductionOn with
  | tmul a c =>
    obtain ⟨f, hf⟩ := (mem_sliceTensorCoefficients_iff F B S e c.val).mp c.property a
    exact ⟨f, funext hf⟩
  | add t s ht hs => exact (map_add j t s).symm ▸ Submodule.add_mem _ ht hs

/-- Pair the tensors and use the injective joint slice map to recover their
smooth scalar sections. -/
def sliceTensorSectionMap : A ⊗[ℂ] I →ₗ[ℂ] W :=
  let E := LinearEquiv.ofInjective (smoothSliceFamily F B S) (smoothSliceFamily_injective F B S)
  E.symm.toLinearMap.comp ((InducedSliceEvaluation.slices e (I).subtype).codRestrict
    (LinearMap.range (smoothSliceFamily F B S)) (slices_mem_range F B S e))

theorem smoothSliceFamily_sliceTensorSectionMap (t : A ⊗[ℂ] I) :
    smoothSliceFamily F B S (sliceTensorSectionMap F B S e t) =
      InducedSliceEvaluation.slices e (I).subtype t := by
  let j := InducedSliceEvaluation.slices e (I).subtype
  let E := LinearEquiv.ofInjective (smoothSliceFamily F B S) (smoothSliceFamily_injective F B S)
  let v : LinearMap.range (smoothSliceFamily F B S) := ⟨j t, slices_mem_range F B S e t⟩
  change (E (E.symm v)).val = v.val
  exact congrArg Subtype.val (E.apply_symm_apply v)

@[simp]
theorem smoothScalarSlice_sliceTensorSectionMap_tmul (a : A) (c : I) (g : G) :
    smoothScalarSlice F B S g (sliceTensorSectionMap F B S e (a ⊗ₜ[ℂ] c)) = c.val (e g a) :=
  congrFun (smoothSliceFamily_sliceTensorSectionMap F B S e _) g

theorem sliceTensorSectionMap_injective
    (h : Function.Injective (InducedSliceEvaluation.slices e (I).subtype)) :
    Function.Injective (sliceTensorSectionMap F B S e) := by
  intro t s hts
  apply h
  rw [← smoothSliceFamily_sliceTensorSectionMap, ← smoothSliceFamily_sliceTensorSectionMap, hts]

private def coefficientOperator (D : Module.End ℂ H) (D' : Module.End ℂ W)
    (hD : ∀ g f, smoothScalarSlice F B S g (D' f) = D (smoothScalarSlice F B S g f)) :
    Module.End ℂ I :=
  ((LinearMap.compRight (M := V) ℂ D).comp (I).subtype).codRestrict I fun c =>
    (mem_sliceTensorCoefficients_iff F B S e (D.comp c.val)).mpr fun a => by
      obtain ⟨f, hf⟩ := (mem_sliceTensorCoefficients_iff F B S e c.val).mp c.property a
      exact ⟨D' f, fun g => (hD g f).trans (congrArg D (hf g))⟩

/-- Infinite compact translation acts on each smooth coefficient by postcomposition. -/
def sliceTensorCompactAction : Representation ℂ K I where
  toFun k := coefficientOperator F B S e (smoothRightAction F n k.val)
    (smoothCompactAction F B S k) (smoothScalarSlice_compactAction F B S k)
  map_one' := by
    apply LinearMap.ext
    intro c
    apply Subtype.ext
    apply LinearMap.ext
    intro v
    change smoothRightAction F n ((1 : K).val) (c.val v) = c.val v
    rw [Subgroup.coe_one, map_one, Module.End.one_apply]
  map_mul' k l := by
    apply LinearMap.ext
    intro c
    apply Subtype.ext
    apply LinearMap.ext
    intro v
    change smoothRightAction F n ((k * l).val) (c.val v) =
      smoothRightAction F n k.val (smoothRightAction F n l.val (c.val v))
    rw [Subgroup.coe_mul, map_mul, Module.End.mul_apply]

/-- The actual smooth enveloping action acts on each infinite coefficient. -/
def sliceTensorEnvelopingAction : EnvelopingAlgebra F n →ₐ[ℂ] Module.End ℂ I where
  toFun b := coefficientOperator F B S e (envelopingAction F n b)
    (sectionEnvelopingAction F B S b) (fun g f => smoothScalarSlice_sectionEnvelopingAction F B S b f g)
  map_one' := by
    apply LinearMap.ext
    intro c
    apply Subtype.ext
    apply LinearMap.ext
    intro v
    change envelopingAction F n 1 (c.val v) = c.val v
    rw [map_one, Module.End.one_apply]
  map_mul' b d := by
    apply LinearMap.ext
    intro c
    apply Subtype.ext
    apply LinearMap.ext
    intro v
    change envelopingAction F n (b * d) (c.val v) =
      envelopingAction F n b (envelopingAction F n d (c.val v))
    rw [map_mul, Module.End.mul_apply]
  map_zero' := by
    apply LinearMap.ext
    intro c
    apply Subtype.ext
    apply LinearMap.ext
    intro v
    change envelopingAction F n 0 (c.val v) = 0
    rw [map_zero, LinearMap.zero_apply]
  map_add' b d := by
    apply LinearMap.ext
    intro c
    apply Subtype.ext
    apply LinearMap.ext
    intro v
    change envelopingAction F n (b + d) (c.val v) =
      envelopingAction F n b (c.val v) + envelopingAction F n d (c.val v)
    rw [map_add, LinearMap.add_apply]
  commutes' z := by
    apply LinearMap.ext
    intro c
    apply Subtype.ext
    apply LinearMap.ext
    intro v
    change envelopingAction F n (algebraMap ℂ _ z) (c.val v) = z • c.val v
    rw [AlgHom.commutes, Module.algebraMap_end_apply]

/-- Finite right translation on the first factor evaluates as actual scalar translation. -/
theorem sliceTensorSectionMap_finite (ρ : Representation ℂ G A)
    (he : ∀ d g a, e g (ρ d a) = e (g * d) a) (d : G) (t : A ⊗[ℂ] I) :
    sliceTensorSectionMap F B S e ((ρ d).rTensor I t) =
      smoothCompactFiniteAction F B S d (sliceTensorSectionMap F B S e t) := by
  induction t using TensorProduct.inductionOn with
  | tmul a c =>
    apply smoothScalarSlice_injective F B S
    funext g
    simp only [LinearMap.rTensor_tmul, smoothScalarSlice_sliceTensorSectionMap_tmul,
      smoothScalarSlice_finiteAction, he]
  | add x y hx hy => simp only [map_add, hx, hy]

/-- The induced compact action evaluates as actual scalar compact translation. -/
theorem sliceTensorSectionMap_compact (k : K) (t : A ⊗[ℂ] I) :
    sliceTensorSectionMap F B S e ((sliceTensorCompactAction F B S e k).lTensor A t) =
      smoothCompactAction F B S k (sliceTensorSectionMap F B S e t) := by
  induction t using TensorProduct.inductionOn with
  | tmul a c =>
    apply smoothScalarSlice_injective F B S
    funext g
    simp only [LinearMap.lTensor_tmul, smoothScalarSlice_sliceTensorSectionMap_tmul,
      smoothScalarSlice_compactAction]
    rfl
  | add x y hx hy => simp only [map_add, hx, hy]

/-- The induced enveloping action evaluates as actual scalar differentiation. -/
theorem sliceTensorSectionMap_enveloping (b : EnvelopingAlgebra F n) (t : A ⊗[ℂ] I) :
    sliceTensorSectionMap F B S e ((sliceTensorEnvelopingAction F B S e b).lTensor A t) =
      sectionEnvelopingAction F B S b (sliceTensorSectionMap F B S e t) := by
  induction t using TensorProduct.inductionOn with
  | tmul a c =>
    apply smoothScalarSlice_injective F B S
    funext g
    simp only [LinearMap.lTensor_tmul, smoothScalarSlice_sliceTensorSectionMap_tmul,
      smoothScalarSlice_sectionEnvelopingAction]
    rfl
  | add x y hx hy => simp only [map_add, hx, hy]

end Langlands.Global.AdelicBlockScalarSections
