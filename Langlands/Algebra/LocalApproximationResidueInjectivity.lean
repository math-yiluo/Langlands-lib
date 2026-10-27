import Langlands.Algebra.LocalApproximationResidueInjectivityStatement
import Langlands.Algebra.LocalTowerResidueFiberRings
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.RingTheory.Flat.Basic
import Mathlib.RingTheory.TensorProduct.Finite
import Mathlib.RingTheory.Localization.Submodule
import Mathlib.RingTheory.Noetherian.Basic

/-! # Eventual residue-fibre injectivity for local approximation systems: proof -/

open scoped TensorProduct
open IsLocalRing
open scoped Langlands.Algebra.LocalModuleSystem Langlands.Algebra.ResidueFiberTensor

universe uI uA uB uN uR uS uM

namespace Langlands.Algebra
namespace ResidueInjectivityProof

variable {ι : Type uI} [Preorder ι] [Nonempty ι] [IsDirectedOrder ι]
  {R : Type uR} {S : Type uS} [CommRing R] [CommRing S]
  [IsLocalRing R] [IsLocalRing S] [Algebra R S] [IsLocalHom (algebraMap R S)]

section Field
variable (D : LocalAlgebraSystem.{uI, uA, uB} ι R S)

/-- The target residue field as an algebra over a base component, through the base cocone. -/
@[instance_reducible]
noncomputable def fieldAlgebra (i : ι) : Algebra (D.base i) (ResidueField R) :=
  ((residue R).comp (D.baseι i)).toAlgebra

attribute [local instance] fieldAlgebra

theorem fieldAlgebra_algebraMap (i : ι) (r : D.base i) :
    algebraMap (D.base i) (ResidueField R) r = residue R (D.baseι i r) := rfl

theorem fieldAlgebra_smul (i : ι) (r : D.base i) (a : ResidueField R) :
    r • a = residue R (D.baseι i r) * a := rfl

theorem fieldAlgebra_smul_eq (i : ι) (r : D.base i) (a : ResidueField R) :
    r • a = D.baseι i r • a := by
  rw [fieldAlgebra_smul, Algebra.smul_def, ResidueField.algebraMap_eq]

/-- The identity of the target residue field, semilinear over a base transition. -/
noncomputable def fieldMap {i j : ι} (h : i ≤ j) :
    ResidueField R →ₛₗ[D.baseMap i j h] ResidueField R where
  toFun a := a
  map_add' _ _ := rfl
  map_smul' r a := by
    change r • a = D.baseMap i j h r • a
    rw [fieldAlgebra_smul, fieldAlgebra_smul, D.baseι_compat]

/-- The identity of the target residue field, semilinear over a base cocone map. -/
noncomputable def fieldCocone (i : ι) : ResidueField R →ₛₗ[D.baseι i] ResidueField R where
  toFun a := a
  map_add' _ _ := rfl
  map_smul' r a := fieldAlgebra_smul_eq D i r a

theorem exists_baseι_eq (hR : Function.Surjective D.baseColimitMap) (r : R) :
    ∃ i, ∃ r' : D.base i, D.baseι i r' = r := by
  obtain ⟨z, rfl⟩ := hR r
  obtain ⟨i, r', rfl⟩ := Ring.DirectLimit.exists_of z
  exact ⟨i, r', (D.baseColimitMap_of i r').symm⟩

/-- The component fibre ring over the target residue field. -/
abbrev FieldFiberRing (i : ι) := D.alg i ⊗[D.base i] ResidueField R

/-- The extended component fibre rings are Noetherian. -/
theorem fieldFiberRing_isNoetherianRing (i : ι) [Algebra.EssFiniteType (D.base i) (D.alg i)] :
    IsNoetherianRing (FieldFiberRing D i) := by
  have : IsNoetherianRing (ResidueField R ⊗[D.base i] D.alg i) :=
    Algebra.EssFiniteType.isNoetherianRing (ResidueField R) _
  exact isNoetherianRing_of_ringEquiv _
    (Algebra.TensorProduct.comm (D.base i) (ResidueField R) (D.alg i)).toRingEquiv

/-- The transition of the extended fibre rings. -/
noncomputable def fieldFiberRingMap {i j : ι} (h : i ≤ j) :
    FieldFiberRing D i →+* FieldFiberRing D j :=
  Algebra.TensorProduct.mapRingHom (D.baseMap i j h) (D.algMap i j h) (RingHom.id _)
    (by ext r; exact D.map_comm i j h r)
    (by ext r; simp [fieldAlgebra_algebraMap, D.baseι_compat])

@[simp] theorem fieldFiberRingMap_tmul {i j : ι} (h : i ≤ j) (s : D.alg i)
    (a : ResidueField R) :
    fieldFiberRingMap D h (s ⊗ₜ a) = D.algMap i j h s ⊗ₜ a := by
  simp [fieldFiberRingMap]

/-- The cocone of the extended fibre rings. -/
noncomputable def fieldFiberRingι (i : ι) : FieldFiberRing D i →+* S ⊗[R] ResidueField R :=
  Algebra.TensorProduct.mapRingHom (D.baseι i) (D.algι i) (RingHom.id _)
    (by ext r; exact D.ι_comm i r)
    (by ext r; simp [fieldAlgebra_algebraMap, ResidueField.algebraMap_eq])

@[simp] theorem fieldFiberRingι_tmul (i : ι) (s : D.alg i) (a : ResidueField R) :
    fieldFiberRingι D i (s ⊗ₜ a) = D.algι i s ⊗ₜ a := by
  simp [fieldFiberRingι]

end Field

attribute [local instance] fieldAlgebra

section Module
variable {D : LocalAlgebraSystem.{uI, uA, uB} ι R S}
  {M : Type uM} [AddCommGroup M] [Module S M]
  (E : LocalModuleSystem.{uI, uA, uB, uN, uR, uS, uM} D M)

/-- The component module with scalars extended to the target residue field. -/
abbrev FieldFiber (i : ι) := ResidueField R ⊗[D.base i] E.obj i

/-- The transition of the extended component modules. -/
noncomputable def fieldFiberMap {i j : ι} (h : i ≤ j) :
    FieldFiber E i →ₛₗ[D.baseMap i j h] FieldFiber E j :=
  TensorProduct.map (fieldMap D h) (E.baseMap h)

@[simp] theorem fieldFiberMap_tmul {i j : ι} (h : i ≤ j) (a : ResidueField R) (m : E.obj i) :
    fieldFiberMap E h (a ⊗ₜ m) = a ⊗ₜ E.map i j h m := rfl

theorem fieldFiberMap_self (i : ι) (x : FieldFiber E i) :
    fieldFiberMap E (le_refl i) x = x := by
  induction x using TensorProduct.inductionOn with
  | tmul a m => simp [E.directed.map_self]
  | add x y hx hy => rw [map_add, hx, hy]

theorem fieldFiberMap_comp {i j k : ι} (hij : i ≤ j) (hjk : j ≤ k) (x : FieldFiber E i) :
    fieldFiberMap E hjk (fieldFiberMap E hij x) = fieldFiberMap E (hij.trans hjk) x := by
  induction x using TensorProduct.inductionOn with
  | tmul a m => simp [E.directed.map_map]
  | add x y hx hy => rw [map_add, map_add, hx, hy, map_add]

theorem fieldFiber_directed :
    DirectedSystem (FieldFiber E) fun _ _ h ↦ (fieldFiberMap E h).toAddMonoidHom where
  map_self := fun {_} x ↦ fieldFiberMap_self E _ x
  map_map := fun {_ _ _} hij hjk x ↦ fieldFiberMap_comp E hij hjk x

section Colimit

/-- The additive direct limit of the extended component modules. -/
abbrev FieldFiberLimit : Type _ :=
  @AddCommGroup.DirectLimit ι _ (FieldFiber E) _ (Classical.decEq ι)
    (fun _ _ h ↦ (fieldFiberMap E h).toAddMonoidHom)

/-- The canonical map from a component to the direct limit. -/
noncomputable abbrev limitOf (i : ι) : FieldFiber E i →+ FieldFiberLimit E :=
  letI := Classical.decEq ι
  AddCommGroup.DirectLimit.of (FieldFiber E) (fun _ _ h ↦ (fieldFiberMap E h).toAddMonoidHom) i

theorem limitOf_map {i j : ι} (h : i ≤ j) (x : FieldFiber E i) :
    limitOf E j (fieldFiberMap E h x) = limitOf E i x := by
  let := Classical.decEq ι
  exact AddCommGroup.DirectLimit.of_f (G := FieldFiber E)
    (f := fun _ _ h ↦ (fieldFiberMap E h).toAddMonoidHom) h x

/-- The bilinear components of the inverse comparison map. -/
noncomputable def pairing (i : ι) : E.obj i →+ ResidueField R →+ FieldFiberLimit E :=
  AddMonoidHom.mk'
    (fun m ↦ AddMonoidHom.mk' (fun a ↦ limitOf E i (a ⊗ₜ m))
      (fun a b ↦ by rw [TensorProduct.add_tmul, map_add]))
    (fun m n ↦ by ext a; simp [TensorProduct.tmul_add])

@[simp] theorem pairing_apply (i : ι) (m : E.obj i) (a : ResidueField R) :
    pairing E i m a = limitOf E i (a ⊗ₜ m) := rfl

theorem pairing_compat {i j : ι} (h : i ≤ j) (m : E.obj i) :
    pairing E j (E.map i j h m) = pairing E i m := by
  ext a
  simp only [pairing_apply]
  exact limitOf_map E h (a ⊗ₜ m)

/-- The inverse comparison, before tensoring: a module element paired with a field element. -/
noncomputable def limitPairing (hM : Function.Bijective E.moduleColimitMap) :
    M →+ ResidueField R →+ FieldFiberLimit E :=
  letI := Classical.decEq ι
  (AddCommGroup.DirectLimit.lift E.obj (fun _ _ h ↦ (E.map _ _ h).toAddMonoidHom)
      (ResidueField R →+ FieldFiberLimit E) (pairing E)
      (fun _ _ h m ↦ pairing_compat E h m)).comp
    (AddEquiv.ofBijective E.moduleColimitMap hM).symm.toAddMonoidHom

theorem limitPairing_ιM (hM : Function.Bijective E.moduleColimitMap) (i : ι) (m : E.obj i) :
    limitPairing E hM (E.ιM i m) = pairing E i m := by
  let := Classical.decEq ι
  have hsymm : (AddEquiv.ofBijective E.moduleColimitMap hM).symm (E.ιM i m) =
      AddCommGroup.DirectLimit.of E.obj (fun _ _ h ↦ (E.map _ _ h).toAddMonoidHom) i m := by
    rw [AddEquiv.symm_apply_eq]
    exact (E.moduleColimitMap_of i m).symm
  simp only [limitPairing, AddMonoidHom.coe_comp, Function.comp_apply]
  erw [hsymm]
  exact AddCommGroup.DirectLimit.lift_of _ _ _ _ _

theorem exists_ιM_eq (hM : Function.Bijective E.moduleColimitMap) (m : M) :
    ∃ i, ∃ m' : E.obj i, E.ιM i m' = m := by
  let := Classical.decEq ι
  obtain ⟨z, rfl⟩ := hM.2 m
  refine AddCommGroup.DirectLimit.induction_on z (fun i x ↦ ?_)
  exact ⟨i, x, (E.moduleColimitMap_of i x).symm⟩

variable [Module R M] [IsScalarTower R S M]

/-- The cocone of the extended component modules. -/
noncomputable def fieldFiberι (i : ι) :
    FieldFiber E i →ₛₗ[D.baseι i] LocalModuleSystem.TargetResidueFiber R M :=
  TensorProduct.map (fieldCocone D i) (E.baseι i)

@[simp] theorem fieldFiberι_tmul (i : ι) (a : ResidueField R) (m : E.obj i) :
    fieldFiberι E i (a ⊗ₜ m) = a ⊗ₜ E.ιM i m := rfl

theorem fieldFiberι_compat {i j : ι} (h : i ≤ j) (x : FieldFiber E i) :
    fieldFiberι E j (fieldFiberMap E h x) = fieldFiberι E i x := by
  induction x using TensorProduct.inductionOn with
  | tmul a m => simp [E.ιM_compat]
  | add x y hx hy => rw [map_add, map_add, hx, hy, map_add]

theorem limitPairing_balanced (hM : Function.Bijective E.moduleColimitMap)
    (hR : Function.Surjective D.baseColimitMap) (r : R)
    (a : ResidueField R) (m : M) :
    (limitPairing E hM).flip (r • a) m = (limitPairing E hM).flip a (r • m) := by
  simp only [AddMonoidHom.flip_apply]
  obtain ⟨i, r', rfl⟩ := exists_baseι_eq D hR r
  obtain ⟨k, m', rfl⟩ := exists_ιM_eq E hM m
  obtain ⟨l, hil, hkl⟩ := exists_ge_ge i k
  rw [← D.baseι_compat i l hil r', ← E.ιM_compat k l hkl m']
  have hsmul : D.baseι l (D.baseMap i l hil r') • E.ιM l (E.map k l hkl m') =
      E.ιM l (D.baseMap i l hil r' • E.map k l hkl m') :=
    ((E.baseι l).map_smulₛₗ _ _).symm
  rw [hsmul, limitPairing_ιM, limitPairing_ιM, pairing_apply, pairing_apply,
    ← TensorProduct.smul_tmul, fieldAlgebra_smul_eq]

/-- The inverse comparison from the target residue module to the direct limit. -/
noncomputable def limitInverse (hM : Function.Bijective E.moduleColimitMap)
    (hR : Function.Surjective D.baseColimitMap) :
    LocalModuleSystem.TargetResidueFiber R M →+ FieldFiberLimit E :=
  TensorProduct.liftAddHom (limitPairing E hM).flip (limitPairing_balanced E hM hR)

theorem limitInverse_fieldFiberι (hM : Function.Bijective E.moduleColimitMap)
    (hR : Function.Surjective D.baseColimitMap) (i : ι)
    (x : FieldFiber E i) : limitInverse E hM hR (fieldFiberι E i x) = limitOf E i x := by
  induction x using TensorProduct.inductionOn with
  | tmul a m =>
    rw [fieldFiberι_tmul, limitInverse, TensorProduct.liftAddHom_tmul, AddMonoidHom.flip_apply,
      limitPairing_ιM, pairing_apply]
  | add x y hx hy => rw [map_add, map_add, hx, hy, map_add]

/-- A component element killed by the cocone dies at some later stage. -/
theorem exists_fieldFiberMap_eq_zero (hM : Function.Bijective E.moduleColimitMap)
    (hR : Function.Surjective D.baseColimitMap) {i : ι}
    (x : FieldFiber E i) (hx : fieldFiberι E i x = 0) :
    ∃ j, ∃ h : i ≤ j, fieldFiberMap E h x = 0 := by
  have h0 : limitOf E i x = 0 := by rw [← limitInverse_fieldFiberι E hM hR, hx, map_zero]
  let := Classical.decEq ι
  have := fieldFiber_directed E
  exact AddCommGroup.DirectLimit.of.zero_exact i x h0

end Colimit

section Noetherian

theorem fieldFiberMap_smul {i j : ι} (h : i ≤ j) (a : FieldFiberRing D i) (x : FieldFiber E i) :
    fieldFiberMap E h (a • x) = fieldFiberRingMap D h a • fieldFiberMap E h x := by
  induction a using TensorProduct.inductionOn with
  | tmul s b =>
    induction x using TensorProduct.inductionOn with
    | tmul c m =>
      rw [ResidueFiberTensor.tmul_smul_tmul, fieldFiberMap_tmul, fieldFiberMap_tmul,
        fieldFiberRingMap_tmul, ResidueFiberTensor.tmul_smul_tmul, LinearMap.map_smulₛₗ]
    | add x y hx hy => rw [smul_add, map_add, hx, hy, map_add, smul_add]
  | add a b ha hb => rw [add_smul, map_add, ha, hb, map_add, add_smul]

/-- The kernel of a transition, as a submodule over the extended fibre ring. -/
def transitionKernel {i j : ι} (h : i ≤ j) : Submodule (FieldFiberRing D i) (FieldFiber E i) where
  carrier := {x | fieldFiberMap E h x = 0}
  add_mem' {x y} hx hy := by
    simp only [Set.mem_ofPred_eq] at hx hy ⊢
    rw [map_add, hx, hy, add_zero]
  zero_mem' := map_zero _
  smul_mem' a x hx := by
    simp only [Set.mem_ofPred_eq] at hx ⊢
    rw [fieldFiberMap_smul, hx, smul_zero]

theorem mem_transitionKernel {i j : ι} (h : i ≤ j) (x : FieldFiber E i) :
    x ∈ transitionKernel E h ↔ fieldFiberMap E h x = 0 := Iff.rfl

variable [Module R M] [IsScalarTower R S M]

theorem fieldFiberι_smul (i : ι) (a : FieldFiberRing D i) (x : FieldFiber E i) :
    fieldFiberι E i (a • x) = fieldFiberRingι D i a • fieldFiberι E i x := by
  induction a using TensorProduct.inductionOn with
  | tmul s b =>
    induction x using TensorProduct.inductionOn with
    | tmul c m =>
      rw [ResidueFiberTensor.tmul_smul_tmul, fieldFiberι_tmul, fieldFiberι_tmul,
        fieldFiberRingι_tmul, ResidueFiberTensor.tmul_smul_tmul, LinearMap.map_smulₛₗ]
    | add x y hx hy => rw [smul_add, map_add, hx, hy, map_add, smul_add]
  | add a b ha hb => rw [add_smul, map_add, ha, hb, map_add, add_smul]

/-- The kernels of the transitions out of a fixed stage eventually contain the whole kernel of
the cocone map. -/
theorem eventually_kernel_stable (hR : Function.Surjective D.baseColimitMap)
    (hM : Function.Bijective E.moduleColimitMap) (i : ι)
    [Algebra.EssFiniteType (D.base i) (D.alg i)] [Module.Finite (D.alg i) (E.obj i)] :
    ∃ j₀, ∃ h₀ : i ≤ j₀, ∀ j (hj : j₀ ≤ j) (x : FieldFiber E i),
      fieldFiberι E i x = 0 → fieldFiberMap E (h₀.trans hj) x = 0 := by
  have := fieldFiberRing_isNoetherianRing D i
  have : Module.Finite (FieldFiberRing D i) (FieldFiber E i) :=
    Module.Finite.equiv
      (ResidueFiberTensor.linearComparison (D.base i) (D.alg i) (ResidueField R) (E.obj i))
  have : IsNoetherian (FieldFiberRing D i) (FieldFiber E i) :=
    isNoetherian_of_isNoetherianRing_of_finite _ _
  obtain ⟨N, ⟨j₀, h₀, rfl⟩, hmax⟩ := set_has_maximal_iff_noetherian.mpr ‹IsNoetherian _ _›
    {N | ∃ j, ∃ h : i ≤ j, N = transitionKernel E h} ⟨_, i, le_rfl, rfl⟩
  refine ⟨j₀, h₀, fun j hj x hx ↦ ?_⟩
  obtain ⟨k, hik, hk⟩ := exists_fieldFiberMap_eq_zero E hM hR x hx
  obtain ⟨l, hjl, hkl⟩ := exists_ge_ge j₀ k
  have hle : transitionKernel E h₀ ≤ transitionKernel E (h₀.trans hjl) := by
    intro y hy
    rw [mem_transitionKernel] at hy ⊢
    rw [← fieldFiberMap_comp E h₀ hjl, hy, map_zero]
  have heq : transitionKernel E h₀ = transitionKernel E (h₀.trans hjl) :=
    eq_of_le_of_not_lt hle (hmax _ ⟨l, _, rfl⟩)
  have hxl : x ∈ transitionKernel E (h₀.trans hjl) := by
    rw [mem_transitionKernel, ← fieldFiberMap_comp E hik hkl, hk, map_zero]
  rw [← heq, mem_transitionKernel] at hxl
  rw [← fieldFiberMap_comp E h₀ hj, hxl, map_zero]

end Noetherian

section Localization

theorem smul_mem_range {i j : ι} (h : i ≤ j) (b : D.RingBaseChange h) (x : FieldFiber E i) :
    ∃ x', (D.ringBaseChangeMap h b ⊗ₜ[D.base j] (1 : ResidueField R) : FieldFiberRing D j) •
      fieldFiberMap E h x = fieldFiberMap E h x' := by
  let := (D.baseMap i j h).toAlgebra
  induction b using TensorProduct.inductionOn with
  | tmul s r =>
    refine ⟨(s ⊗ₜ[D.base i] algebraMap (D.base j) (ResidueField R) r) • x, ?_⟩
    have key : (D.ringBaseChangeMap h (s ⊗ₜ r) ⊗ₜ[D.base j] (1 : ResidueField R) :
        FieldFiberRing D j) = D.algMap i j h s ⊗ₜ algebraMap (D.base j) (ResidueField R) r := by
      rw [D.ringBaseChangeMap_tmul, mul_comm (D.algMap i j h s), ← Algebra.smul_def,
        TensorProduct.smul_tmul, Algebra.smul_def, mul_one]
    rw [key, fieldFiberMap_smul, fieldFiberRingMap_tmul]
  | add b c hb hc =>
    obtain ⟨y, hy⟩ := hb
    obtain ⟨z, hz⟩ := hc
    exact ⟨y + z, by rw [map_add, TensorProduct.add_tmul, add_smul, hy, hz, map_add]⟩

theorem exists_unit_smul_eq {i j : ι} (h : i ≤ j) (hloc : D.IsPrimeLocalization h)
    (hsurj : Function.Surjective (E.moduleBaseChangeMap h)) (y : FieldFiber E j) :
    ∃ u : FieldFiberRing D j, IsUnit u ∧ ∃ x, u • y = fieldFiberMap E h x := by
  let := (D.baseMap i j h).toAlgebra
  let := (D.ringBaseChangeMap h).toAlgebra
  obtain ⟨p, hp, hlocp⟩ := hloc
  suffices H : ∃ w ∈ p.primeCompl, ∃ x, (D.ringBaseChangeMap h w ⊗ₜ[D.base j]
      (1 : ResidueField R) : FieldFiberRing D j) • y = fieldFiberMap E h x by
    obtain ⟨w, hw, x, hx⟩ := H
    refine ⟨_, ?_, x, hx⟩
    exact (IsLocalization.map_units (D.alg j) (⟨w, hw⟩ : p.primeCompl)).map
      Algebra.TensorProduct.includeLeftRingHom
  have hadd : ∀ y₁ y₂ : FieldFiber E j,
      (∃ w ∈ p.primeCompl, ∃ x, (D.ringBaseChangeMap h w ⊗ₜ[D.base j]
        (1 : ResidueField R) : FieldFiberRing D j) • y₁ = fieldFiberMap E h x) →
      (∃ w ∈ p.primeCompl, ∃ x, (D.ringBaseChangeMap h w ⊗ₜ[D.base j]
        (1 : ResidueField R) : FieldFiberRing D j) • y₂ = fieldFiberMap E h x) →
      ∃ w ∈ p.primeCompl, ∃ x, (D.ringBaseChangeMap h w ⊗ₜ[D.base j]
        (1 : ResidueField R) : FieldFiberRing D j) • (y₁ + y₂) = fieldFiberMap E h x := by
    rintro y₁ y₂ ⟨w₁, hw₁, x₁, hx₁⟩ ⟨w₂, hw₂, x₂, hx₂⟩
    obtain ⟨z₁, hz₁⟩ := smul_mem_range E h w₂ x₁
    obtain ⟨z₂, hz₂⟩ := smul_mem_range E h w₁ x₂
    refine ⟨w₁ * w₂, p.primeCompl.mul_mem hw₁ hw₂, z₁ + z₂, ?_⟩
    have e₁ : (D.ringBaseChangeMap h (w₁ * w₂) ⊗ₜ[D.base j] (1 : ResidueField R) :
        FieldFiberRing D j) • y₁ = fieldFiberMap E h z₁ := by
      rw [map_mul, mul_comm, ← mul_one (1 : ResidueField R),
        ← Algebra.TensorProduct.tmul_mul_tmul, mul_smul, hx₁, hz₁]
    have e₂ : (D.ringBaseChangeMap h (w₁ * w₂) ⊗ₜ[D.base j] (1 : ResidueField R) :
        FieldFiberRing D j) • y₂ = fieldFiberMap E h z₂ := by
      rw [map_mul, ← mul_one (1 : ResidueField R),
        ← Algebra.TensorProduct.tmul_mul_tmul, mul_smul, hx₂, hz₂]
    rw [smul_add, e₁, e₂, map_add]
  induction y using TensorProduct.inductionOn with
  | tmul a m' =>
    obtain ⟨t, rfl⟩ := hsurj m'
    induction t using TensorProduct.inductionOn with
    | tmul s' m =>
      obtain ⟨⟨b, w⟩, hbw⟩ := IsLocalization.surj p.primeCompl s'
      dsimp only at hbw
      rw [RingHom.algebraMap_toAlgebra] at hbw
      obtain ⟨x', hx'⟩ := smul_mem_range E h b (a ⊗ₜ m)
      refine ⟨w, w.2, x', ?_⟩
      rw [← hx', E.moduleBaseChangeMap_tmul, fieldFiberMap_tmul,
        ResidueFiberTensor.tmul_smul_tmul, ResidueFiberTensor.tmul_smul_tmul, smul_smul,
        mul_comm _ s', hbw]
    | add t₁ t₂ h₁ h₂ =>
      rw [map_add, TensorProduct.tmul_add]
      exact hadd _ _ h₁ h₂
  | add y₁ y₂ h₁ h₂ => exact hadd _ _ h₁ h₂

variable [Module R M] [IsScalarTower R S M]

theorem fieldFiberι_injective {i j₀ : ι} (h₀ : i ≤ j₀)
    (hstable : ∀ j (hj : j₀ ≤ j) (x : FieldFiber E i),
      fieldFiberι E i x = 0 → fieldFiberMap E (h₀.trans hj) x = 0)
    {j : ι} (hj : j₀ ≤ j) (hloc : D.IsPrimeLocalization (h₀.trans hj))
    (hsurj : Function.Surjective (E.moduleBaseChangeMap (h₀.trans hj))) :
    Function.Injective (fieldFiberι E j) := by
  rw [injective_iff_map_eq_zero]
  intro y hy
  obtain ⟨u, hu, x, hx⟩ := exists_unit_smul_eq E (h₀.trans hj) hloc hsurj y
  have hx0 : fieldFiberι E i x = 0 := by
    rw [← fieldFiberι_compat E (h₀.trans hj) x, ← hx, fieldFiberι_smul, hy, smul_zero]
  have hux : u • y = 0 := by rw [hx, hstable j hj x hx0]
  exact hu.smul_eq_zero.mp hux

end Localization

section Comparison
variable [Module R M] [IsScalarTower R S M]

/-- The cancellation of the intermediate residue field. -/
noncomputable def residueExtensionEquiv (j : ι) :
    letI := (D.residueι j).toAlgebra
    E.ResidueFiberExtension j ≃ₗ[ResidueField R] FieldFiber E j := by
  letI := (D.residueι j).toAlgebra
  letI : IsScalarTower (D.base j) (ResidueField (D.base j)) (ResidueField R) :=
    IsScalarTower.of_algebraMap_eq (fun _ ↦ rfl)
  exact TensorProduct.AlgebraTensorModule.cancelBaseChange (D.base j) (ResidueField (D.base j))
    (ResidueField R) (ResidueField R) (E.obj j)

theorem residueFiberΨ_eq (j : ι) (z : E.ResidueFiberExtension j) :
    E.residueFiberΨ j z = fieldFiberι E j (residueExtensionEquiv E j z) := by
  let := (D.residueι j).toAlgebra
  induction z using TensorProduct.inductionOn with
  | tmul a x =>
    induction x using TensorProduct.inductionOn with
    | tmul b m =>
      rw [LocalModuleSystem.residueFiberΨ_tmul_tmul]
      change _ = fieldFiberι E j ((b • a) ⊗ₜ m)
      rw [fieldFiberι_tmul, Algebra.smul_def, mul_comm]
      rfl
    | add x y hx hy => rw [TensorProduct.tmul_add, map_add, hx, hy, map_add, map_add]
  | add x y hx hy => rw [map_add, hx, hy, map_add, map_add]

omit [Module R M] [IsScalarTower R S M] in
theorem includeResidue_injective (j : ι) :
    letI := (D.residueι j).toAlgebra
    Function.Injective
      (fun x : E.ResidueFiber j ↦ (1 : ResidueField R) ⊗ₜ[ResidueField (D.base j)] x) := by
  let := (D.residueι j).toAlgebra
  have hf : Function.Injective
      (Algebra.linearMap (ResidueField (D.base j)) (ResidueField R)) :=
    fun a b hab ↦ (D.residueι j).injective hab
  have : Module.Flat (ResidueField (D.base j)) (E.ResidueFiber j) := Module.Flat.of_free
  have hr := Module.Flat.rTensor_preserves_injective_linearMap (M := E.ResidueFiber j) _ hf
  intro x y hxy
  apply (TensorProduct.lid (ResidueField (D.base j)) (E.ResidueFiber j)).symm.injective
  apply hr
  simpa using hxy

end Comparison
end Module
end ResidueInjectivityProof

open ResidueInjectivityProof in
/-- Eventual residue-fibre injectivity for every local approximation system. -/
theorem localApproximationResidueInjectivity :
    LocalApproximationResidueInjectivityStatement.{uI, uA, uB, uN, uR, uS, uM} := by
  intro ι _ _ _ R S _ _ _ _ _ _ D M _ _ _ _ E hE
  obtain ⟨⟨⟨hR, -⟩, hM⟩, -, hS, hfin, hloc, hbij⟩ := hE
  let i : ι := Classical.arbitrary ι
  have := hS i
  have := hfin i
  obtain ⟨j₀, h₀, hstable⟩ := eventually_kernel_stable E hR.2 hM i
  refine ⟨j₀, fun j hj ↦ ?_⟩
  have hinj := fieldFiberι_injective E h₀ hstable hj (hloc _ _ _) (hbij _ _ _).2
  have hΨ : Function.Injective (E.residueFiberΨ j) := by
    intro z₁ z₂ hz
    rw [residueFiberΨ_eq, residueFiberΨ_eq] at hz
    exact (residueExtensionEquiv E j).injective (hinj hz)
  refine ⟨hΨ, fun x₁ x₂ hx ↦ includeResidue_injective E j (hΨ ?_)⟩
  let := (D.residueι j).toAlgebra
  simp only [LocalModuleSystem.residueFiberΨ_tmul, one_smul]
  exact hx

end Langlands.Algebra
