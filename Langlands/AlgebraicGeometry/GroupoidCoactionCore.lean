import Langlands.AlgebraicGeometry.GroupoidCoactionTensor
import Mathlib.RingTheory.Noetherian.Basic
import Mathlib.LinearAlgebra.TensorProduct.Finiteness

/-! # Finite cores of coactions -/

universe u v

open TensorProduct

namespace Langlands.AlgebraicGeometry

variable {B C : Type u} [CommRing B] [CommRing C] [Algebra B C]
variable {t : B →+* C}
variable {M N : Type v} [AddCommGroup M] [Module B M] [AddCommGroup N] [Module B N]

namespace GroupoidCoaction

/-- Tensor a linear map, retaining the target action on the tensor module. -/
def targetMap (f : M →ₗ[B] N) : TargetModule t M →ₗ[B] TargetModule t N where
  toFun x := ⟨LinearMap.lTensor C f x.val⟩
  map_add' x y := by
    apply (targetModuleEquiv t N).injective
    exact map_add (LinearMap.lTensor C f) x.val y.val
  map_smul' b x := by
    apply (targetModuleEquiv t N).injective
    exact lTensor_alg_smul f (t b) x.val

/-- The obstruction to having coaction coefficients in a submodule. -/
def coreMap (θ : GroupoidCoaction t M) (H : Submodule B M) :
    M →ₗ[B] TargetModule t (M ⧸ H) :=
  (targetMap H.mkQ).comp θ.targetLinearMap

/-- The elements whose coaction has coefficients in `H`. -/
def core (θ : GroupoidCoaction t M) (H : Submodule B M) : Submodule B M :=
  LinearMap.ker (coreMap θ H)

lemma mem_core_iff (θ : GroupoidCoaction t M) (H : Submodule B M) (m : M) :
    m ∈ core θ H ↔ LinearMap.lTensor C H.mkQ (θ.coaction m) = 0 := by
  change (TargetModule.mk _ : TargetModule t (M ⧸ H)) = 0 ↔ _
  exact (targetModuleEquiv t (M ⧸ H)).injective.eq_iff.symm

lemma core_le (hE : RingEtaleEquivalenceRelation t)
    (θ : GroupoidCoaction t M) (H : Submodule B M) : core θ H ≤ H := by
  intro m hm
  have hzero := (mem_core_iff θ H m).mp hm
  have h := congrArg (LinearMap.rTensor (M ⧸ H) hE.identity.toLinearMap) hzero
  rw [← lTensor_rTensor_commute, θ.counit B hE.identity hE.identity_comp_t] at h
  have hq := congrArg (TensorProduct.lid B (M ⧸ H)) h
  simpa using hq

lemma pairTensorMap_tmul_mk (c : C) (x : C ⊗[B] M) :
    pairTensorMap t M (c ⊗ₜ[B] TargetModule.mk x) =
      pairFirst t c • LinearMap.rTensor M (pairSecond t).toLinearMap x := by
  induction x with
  | tmul d m =>
    change (PairRing.mk (c ⊗ₜ[B] TargetRing.mk d) : PairRing t) ⊗ₜ[B] m =
      pairFirst t c • ((pairSecond t d) ⊗ₜ[B] m)
    rw [TensorProduct.smul_tmul', smul_eq_mul]
    congr 1
    apply (pairRingEquiv t).injective
    change c ⊗ₜ[B] TargetRing.mk d =
      (c ⊗ₜ[B] (1 : TargetRing t)) * ((1 : C) ⊗ₜ[B] TargetRing.mk d)
    simp only [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
  | add x y hx hy =>
    simp only [targetModule_mk_add, TensorProduct.tmul_add, map_add, smul_add, hx, hy]

lemma pairTensorMap_lTensor_coreMap (θ : GroupoidCoaction t M) (H : Submodule B M)
    (x : C ⊗[B] M) :
    pairTensorMap t (M ⧸ H) (LinearMap.lTensor C (coreMap θ H) x) =
      LinearMap.lTensor (PairRing t) H.mkQ
        (coactionCompose t M θ.coaction θ.map_smul
          (pairFirst t) (pairSecond t) (pair_compat t) x) := by
  induction x with
  | tmul c m =>
    change pairTensorMap t (M ⧸ H)
      (c ⊗ₜ[B] TargetModule.mk (LinearMap.lTensor C H.mkQ (θ.coaction m))) =
      LinearMap.lTensor (PairRing t) H.mkQ
        (pairFirst t c • LinearMap.rTensor M (pairSecond t).toLinearMap (θ.coaction m))
    rw [pairTensorMap_tmul_mk, lTensor_alg_smul, lTensor_rTensor_commute]
  | add x y hx hy => simp only [map_add, hx, hy]

noncomputable def pairComposite (hE : RingEtaleEquivalenceRelation t) :
    C →ₐ[B] PairRing t where
  toRingHom := (hE.trans (PairRing t) (pairFirst t) (pairSecond t) (pair_compat t)).choose
  commutes' b := congrArg (fun f : B →+* PairRing t => f b)
    (hE.trans (PairRing t) (pairFirst t) (pairSecond t) (pair_compat t)).choose_spec.2

lemma pairComposite_comp_t (hE : RingEtaleEquivalenceRelation t) :
    (pairComposite hE : C →+* PairRing t).comp t = (pairFirst t).comp t :=
  (hE.trans (PairRing t) (pairFirst t) (pairSecond t) (pair_compat t)).choose_spec.1

lemma core_stable (hE : RingEtaleEquivalenceRelation t)
    (θ : GroupoidCoaction t M) (H : Submodule B M) (m : core θ H) :
    LinearMap.lTensor C (coreMap θ H) (θ.coaction m) = 0 := by
  apply pairTensorMap_injective t (M ⧸ H)
  rw [map_zero, pairTensorMap_lTensor_coreMap,
    ← θ.coassoc (PairRing t) (pairFirst t) (pairSecond t) (pairComposite hE)
      (pair_compat t) (pairComposite_comp_t hE), lTensor_rTensor_commute,
    (mem_core_iff θ H m).mp m.property, map_zero]

section Flat

variable [Module.Flat B C]

/-- Restrict a coaction to its core, using flat tensor-kernel exactness. -/
noncomputable def coreSemilinearMap (hE : RingEtaleEquivalenceRelation t)
    (θ : GroupoidCoaction t M) (H : Submodule B M) :
    core θ H →ₛₗ[t] C ⊗[B] core θ H :=
  (LinearMap.tensorKerEquiv C C (coreMap θ H)).symm.toLinearMap.comp
    ((θ.semilinearMap.domRestrict (core θ H)).codRestrict
      (LinearMap.ker (AlgebraTensorModule.lTensor C C (coreMap θ H)))
      (fun m => core_stable hE θ H m))

lemma coreSemilinearMap_subtype (hE : RingEtaleEquivalenceRelation t)
    (θ : GroupoidCoaction t M) (H : Submodule B M) (m : core θ H) :
    LinearMap.lTensor C (core θ H).subtype (coreSemilinearMap hE θ H m) =
      θ.coaction m :=
  LinearMap.lTensor_ker_subtype_tensorKerEquiv_symm C C (coreMap θ H) _

end Flat

/-- The core inherits a coaction from the ambient module. -/
noncomputable def coreCoaction (hE : RingEtaleEquivalenceRelation t)
    (θ : GroupoidCoaction t M) (H : Submodule B M) : GroupoidCoaction t (core θ H) := by
  letI : Module.Flat B C := RingHom.flat_algebraMap_iff.mp
    (RingHom.Etale.iff_flat_and_formallyUnramified.mp hE.etale_algebraMap).1
  exact ofInjective hE θ (core θ H).subtype (core θ H).subtype_injective
    (coreSemilinearMap hE θ H).toAddMonoidHom
    (fun b m => (coreSemilinearMap hE θ H).map_smulₛₗ b m)
    (fun m => (coreSemilinearMap_subtype hE θ H m).symm)

lemma core_subtype_isHom (hE : RingEtaleEquivalenceRelation t)
    (θ : GroupoidCoaction t M) (H : Submodule B M) :
    (coreCoaction hE θ H).IsHom θ (core θ H).subtype := by
  let : Module.Flat B C := RingHom.flat_algebraMap_iff.mp
    (RingHom.Etale.iff_flat_and_formallyUnramified.mp hE.etale_algebraMap).1
  intro m
  exact (coreSemilinearMap_subtype hE θ H m).symm

lemma finite_core [IsNoetherianRing B] (hE : RingEtaleEquivalenceRelation t)
    (θ : GroupoidCoaction t M) (H : Submodule B M) [Module.Finite B H] :
    Module.Finite B (core θ H) :=
  Module.Finite.of_injective (Submodule.inclusion (core_le hE θ H))
    (Submodule.inclusion_injective _)

lemma mem_core_of_tensor_range (θ : GroupoidCoaction t M) (H : Submodule B M) (m : M)
    (hm : θ.coaction m ∈ LinearMap.range (LinearMap.lTensor C H.subtype)) :
    m ∈ core θ H := by
  rw [mem_core_iff]
  obtain ⟨x, hx⟩ := hm
  rw [← hx]
  clear hx
  induction x with
  | tmul c n =>
    simp only [LinearMap.lTensor_tmul, Submodule.subtype_apply, Submodule.mkQ_apply]
    rw [(Submodule.Quotient.mk_eq_zero H).mpr n.property, TensorProduct.tmul_zero]
  | add x y hx hy => simp [hx, hy]

/-- Every element belongs to a finite submodule carrying the restricted coaction. -/
theorem exists_finite_subcoaction [IsNoetherianRing B] (hE : RingEtaleEquivalenceRelation t)
    (θ : GroupoidCoaction t M) (m : M) :
    ∃ (H : Submodule B M) (θH : GroupoidCoaction t H),
      Module.Finite B H ∧ m ∈ H ∧ θH.IsHom θ H.subtype := by
  obtain ⟨H, hH, hm⟩ := TensorProduct.exists_finite_submodule_right_of_setFinite
    ({θ.coaction m} : Set (C ⊗[B] M)) (Set.finite_singleton _)
  let := hH
  exact ⟨core θ H, coreCoaction hE θ H, finite_core hE θ H,
    mem_core_of_tensor_range θ H m (hm (Set.mem_singleton _)), core_subtype_isHom hE θ H⟩

end GroupoidCoaction

end Langlands.AlgebraicGeometry
