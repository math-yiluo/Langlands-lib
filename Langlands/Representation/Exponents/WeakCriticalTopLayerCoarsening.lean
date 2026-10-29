import Langlands.Representation.Classification.MaximalConeExponents
import Langlands.Representation.Classification.MaximalConeAssembly

/-!
# Restricting opposite dual Jacquet vectors to a consecutive coarsening

A functional on the opposite Jacquet quotient along a block shape `B` is the same
as a source functional invariant under the opposite radical of `B`. The opposite
radical of a consecutive coarsening `C` of `B` is smaller, so the same source
functional defines a functional on the opposite Jacquet quotient along `C`. This
restriction is linear, injective, and intertwines the action of the coarse block
scalars with the action of their fine images.
-/

noncomputable section

namespace Langlands

open GeneralLinear
open scoped BigOperators

universe uF uV

namespace PadicField.TopologicalData

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p} (T : F.TopologicalData) {n : ℕ}

section Coarsen

variable {B C : BlockShape n} {q : Fin B.length → Fin C.length}

theorem subgroupInvariantDual_le_of_coarsen (hq : Monotone q)
    (hsize : ∀ j, C.size j = ∑ i ∈ Finset.univ.filter (fun i => q i = j), B.size i)
    (A : Rep.{uV} ℂ (GeneralLinear n F.Carrier)) :
    Jacquet.subgroupInvariantDual A.ρ (B.oppositeUnipotentSubgroup F.Carrier) ≤
      Jacquet.subgroupInvariantDual A.ρ (C.oppositeUnipotentSubgroup F.Carrier) := by
  intro f hf g v
  exact hf ⟨g.val, BlockShape.oppositeUnipotentSubgroup_le_of_coarsen F.Carrier hq hsize
    g.property⟩ v

/-- The restriction of fine opposite dual vectors to the coarse opposite quotient. -/
def dualJacquetCoarsen (hq : Monotone q)
    (hsize : ∀ j, C.size j = ∑ i ∈ Finset.univ.filter (fun i => q i = j), B.size i)
    (A : Rep.{uV} ℂ (GeneralLinear n F.Carrier)) :
    T.splitCentreDualJacquet B A →ₗ[ℂ] T.splitCentreDualJacquet C A :=
  ((T.splitCentreDualJacquetSourceEquiv C A).symm.toLinearMap ∘ₗ
    (Submodule.inclusion (subgroupInvariantDual_le_of_coarsen hq hsize A)) ∘ₗ
      (T.splitCentreDualJacquetSourceEquiv B A).toLinearMap :)

variable (hq : Monotone q)
  (hsize : ∀ j, C.size j = ∑ i ∈ Finset.univ.filter (fun i => q i = j), B.size i)
  (A : Rep.{uV} ℂ (GeneralLinear n F.Carrier))

/-- Evaluation of the dual split-centre action through source functionals. -/
theorem splitCentreDualJacquetSource_action {D : BlockShape n} (a : Fin D.length → F.Carrierˣ)
    (φ : T.splitCentreDualJacquet D A) (v : A) :
    (T.splitCentreDualJacquetSourceEquiv D A ((T.splitCentreDualJacquet D A).ρ a φ)).val v =
      (T.leviHalfModulus D (D.blockScalarLevi F.Carrier a) : ℂ) *
        (T.splitCentreDualJacquetSourceEquiv D A φ).val
          (A.ρ (D.leviEmbedding F.Carrier (D.blockScalarLevi F.Carrier a)) v) :=
  T.splitCentreDualJacquet_apply_mk D A a φ v

/-- Dual vectors are determined by their source functionals. -/
theorem splitCentreDualJacquet_ext {D : BlockShape n} {φ φ' : T.splitCentreDualJacquet D A}
    (h : ∀ v : A, (T.splitCentreDualJacquetSourceEquiv D A φ).val v =
      (T.splitCentreDualJacquetSourceEquiv D A φ').val v) : φ = φ' :=
  (T.splitCentreDualJacquetSourceEquiv D A).injective (Subtype.ext (LinearMap.ext h))

theorem dualJacquetCoarsen_source (φ : T.splitCentreDualJacquet B A) (v : A) :
    (T.splitCentreDualJacquetSourceEquiv C A (T.dualJacquetCoarsen hq hsize A φ)).val v =
      (T.splitCentreDualJacquetSourceEquiv B A φ).val v := by
  change ((T.splitCentreDualJacquetSourceEquiv C A)
    ((T.splitCentreDualJacquetSourceEquiv C A).symm _)).val v = _
  rw [LinearEquiv.apply_symm_apply]
  rfl

theorem dualJacquetCoarsen_injective :
    Function.Injective (T.dualJacquetCoarsen hq hsize A) := by
  intro φ ψ h
  apply T.splitCentreDualJacquet_ext A
  intro v
  rw [← T.dualJacquetCoarsen_source hq hsize A φ v,
    ← T.dualJacquetCoarsen_source hq hsize A ψ v, h]

/-- Coarse block scalars act on restricted vectors through their fine images. -/
theorem dualJacquetCoarsen_comm (c : Fin C.length → F.Carrierˣ)
    (φ : T.splitCentreDualJacquet B A) :
    T.dualJacquetCoarsen hq hsize A ((T.splitCentreDualJacquet B A).ρ (c ∘ q) φ) =
      (T.splitCentreDualJacquet C A).ρ c (T.dualJacquetCoarsen hq hsize A φ) := by
  apply T.splitCentreDualJacquet_ext A
  intro v
  rw [T.dualJacquetCoarsen_source hq hsize A, T.splitCentreDualJacquetSource_action A,
    T.splitCentreDualJacquetSource_action A, T.dualJacquetCoarsen_source hq hsize A,
    BlockShape.leviEmbedding_blockScalarLevi_coarsen F.Carrier hq hsize,
    leviHalfModulus_apply, leviHalfModulus_apply,
    T.leviModulus_blockScalarLevi_coarsen hq hsize]

theorem dualJacquetCoarsen_defect_pow (c : Fin C.length → F.Carrierˣ) (z : ℂ) (k : ℕ)
    (φ : T.splitCentreDualJacquet B A) :
    T.dualJacquetCoarsen hq hsize A
        ((((T.splitCentreDualJacquet B A).ρ (c ∘ q) - z • 1) ^ k) φ) =
      (((T.splitCentreDualJacquet C A).ρ c - z • 1) ^ k)
        (T.dualJacquetCoarsen hq hsize A φ) := by
  induction k generalizing φ with
  | zero => rfl
  | succ k ih =>
      rw [pow_succ, Module.End.mul_apply, ih, pow_succ, Module.End.mul_apply]
      congr 1
      simp only [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply, map_sub,
        map_smul]
      rw [T.dualJacquetCoarsen_comm hq hsize A]

/-- Generalized dual eigenvectors restrict to generalized dual eigenvectors of the
restricted character. -/
theorem dualJacquetCoarsen_mem_generalized
    {ψ : (Fin B.length → F.Carrierˣ) →* ℂˣ}
    {φ : T.splitCentreDualJacquet B A}
    (hφ : φ ∈ generalizedCommutativeCharacterSpace (T.splitCentreDualJacquet B A).ρ ψ) :
    T.dualJacquetCoarsen hq hsize A φ ∈ generalizedCommutativeCharacterSpace
      (T.splitCentreDualJacquet C A).ρ (ψ.comp (MaximalConeAssembly.precomp q)) := by
  obtain ⟨k, hk⟩ := (mem_generalizedCommutativeCharacterSpace _ ψ φ).mp hφ
  refine (mem_generalizedCommutativeCharacterSpace _ _ _).mpr ⟨k, fun c => ?_⟩
  have h := T.dualJacquetCoarsen_defect_pow hq hsize A c (ψ (c ∘ q) : ℂ) k φ
  rw [hk (c ∘ q), map_zero] at h
  exact h.symm

end Coarsen

end PadicField.TopologicalData

end Langlands
