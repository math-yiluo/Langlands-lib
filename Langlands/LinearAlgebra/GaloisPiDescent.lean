import Langlands.LinearAlgebra.GaloisSubmoduleDescent
import Mathlib.LinearAlgebra.TensorProduct.Pi
import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic

/-! # Scalar extension and Galois descent in finite coordinate spaces -/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u v

open scoped TensorProduct

namespace Langlands.LinearAlgebra.GaloisPiDescent

variable {k K : Type u} [Field k] [Field K] [Algebra k K]
  {ι : Type v} [Fintype ι] [DecidableEq ι]

/-- Extend a finite vector coefficientwise to the extension field. -/
def extend : (ι → k) →ₗ[k] (ι → K) where
  toFun x := fun i => algebraMap k K (x i)
  map_add' x y := by ext i; exact map_add _ _ _
  map_smul' a x := by
    ext i
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Algebra.smul_def, map_mul]

omit [Fintype ι] [DecidableEq ι] in
@[simp] theorem extend_apply (x : ι → k) (i : ι) :
    extend (K := K) x i = algebraMap k K (x i) := rfl

/-- The extended subspace is the extension-field span of the original vectors. -/
def scalarExtension (V : Submodule k (ι → k)) : Submodule K (ι → K) :=
  Submodule.span K {x | ∃ v ∈ V, extend v = x}

/-- Recover the original vectors in an extension-field subspace. -/
def descend (W : Submodule K (ι → K)) : Submodule k (ι → k) :=
  (W.restrictScalars k).comap extend

omit [Fintype ι] [DecidableEq ι] in
@[simp] theorem mem_descend (W : Submodule K (ι → K)) (x : ι → k) :
    x ∈ descend W ↔ extend x ∈ W := Iff.rfl

/-- Scalar extension reflects membership of original vectors, for every field extension. -/
theorem extend_mem_scalarExtension_iff (V : Submodule k (ι → k)) (x : ι → k) :
    extend (K := K) x ∈ scalarExtension V ↔ x ∈ V := by
  let e := TensorProduct.piScalarRight k K K ι
  have he (v : ι → k) : e (1 ⊗ₜ[k] v) = extend v := by
    ext i
    simp [e, TensorProduct.piScalarRight_apply, TensorProduct.piScalarRightHom_tmul,
      Algebra.smul_def]
  let q := V.mkQ
  let F := (q.baseChange K).comp e.symm.toLinearMap
  have hkill : scalarExtension (K := K) V ≤ LinearMap.ker F := by
    apply Submodule.span_le.mpr
    rintro _ ⟨v, hv, rfl⟩
    change q.baseChange K (e.symm (extend v)) = 0
    rw [← he, LinearEquiv.symm_apply_apply, LinearMap.baseChange_tmul]
    have hvq : q v = 0 := (Submodule.Quotient.mk_eq_zero V).mpr hv
    rw [hvq, TensorProduct.tmul_zero]
  constructor
  · intro hx
    have h := hkill hx
    change q.baseChange K (e.symm (extend x)) = 0 at h
    rw [← he, LinearEquiv.symm_apply_apply, LinearMap.baseChange_tmul] at h
    apply (Submodule.Quotient.mk_eq_zero V).mp
    change q x = 0
    simpa only [Module.FaithfullyFlat.one_tmul_eq_zero_iff] using h
  · intro hx
    exact Submodule.subset_span ⟨x, hx, rfl⟩

@[simp] theorem descend_scalarExtension (V : Submodule k (ι → k)) :
    descend (scalarExtension (K := K) V) = V := by
  ext x
  exact extend_mem_scalarExtension_iff V x

/-- Coefficientwise field-automorphism stability of a finite-coordinate subspace. -/
def IsGaloisStable (W : Submodule K (ι → K)) : Prop :=
  ∀ (σ : K ≃ₐ[k] K) (x : ι → K), x ∈ W → (fun i => σ (x i)) ∈ W

omit [Fintype ι] [DecidableEq ι] in
/-- Scalar-extended subspaces are stable under every ground-field automorphism. -/
theorem isGaloisStable_scalarExtension (V : Submodule k (ι → k)) :
    IsGaloisStable (k := k) (scalarExtension (K := K) V) := by
  intro σ x hx
  induction hx using Submodule.span_induction with
  | mem x hx =>
      obtain ⟨v, hv, rfl⟩ := hx
      have h : (fun i => σ (extend (K := K) v i)) = extend v := by
        ext i
        exact σ.commutes (v i)
      rw [h]
      exact Submodule.subset_span ⟨v, hv, rfl⟩
  | zero => simpa only [Pi.zero_def, map_zero] using (scalarExtension (K := K) V).zero_mem
  | add x y hx hy ihx ihy =>
      simpa only [Pi.add_def, map_add] using (scalarExtension (K := K) V).add_mem ihx ihy
  | smul a x hx ih =>
      simpa only [Pi.smul_def, smul_eq_mul, map_mul] using
        (scalarExtension (K := K) V).smul_mem (σ a) ih

variable [IsGalois k K]

omit [DecidableEq ι] in
/-- Galois-stable finite-coordinate subspaces are spanned by original vectors. -/
theorem eq_span_ground_vectors (W : Submodule K (ι → K))
    (hW : IsGaloisStable (k := k) W) :
    W = Submodule.span K {x | ∃ v : ι → k, extend v = x ∧ x ∈ W} := by
  let e := Finsupp.linearEquivFunOnFinite K K ι
  let W' := W.comap e.toLinearMap
  have hW' (σ : K ≃ₐ[k] K) (x : ι →₀ K) (hx : x ∈ W') :
      GaloisSubmoduleDescent.conjugate σ x ∈ W' := hW σ (e x) hx
  have hspan := GaloisSubmoduleDescent.eq_span_ground_vectors W' hW'
  apply le_antisymm
  · intro x hx
    have hx' : e.symm x ∈ W' := by
      change e (e.symm x) ∈ W
      simpa only [LinearEquiv.apply_symm_apply] using hx
    rw [hspan] at hx'
    have hall : ∀ (z : ι →₀ K), z ∈ Submodule.span K
        {z | ∃ v : ι →₀ k, GaloisSubmoduleDescent.extend v = z ∧ z ∈ W'} →
        e z ∈ Submodule.span K {z | ∃ v : ι → k, extend v = z ∧ z ∈ W} := by
      intro z hz
      induction hz using Submodule.span_induction with
      | mem z hz =>
          obtain ⟨v, rfl, hv⟩ := hz
          exact Submodule.subset_span ⟨v, rfl, hv⟩
      | zero => simpa only [map_zero] using (Submodule.zero_mem _)
      | add z t hz ht ihz iht =>
          simpa only [map_add] using Submodule.add_mem _ ihz iht
      | smul a z hz ih =>
          simpa only [map_smul] using Submodule.smul_mem _ a ih
    simpa only [LinearEquiv.apply_symm_apply] using hall _ hx'
  · apply Submodule.span_le.mpr
    rintro x ⟨v, hv, hx⟩
    exact hx

omit [DecidableEq ι] in
/-- Scalar extension recovers every Galois-stable subspace from its original vectors. -/
theorem scalarExtension_descend (W : Submodule K (ι → K))
    (hW : IsGaloisStable (k := k) W) :
    scalarExtension (descend (k := k) W) = W := by
  have hset : {x : ι → K | ∃ v ∈ descend (k := k) W, extend v = x} =
      {x | ∃ v : ι → k, extend v = x ∧ x ∈ W} := by
    ext x
    constructor
    · rintro ⟨v, hv, rfl⟩
      exact ⟨v, rfl, hv⟩
    · rintro ⟨v, hv, hx⟩
      exact ⟨v, by rw [mem_descend, hv]; exact hx, hv⟩
  change Submodule.span K {x | ∃ v ∈ descend (k := k) W, extend v = x} = W
  rw [hset]
  exact (eq_span_ground_vectors W hW).symm

end Langlands.LinearAlgebra.GaloisPiDescent
