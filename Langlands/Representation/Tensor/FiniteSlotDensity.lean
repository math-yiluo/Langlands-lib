import Langlands.Representation.Tensor.FiniteProperties

/-!
# Irreducibility from dense operator algebras in the tensor factors

One-slot tensor maps form an algebra homomorphism. A subspace invariant
under the generators in each slot is invariant under the generated
algebras. If each such algebra acts densely on finite sets of vectors,
every nonzero invariant subspace of the finite tensor is the whole tensor.
-/

noncomputable section

set_option autoImplicit false

open scoped TensorProduct

namespace Langlands.FiniteTensor

open Module

variable {k ι : Type*} [Field k] [DecidableEq ι]
    {V : ι → Type*} [∀ i, AddCommGroup (V i)] [∀ i, Module k (V i)]

/-- An endomorphism acts in the given tensor slot, with identity actions in the other slots. -/
def slotAlgebraHom (i : ι) : Module.End k (V i) →ₐ[k] Module.End k (⨂[k] j, V j) where
  toFun T := PiTensorProduct.map (slot i T)
  map_one' := by
    have h : slot i (1 : Module.End k (V i)) = fun j => (1 : Module.End k (V j)) := by
      simp [slot, Module.End.one_eq_id]
    rw [h, PiTensorProduct.map_one]
  map_mul' A B := by
    rw [← PiTensorProduct.map_mul]
    congr 1
    funext j
    by_cases h : j = i
    · subst j
      simp [slot]
    · simp [slot, h, ← Module.End.one_eq_id]
  map_zero' := (PiTensorProduct.mapMultilinear k V V).map_update_zero _ i
  map_add' A B := by
    exact PiTensorProduct.map_update_add _ i A B
  commutes' c := by
    have h : slot i (1 : Module.End k (V i)) = fun j => (1 : Module.End k (V j)) := by
      simp [slot, Module.End.one_eq_id]
    rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one]
    change PiTensorProduct.map (slot i (c • (1 : Module.End k (V i)))) = _
    rw [slot, PiTensorProduct.map_update_smul]
    change c • PiTensorProduct.map (slot i (1 : Module.End k (V i))) = _
    rw [h, PiTensorProduct.map_one]

/-- Invariance under the one-slot generators extends to their algebra. -/
theorem slotAlgebraHom_mem_of_adjoin (W : Submodule k (⨂[k] j, V j)) (i : ι)
    {S : Set (Module.End k (V i))}
    (hS : ∀ A ∈ S, ∀ x ∈ W, slotAlgebraHom i A x ∈ W)
    {A : Module.End k (V i)} (hA : A ∈ Algebra.adjoin k S) :
    ∀ x ∈ W, slotAlgebraHom i A x ∈ W := by
  induction hA using Algebra.adjoin_induction with
  | mem A hA => exact hS A hA
  | algebraMap c =>
    intro x hx
    rw [AlgHom.commutes, Algebra.algebraMap_eq_smul_one, LinearMap.smul_apply, Module.End.one_apply]
    exact W.smul_mem c hx
  | add A B _ _ hA hB =>
    intro x hx
    rw [map_add, LinearMap.add_apply]
    exact W.add_mem (hA x hx) (hB x hx)
  | mul A B _ _ hA hB =>
    intro x hx
    rw [map_mul, Module.End.mul_apply]
    exact hA _ (hB x hx)

variable [Fintype ι]

/-- Finite-set density in each factor makes a nonzero subspace invariant under
the individual slot generators equal to the whole finite tensor. -/
theorem eq_top_of_slot_density (W : Submodule k (⨂[k] j, V j))
    (S : ∀ i, Set (Module.End k (V i)))
    (hS : ∀ i (A : Module.End k (V i)), A ∈ S i → ∀ x ∈ W, slotAlgebraHom i A x ∈ W)
    (hd : ∀ i (F : Finset (V i)) (T : Module.End k (V i)),
      ∃ A ∈ Algebra.adjoin k (S i), ∀ v ∈ F, A v = T v)
    {x : ⨂[k] j, V j} (hx : x ∈ W) (hne : x ≠ 0) :
    W = ⊤ := by
  classical
  let b := fun i => Basis.ofVectorSpace k (V i)
  let bt := Basis.piTensorProduct b
  obtain ⟨p, hp⟩ : ∃ p, bt.repr x p ≠ 0 := by
    by_contra h
    push Not at h
    exact hne (bt.ext_elem_iff.mpr fun q => by simp [h q])
  have htprod (u : ∀ i, V i) : PiTensorProduct.tprod k u ∈ W := by
    let T : ∀ i, Module.End k (V i) := fun i => ((b i).coord (p i)).smulRight (u i)
    have ht : PiTensorProduct.map T x = bt.repr x p • PiTensorProduct.tprod k u := by
      have hmap : PiTensorProduct.map T =
          (bt.coord p).smulRight (PiTensorProduct.tprod k u) := by
        ext v
        simp [T, bt, Basis.piTensorProduct_repr_tprod_apply, MultilinearMap.map_smul_univ]
      rw [hmap]
      rfl
    let F : ∀ i, Finset (V i) := fun i => (bt.repr x).support.image (fun q => b i (q i))
    choose A hA hagree using fun i => hd i (F i) (T i)
    have hmap : PiTensorProduct.map A x = PiTensorProduct.map T x := by
      rw [← bt.linearCombination_repr x, Finsupp.linearCombination_apply,
        map_finsuppSum, map_finsuppSum]
      refine Finsupp.sum_congr (fun q hq => ?_)
      rw [map_smul, map_smul, Basis.piTensorProduct_apply, PiTensorProduct.map_tprod,
        PiTensorProduct.map_tprod]
      congr 2
      funext i
      exact hagree i _ (Finset.mem_image_of_mem _ hq)
    have hmem : PiTensorProduct.map A x ∈ W :=
      map_induction A (· ∈ W) (fun i y hy =>
        slotAlgebraHom_mem_of_adjoin W i (hS i) (hA i) y hy) x hx
    rw [hmap, ht] at hmem
    have h := W.smul_mem (bt.repr x p)⁻¹ hmem
    rwa [smul_smul, inv_mul_cancel₀ hp, one_smul] at h
  rw [eq_top_iff, ← PiTensorProduct.span_tprod_eq_top]
  exact Submodule.span_le.mpr (by rintro _ ⟨u, rfl⟩; exact htprod u)

end Langlands.FiniteTensor
