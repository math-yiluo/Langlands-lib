import Mathlib.LinearAlgebra.Dual.Basis
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.PiTensorProduct.Finsupp

/-! Tensor products of scalar functions and their separately finite-dimensional slices. -/

open scoped BigOperators TensorProduct

noncomputable section
set_option autoImplicit false

namespace Langlands

variable {R ι : Type*} [Field R] [Fintype ι]
  {X : ι → Type*} {V : ι → Type*} [∀ i, AddCommGroup (V i)] [∀ i, Module R (V i)]

/-- Evaluate a finite tensor of scalar-valued functions on the product of the domains. -/
def functionTensorEvaluation (e : ∀ i, V i →ₗ[R] (X i → R)) :
    (⨂[R] i, V i) →ₗ[R] ((∀ i, X i) → R) :=
  PiTensorProduct.lift (MultilinearMap.pi fun x =>
    (MultilinearMap.mkPiAlgebra R ι R).compLinearMap fun i =>
      (LinearMap.proj (x i)).comp (e i))

@[simp]
theorem functionTensorEvaluation_tprod (e : ∀ i, V i →ₗ[R] (X i → R))
    (v : ∀ i, V i) (x : ∀ i, X i) :
    functionTensorEvaluation e (PiTensorProduct.tprod R v) x = ∏ i, e i (v i) (x i) := by
  rw [functionTensorEvaluation, PiTensorProduct.lift.tprod]
  rfl

theorem functionTensorEvaluation_map (e : ∀ i, V i →ₗ[R] (X i → R))
    {W : ι → Type*} [∀ i, AddCommGroup (W i)] [∀ i, Module R (W i)]
    (a : ∀ i, W i →ₗ[R] V i) (t : ⨂[R] i, W i) :
    functionTensorEvaluation e (PiTensorProduct.map a t) =
      functionTensorEvaluation (fun i => (e i).comp (a i)) t := by
  change (functionTensorEvaluation e ∘ₗ PiTensorProduct.map a) t = _
  congr 1
  apply PiTensorProduct.ext
  ext v x
  simp

private theorem exists_finiteSampling {R V X : Type*} [Field R] [AddCommGroup V]
    [Module R V] [FiniteDimensional R V] (e : V →ₗ[R] (X → R))
    (he : Function.Injective e) :
    ∃ (s : Set X) (_ : Fintype s) (a : V ≃ₗ[R] (s → R)),
      ∀ v j, a v j = e v j.val := by
  classical
  let evaluation (x : X) : Module.Dual R V := (LinearMap.proj x).comp e
  let P := Submodule.span R (Set.range evaluation)
  have hP : P = ⊤ := by
    have hbot : P.dualAnnihilator = ⊥ := by
      refine le_antisymm (fun φ hφ => ?_) bot_le
      obtain ⟨v, rfl⟩ := (Module.evalEquiv R V).surjective φ
      have hz := (Submodule.mem_dualAnnihilator _).mp hφ
      have hv : e v = 0 := funext fun x => hz (evaluation x) (Submodule.subset_span ⟨x, rfl⟩)
      rw [he (hv.trans e.map_zero.symm), map_zero]
      exact Submodule.zero_mem _
    rw [← Subspace.dualAnnihilator_dualCoannihilator_eq (W := P), hbot]
    ext
    simp
  obtain ⟨κ, points, hpoints, hspan, hli⟩ := exists_linearIndependent' R evaluation
  let s := Set.range points
  let a : κ ≃ s := Equiv.ofInjective points hpoints
  let b : Module.Basis κ R (Module.Dual R V) :=
    Module.Basis.mk hli (show ⊤ ≤ Submodule.span R (Set.range (evaluation ∘ points)) by
      rw [hspan, show Submodule.span R (Set.range evaluation) = ⊤ from hP])
  have : Finite κ := Module.Finite.finite_basis b
  have : Finite s := Finite.of_equiv κ a
  let c := b.reindex a
  refine ⟨s, Fintype.ofFinite s, (Module.evalEquiv R V).trans c.dualBasis.equivFun, ?_⟩
  intro v j
  rw [LinearEquiv.trans_apply, Module.Basis.dualBasis_equivFun,
    Module.evalEquiv_apply, Module.Dual.eval_apply]
  obtain ⟨k, rfl⟩ := a.surjective j
  simp only [c, Module.Basis.reindex_apply, Equiv.symm_apply_apply, b, Module.Basis.mk_apply]
  rfl

variable {J : ι → Type*}

private def gridEquiv [∀ i, Fintype (J i)] (b : ∀ i, V i ≃ₗ[R] (J i → R)) :
    (⨂[R] i, V i) ≃ₗ[R] ((∀ i, J i) → R) := by
  classical
  exact (PiTensorProduct.congr fun i =>
    (b i).trans (Finsupp.linearEquivFunOnFinite R R (J i)).symm).trans
      (PiTensorProduct.ofFinsuppEquiv'.trans (Finsupp.linearEquivFunOnFinite R R (∀ i, J i)))

private theorem gridEquiv_apply [∀ i, Fintype (J i)] (e : ∀ i, V i →ₗ[R] (X i → R))
    (a : ∀ i, J i → X i) (b : ∀ i, V i ≃ₗ[R] (J i → R))
    (hb : ∀ i v j, b i v j = e i v (a i j))
    (t : ⨂[R] i, V i) (j : ∀ i, J i) :
    gridEquiv b t j = functionTensorEvaluation e t (fun i => a i (j i)) := by
  induction t using PiTensorProduct.induction_on with
  | smul_tprod c v =>
    classical
    simp only [map_smul, Pi.smul_apply, functionTensorEvaluation_tprod, gridEquiv,
      LinearEquiv.trans_apply, PiTensorProduct.congr_tprod, Finsupp.linearEquivFunOnFinite_apply,
      PiTensorProduct.ofFinsuppEquiv'_apply_apply, Finsupp.linearEquivFunOnFinite_symm_apply, hb]
  | add t u ht hu => simp only [map_add, Pi.add_apply, ht, hu]

private theorem functionTensorEvaluation_slice [DecidableEq ι]
    (e : ∀ i, V i →ₗ[R] (X i → R)) (t : ⨂[R] i, V i) (i : ι) (x : ∀ j, X j) :
    ∃ v : V i, e i v = fun y => functionTensorEvaluation e t (Function.update x i y) := by
  induction t using PiTensorProduct.induction_on with
  | smul_tprod c v =>
    let d := ∏ j ∈ Finset.univ.erase i, e j (v j) (x j)
    refine ⟨(c * d) • v i, funext fun y => ?_⟩
    have hprod :
        (∏ j, e j (v j) (Function.update x i y j)) = d * e i (v i) y := by
      rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ i), Function.update_self]
      congr 1
      exact Finset.prod_congr rfl fun j hj => by
        rw [Function.update_of_ne (Finset.mem_erase.mp hj).1]
    simp [hprod, smul_eq_mul, mul_assoc]
  | add t u ht hu =>
    obtain ⟨v, hv⟩ := ht
    obtain ⟨w, hw⟩ := hu
    exact ⟨v + w, by ext y; simp [hv, hw]⟩

private theorem eq_zero_of_grid [DecidableEq ι] (e : ∀ i, V i →ₗ[R] (X i → R))
    (a : ∀ i, J i → X i) (b : ∀ i, V i ≃ₗ[R] (J i → R))
    (hb : ∀ i v j, b i v j = e i v (a i j))
    (f : (∀ i, X i) → R)
    (hs : ∀ i x, ∃ v : V i, e i v = fun y => f (Function.update x i y))
    (hz : ∀ j : ∀ i, J i, f (fun i => a i (j i)) = 0) :
    f = 0 := by
  classical
  have hvanishes (s : Finset ι) (x : ∀ i, X i)
      (hx : ∀ i ∉ s, x i ∈ Set.range (a i)) : f x = 0 := by
    induction s using Finset.induction_on generalizing x with
    | empty =>
      choose j hj using fun i => hx i (Finset.notMem_empty i)
      rw [show x = (fun i => a i (j i)) from funext fun i => (hj i).symm]
      exact hz j
    | insert i s hi ih =>
      obtain ⟨v, hv⟩ := hs i x
      have hv0 : b i v = 0 := by
        funext j
        rw [hb, hv]
        apply ih
        intro k hk
        by_cases hki : k = i
        · subst k
          rw [Function.update_self]
          exact Set.mem_range_self j
        · rw [Function.update_of_ne hki]
          exact hx k (by simp [hki, hk])
      have he0 : v = 0 := (b i).injective (hv0.trans (b i).map_zero.symm)
      simpa [he0] using (congrFun hv (x i)).symm
  funext x
  exact hvanishes Finset.univ x (by simp)

private theorem exists_tensor_of_finiteFactors [DecidableEq ι]
    [∀ i, FiniteDimensional R (V i)] (e : ∀ i, V i →ₗ[R] (X i → R))
    (he : ∀ i, Function.Injective (e i)) (f : (∀ i, X i) → R)
    (hs : ∀ i x, ∃ v : V i, e i v = fun y => f (Function.update x i y)) :
    ∃ t, functionTensorEvaluation e t = f := by
  choose s fin b hb using fun i => exists_finiteSampling (e i) (he i)
  let : ∀ i, Fintype (s i) := fin
  let a (i : ι) (j : s i) : X i := j.val
  obtain ⟨t, ht⟩ := (gridEquiv b).surjective (fun j => f (fun i => a i (j i)))
  refine ⟨t, sub_eq_zero.mp (eq_zero_of_grid e a b hb _ ?_ ?_)⟩
  · intro i x
    obtain ⟨v, hv⟩ := functionTensorEvaluation_slice e t i x
    obtain ⟨w, hw⟩ := hs i x
    exact ⟨v - w, by ext y; simp [hv, hw]⟩
  · intro j
    rw [Pi.sub_apply, ← gridEquiv_apply e a b hb, ht, sub_self]

omit [Fintype ι] in
private theorem exists_finiteFactors (t : ⨂[R] i, V i) :
    ∃ (P : ∀ i, Submodule R (V i)), (∀ i, FiniteDimensional R (P i)) ∧
      ∃ u, PiTensorProduct.mapIncl P u = t := by
  induction t using PiTensorProduct.induction_on with
  | smul_tprod c v =>
    let P (i : ι) : Submodule R (V i) := Submodule.span R {v i}
    let w (i : ι) : P i := ⟨v i, Submodule.subset_span (Set.mem_singleton _)⟩
    exact ⟨P, fun i => inferInstanceAs (FiniteDimensional R (Submodule.span R {v i})),
      c • PiTensorProduct.tprod R w, by simp [PiTensorProduct.mapIncl, w]⟩
  | add t u ht hu =>
    obtain ⟨P, hP, t', ht'⟩ := ht
    obtain ⟨Q, hQ, u', hu'⟩ := hu
    have : ∀ i, FiniteDimensional R (P i) := hP
    have : ∀ i, FiniteDimensional R (Q i) := hQ
    let S (i : ι) := P i ⊔ Q i
    let l (i : ι) : P i →ₗ[R] S i := Submodule.inclusion le_sup_left
    let r (i : ι) : Q i →ₗ[R] S i := Submodule.inclusion le_sup_right
    refine ⟨S, fun i => inferInstanceAs (FiniteDimensional R ↥(P i ⊔ Q i)),
      PiTensorProduct.map l t' + PiTensorProduct.map r u', ?_⟩
    rw [map_add, ← LinearMap.comp_apply, PiTensorProduct.mapIncl, ← PiTensorProduct.map_comp,
      ← LinearMap.comp_apply, ← PiTensorProduct.map_comp]
    exact congrArg₂ (· + ·) ht' hu'

/-- An injective function realization of each factor induces an injective function
realization of the tensor product. -/
theorem functionTensorEvaluation_injective (e : ∀ i, V i →ₗ[R] (X i → R))
    (he : ∀ i, Function.Injective (e i)) :
    Function.Injective (functionTensorEvaluation e) := by
  rw [injective_iff_map_eq_zero (functionTensorEvaluation e)]
  intro t ht
  obtain ⟨P, hP, u, rfl⟩ := exists_finiteFactors t
  have : ∀ i, FiniteDimensional R (P i) := hP
  let e' (i : ι) := (e i).comp (P i).subtype
  choose s fin b hb using
    fun i => exists_finiteSampling (e' i) ((he i).comp Subtype.val_injective)
  let : ∀ i, Fintype (s i) := fin
  have hu : functionTensorEvaluation e' u = 0 :=
    (functionTensorEvaluation_map e (fun i => (P i).subtype) u).symm.trans ht
  have hgrid : gridEquiv b u = 0 := by
    funext j
    exact (gridEquiv_apply e' (fun _ k => k.val) b hb u j).trans (congrFun hu _)
  rw [(gridEquiv b).injective (hgrid.trans (gridEquiv b).map_zero.symm), map_zero]

/-- A function whose slices in each coordinate all lie in one finite-dimensional
coefficient subspace is represented by a tensor of vectors in those subspaces. -/
theorem exists_tensor_of_finiteDimensional_slices [DecidableEq ι]
    (e : ∀ i, V i →ₗ[R] (X i → R)) (he : ∀ i, Function.Injective (e i))
    (P : ∀ i, Submodule R (V i)) [∀ i, FiniteDimensional R (P i)]
    (f : (∀ i, X i) → R)
    (hs : ∀ i x, ∃ v : P i, e i v.val = fun y => f (Function.update x i y)) :
    ∃ t : ⨂[R] i, P i, functionTensorEvaluation e (PiTensorProduct.mapIncl P t) = f := by
  obtain ⟨t, ht⟩ := exists_tensor_of_finiteFactors
    (fun i => (e i).comp (P i).subtype) (fun i => (he i).comp Subtype.val_injective) f hs
  exact ⟨t, (functionTensorEvaluation_map e (fun i => (P i).subtype) t).trans ht⟩

end Langlands
