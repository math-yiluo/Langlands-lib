import Langlands.Representation.Exponents.WeylBranchPiecesSubquotient
import Langlands.Representation.Tensor.FiniteFiltration
import Mathlib.LinearAlgebra.TensorProduct.Finiteness
import Mathlib.LinearAlgebra.PiTensorProduct.Basis
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.Basis.VectorSpace

/-!
# Irreducible subquotients of external tensor products

An irreducible representation that is an actual subquotient of a tensor product
with a trivially acted factor is an actual subquotient of the other factor. For
finite external tensor products this shows that each factor of an irreducible
external tensor subquotient is a subquotient of the corresponding factor.
-/

noncomputable section

open scoped TensorProduct

namespace Langlands.FiniteTensor

open WeylBranchPieces

universe uG uM uW uX uI uV

section Slot

variable {G : Type uG} [Group G] {M : Type uM} {W : Type uW} {X : Type uX}
  [AddCommGroup M] [Module ℂ M] [AddCommGroup W] [Module ℂ W]
  [AddCommGroup X] [Module ℂ X]
  (τ : Representation ℂ G M) (hτ : ∀ g, τ g = 1) (J : Representation ℂ G W)

/-- Contraction of a trivially acted left tensor factor against a linear
functional. -/
def trivialContraction (φ : Module.Dual ℂ M) :
    (Representation.tprod τ J).IntertwiningMap J where
  toLinearMap := (TensorProduct.lid ℂ W).toLinearMap ∘ₗ φ.rTensor W
  isIntertwining' g := by
    apply TensorProduct.ext'
    intro m w
    simp [Representation.tprod_apply, hτ g]

theorem trivialContraction_tmul (φ : Module.Dual ℂ M) (m : M) (w : W) :
    trivialContraction τ hτ J φ (m ⊗ₜ w) = φ m • w := by
  simp [trivialContraction]

theorem trivialContraction_surjective (φ : Module.Dual ℂ M) {m : M} (hm : φ m = 1) :
    Function.Surjective (trivialContraction τ hτ J φ) := fun w =>
  ⟨m ⊗ₜ w, by rw [trivialContraction_tmul, hm, one_smul]⟩

/-- The tensors whose left factors lie in a given subspace. -/
def leftSlice (N : Submodule ℂ M) : Subrepresentation (Representation.tprod τ J) where
  toSubmodule := LinearMap.range (N.subtype.rTensor W)
  apply_mem_toSubmodule g := by
    rintro _ ⟨y, rfl⟩
    refine ⟨(J g).lTensor N y, ?_⟩
    induction y using TensorProduct.inductionOn with
    | tmul n w => simp [Representation.tprod_apply, hτ g]
    | add y z hy hz => rw [map_add, map_add, map_add, map_add, hy, hz]

/-- If the contraction against `φ` kills a tensor with left factors in `N`, and
`φ m = 1` for some `m ∈ N`, its left factors lie in `N ∩ ker φ`. -/
theorem mem_range_of_trivialContraction_eq_zero {N : Submodule ℂ M} {m : M} (hm : m ∈ N)
    {φ : Module.Dual ℂ M} (hφ : φ m = 1) (y : N ⊗[ℂ] W)
    (hy : trivialContraction τ hτ J φ (N.subtype.rTensor W y) = 0) :
    N.subtype.rTensor W y ∈
      LinearMap.range ((N ⊓ LinearMap.ker φ).subtype.rTensor W) := by
  let s : N →ₗ[ℂ] (N ⊓ LinearMap.ker φ : Submodule ℂ M) :=
    LinearMap.codRestrict (N ⊓ LinearMap.ker φ)
      (N.subtype - (φ ∘ₗ N.subtype).smulRight m) (fun n => by
        refine ⟨?_, ?_⟩
        · exact N.sub_mem n.property (N.smul_mem _ hm)
        · simp [hφ])
  have hs : ∀ n : N, ((s n : (N ⊓ LinearMap.ker φ : Submodule ℂ M)) : M) = n - φ n • m :=
    fun _ => rfl
  have key : N.subtype.rTensor W =
      (N ⊓ LinearMap.ker φ).subtype.rTensor W ∘ₗ s.rTensor W +
        (TensorProduct.mk ℂ M W m) ∘ₗ (trivialContraction τ hτ J φ).toLinearMap ∘ₗ
          N.subtype.rTensor W := by
    apply TensorProduct.ext'
    intro n w
    simp only [LinearMap.add_apply, LinearMap.comp_apply, LinearMap.rTensor_tmul,
      Submodule.subtype_apply, hs, TensorProduct.mk_apply]
    change _ = _ + m ⊗ₜ trivialContraction τ hτ J φ ((n : M) ⊗ₜ w)
    rw [trivialContraction_tmul, TensorProduct.sub_tmul, TensorProduct.tmul_smul,
      TensorProduct.smul_tmul']
    abel
  have key' := congrArg (fun F => F y) key
  simp only [LinearMap.add_apply, LinearMap.comp_apply] at key'
  change _ = _ + m ⊗ₜ trivialContraction τ hτ J φ (N.subtype.rTensor W y) at key'
  rw [key', hy, TensorProduct.tmul_zero, add_zero]
  exact ⟨_, rfl⟩

include hτ in
/-- An irreducible actual subquotient of the tensor product of a trivially acted
space with `J` is an actual subquotient of `J`. -/
theorem isSubquotient_of_tprod_trivial {Y : Representation ℂ G X} [Y.IsIrreducible]
    (h : IsSubquotient (Representation.tprod τ J) Y) : IsSubquotient J Y := by
  classical
  obtain ⟨U, f, hf⟩ := h
  have : Nontrivial X := IsSimpleModule.nontrivial (MonoidAlgebra ℂ G) Y.asModule
  obtain ⟨x₀, hx₀⟩ := exists_ne (0 : X)
  obtain ⟨u, hu⟩ := hf x₀
  let P : Submodule ℂ M → Prop := fun N =>
    ∃ x : U.toSubmodule, (x : M ⊗[ℂ] W) ∈ LinearMap.range (N.subtype.rTensor W) ∧ f x ≠ 0
  let Q : ℕ → Prop := fun d =>
    ∃ N : Submodule ℂ M, FiniteDimensional ℂ N ∧ Module.finrank ℂ N = d ∧ P N
  have hQ : ∃ d, Q d := by
    obtain ⟨N, hNfin, hN⟩ := TensorProduct.exists_finite_submodule_left_of_setFinite
      {(u : M ⊗[ℂ] W)} (Set.finite_singleton _)
    exact ⟨_, N, hNfin, rfl, u, hN rfl, hu ▸ hx₀⟩
  obtain ⟨N, hNfin, hNd, x, hxN, hfx⟩ := Nat.find_spec hQ
  have hNbot : N ≠ ⊥ := by
    rintro rfl
    apply hfx
    obtain ⟨y, hy⟩ := hxN
    have hsub : (⊥ : Submodule ℂ M).subtype = 0 := by
      ext v
      exact (Submodule.mem_bot ℂ).1 v.property
    have hx0 : x = 0 := by
      apply Subtype.ext
      rw [← hy, hsub, LinearMap.rTensor_zero]
      rfl
    rw [hx0, map_zero]
  obtain ⟨m, hmN, hm0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hNbot
  obtain ⟨φ, hφ⟩ := Module.Projective.exists_dual_eq_one ℂ hm0
  have hlt : N ⊓ LinearMap.ker φ < N := by
    refine lt_of_le_of_ne inf_le_left fun he => ?_
    have hm' : m ∈ N ⊓ LinearMap.ker φ := by rw [he]; exact hmN
    have h0 : φ m = 0 := hm'.2
    rw [hφ] at h0
    exact one_ne_zero h0
  have hvan : ∀ v : U.toSubmodule,
      (v : M ⊗[ℂ] W) ∈ LinearMap.range ((N ⊓ LinearMap.ker φ).subtype.rTensor W) →
        f v = 0 := by
    intro v hv
    by_contra hne
    have hfin' : FiniteDimensional ℂ (N ⊓ LinearMap.ker φ : Submodule ℂ M) :=
      Submodule.finiteDimensional_of_le inf_le_left
    have hlt' : Module.finrank ℂ (N ⊓ LinearMap.ker φ : Submodule ℂ M) < Nat.find hQ := by
      rw [← hNd]
      exact Submodule.finrank_lt_finrank_of_lt hlt
    exact Nat.find_min hQ hlt' ⟨_, hfin', rfl, v, hv, hne⟩
  let UN : Subrepresentation (Representation.tprod τ J) := U ⊓ leftSlice τ hτ J N
  let iU : UN.toRepresentation.IntertwiningMap U.toRepresentation :=
    { toLinearMap :=
        { toFun := fun v => ⟨v.val, v.property.1⟩
          map_add' := fun _ _ => rfl
          map_smul' := fun _ _ => rfl }
      isIntertwining' := fun _ => rfl }
  let c : UN.toRepresentation.IntertwiningMap J :=
    (trivialContraction τ hτ J φ).comp (subtypeMap UN)
  let R : Subrepresentation J := c.range
  let c' : UN.toRepresentation.IntertwiningMap R.toRepresentation :=
    { toLinearMap := c.toLinearMap.rangeRestrict
      isIntertwining' := by
        intro g
        ext v
        exact Representation.IntertwiningMap.isIntertwining _ _ c g v }
  have hc' : Function.Surjective c' := LinearMap.surjective_rangeRestrict _
  let fN := f.comp iU
  have hker : c'.toLinearMap.ker ≤ fN.toLinearMap.ker := by
    intro v hv
    have hv' : c v = 0 := by
      change v ∈ LinearMap.ker c.toLinearMap.rangeRestrict at hv
      rw [LinearMap.ker_rangeRestrict] at hv
      exact hv
    obtain ⟨y, hy⟩ := v.property.2
    have hmem := mem_range_of_trivialContraction_eq_zero τ hτ J hmN hφ y (by
      rw [hy]
      exact hv')
    rw [hy] at hmem
    exact hvan (iU v) hmem
  obtain ⟨d, hd⟩ := exists_descend c' fN hc' hker
  have hdsurj : Function.Surjective d := by
    refine (Representation.IsIrreducible.surjective_or_eq_zero d).resolve_right ?_
    intro h0
    apply hfx
    have hxUN : (x : M ⊗[ℂ] W) ∈ UN.toSubmodule := ⟨x.property, hxN⟩
    have h1 := hd ⟨x, hxUN⟩
    rw [h0] at h1
    exact h1.symm
  exact ⟨R, d, hdsurj⟩

end Slot

section External

variable {ι : Type uI} [Fintype ι] [DecidableEq ι] {H : ι → Type uG} [∀ i, Group (H i)]
  {V : ι → Type uV} [∀ i, AddCommGroup (V i)] [∀ i, Module ℂ (V i)]
  {W : ι → Type uW} [∀ i, AddCommGroup (W i)] [∀ i, Module ℂ (W i)]

/-- A finite indexed tensor product of nonzero complex vector spaces is nonzero. -/
theorem nontrivial_piTensorProduct {κ : Type*} [Finite κ] {E : κ → Type*}
    [∀ i, AddCommGroup (E i)] [∀ i, Module ℂ (E i)] (hE : ∀ i, Nontrivial (E i)) :
    Nontrivial (PiTensorProduct ℂ E) := by
  let b := fun i => Module.Basis.ofVectorSpace ℂ (E i)
  let q := fun i => Classical.choice (b i).index_nonempty
  exact ⟨⟨Basis.piTensorProduct b q, 0, (Basis.piTensorProduct b).ne_zero q⟩⟩

/-- The external action restricted to one coordinate, written as an action of
that coordinate group. -/
abbrev slotRestriction (ρ : ∀ i, Representation ℂ (H i) (V i)) (k : ι) (i : ι) :
    Representation ℂ (H k) (V i) :=
  (ρ i).comp ((Pi.evalMonoidHom H i).comp (MonoidHom.mulSingle H k))

omit [Fintype ι] in
theorem slotRestriction_self (ρ : ∀ i, Representation ℂ (H i) (V i)) (k : ι) :
    slotRestriction ρ k k = ρ k := by
  ext g v
  simp [slotRestriction]

omit [Fintype ι] in
/-- Off the chosen coordinate the restricted external action is trivial. -/
theorem action_slotRestriction_compl (ρ : ∀ i, Representation ℂ (H i) (V i)) (k : ι)
    (g : H k) :
    action (fun i : ({k}ᶜ : Set ι) => slotRestriction ρ k i) g = 1 := by
  have h : (fun i : ({k}ᶜ : Set ι) => slotRestriction ρ k i g) =
      fun i => LinearMap.id := by
    funext i
    have hi : (i : ι) ≠ k := i.property
    simp [slotRestriction, Pi.mulSingle_eq_of_ne hi, Module.End.one_eq_id]
  change PiTensorProduct.map (fun i : ({k}ᶜ : Set ι) => slotRestriction ρ k i g) = 1
  rw [h, PiTensorProduct.map_id, Module.End.one_eq_id]

/-- If an external tensor product of irreducible representations is an actual
subquotient of an external tensor product, each factor is an actual subquotient
of the corresponding factor. -/
theorem isSubquotient_factor_of_external (J : ∀ i, Representation ℂ (H i) (W i))
    (ρ : ∀ i, Representation ℂ (H i) (V i)) (hρ : ∀ i, (ρ i).IsIrreducible)
    (h : IsSubquotient (external J) (external ρ)) (k : ι) :
    IsSubquotient (J k) (ρ k) := by
  have h0 : IsSubquotient (action (slotRestriction J k)) (action (slotRestriction ρ k)) :=
    h.comp (MonoidHom.mulSingle H k)
  have h1 := IsSubquotient.of_equiv_left (slotEquiv (slotRestriction J k) k).symm
    (h0.of_equiv_right (slotEquiv (slotRestriction ρ k) k))
  have hV : Nontrivial (PiTensorProduct ℂ (fun i : ({k}ᶜ : Set ι) => V i)) :=
    nontrivial_piTensorProduct fun i => by
      have := hρ i
      exact IsSimpleModule.nontrivial (MonoidAlgebra ℂ (H i)) (ρ i).asModule
  obtain ⟨m, hm⟩ := exists_ne (0 : PiTensorProduct ℂ (fun i : ({k}ᶜ : Set ι) => V i))
  obtain ⟨φ, hφ⟩ := Module.Projective.exists_dual_eq_one ℂ hm
  have h2 := h1.trans (IsSubquotient.of_surjective
    (trivialContraction _ (action_slotRestriction_compl ρ k) _ φ)
    (trivialContraction_surjective _ (action_slotRestriction_compl ρ k) _ φ hφ))
  have hk : (slotRestriction ρ k k).IsIrreducible := by
    rw [slotRestriction_self]
    exact hρ k
  have h3 := isSubquotient_of_tprod_trivial _ (action_slotRestriction_compl J k) _ h2
  rwa [slotRestriction_self J k, slotRestriction_self ρ k] at h3

end External

end Langlands.FiniteTensor
