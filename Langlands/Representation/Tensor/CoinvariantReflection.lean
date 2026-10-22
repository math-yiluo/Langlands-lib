import Langlands.Representation.Tensor.FiniteProperties

/-! Coinvariant vanishing reflected from a single active tensor factor. -/

noncomputable section

open scoped TensorProduct
open Function Module

namespace Langlands.FiniteTensor

universe uk uI uG uV

variable {k : Type uk} [Field k]
variable {ι : Type uI} [Fintype ι] [DecidableEq ι]
variable {V : ι → Type uV} [∀ i, AddCommGroup (V i)] [∀ i, Module k (V i)]
variable {H : ι → Type uG} [∀ i, Group (H i)]

/-- If a product subgroup is trivial away from one slot, nonzero other factors
allow coinvariant vanishing of the external tensor to be reflected to that slot. -/
theorem coinvariants_factor_subsingleton (ρ : ∀ i, Representation k (H i) (V i))
    (N : ∀ i, Subgroup (H i)) (j : ι)
    (hN : ∀ i, i ≠ j → N i = ⊥)
    (hne : ∀ i, i ≠ j → Nontrivial (V i))
    (hz : Subsingleton (Jacquet.Coinvariants (external ρ) (Subgroup.pi Set.univ N))) :
    Subsingleton (Jacquet.Coinvariants (ρ j) (N j)) := by
  classical
  let J := ({j}ᶜ : Set ι)
  let X := ⨂[k] i : J, V i
  let b := fun i : J => Basis.ofVectorSpace k (V i)
  have hb : ∀ i : J, Nonempty (Basis.ofVectorSpaceIndex k (V i)) := by
    intro i
    let := hne i i.property
    exact (b i).index_nonempty
  let a := fun i : J => Classical.choice (hb i)
  let c := Basis.piTensorProduct b
  let e := PiTensorProduct.equivPiTensorComplSingletonTensor k V j
  let Q := Jacquet.Coinvariants (ρ j) (N j)
  let q : X ⊗[k] V j →ₗ[k] Q :=
    (TensorProduct.lid k Q).toLinearMap ∘ₗ
      TensorProduct.map (c.coord a) (Jacquet.mk (ρ j) (N j))
  have hq : ∀ (x : X) (v : V j), q (x ⊗ₜ[k] v) =
      c.coord a x • Jacquet.mk (ρ j) (N j) v := by
    intro x v
    simp [q]
  let f : (⨂[k] i, V i) →ₗ[k] Q := q ∘ₗ e.toLinearMap
  have hf : ∀ g : Subgroup.pi Set.univ N, f ∘ₗ external ρ g = f := by
    intro g
    have hg : (g : ∀ i, H i) = Pi.mulSingle j (g.val j) := by
      funext i
      by_cases hi : i = j
      · subst i
        simp
      · have hgi : g.val i ∈ N i := g.property i (Set.mem_univ i)
        rw [hN i hi, Subgroup.mem_bot] at hgi
        simp [hi, hgi]
    have hj : g.val j ∈ N j := g.property j (Set.mem_univ j)
    apply LinearMap.ext
    intro z
    change q (e (external ρ g z)) = q (e z)
    rw [hg, external_mulSingle, split_map_slot]
    generalize e z = y
    induction y with
    | tmul x v =>
      rw [LinearMap.lTensor_tmul, hq, hq]
      congr 1
      exact Jacquet.mk_apply_subgroup (ρ j) (N j) ⟨_, hj⟩ v
    | add y y' hy hy' => simp only [map_add, hy, hy']
  let l := Jacquet.lift (external ρ) (Subgroup.pi Set.univ N) f hf
  have hfzero : ∀ z, f z = 0 := by
    intro z
    change l (Jacquet.mk (external ρ) (Subgroup.pi Set.univ N) z) = 0
    rw [Subsingleton.elim (Jacquet.mk (external ρ) (Subgroup.pi Set.univ N) z) 0,
      map_zero]
  rw [subsingleton_coinvariants_iff]
  intro v
  rw [← Jacquet.mk_eq_zero]
  have h := hfzero (e.symm (c a ⊗ₜ[k] v))
  change q (e (e.symm (c a ⊗ₜ[k] v))) = 0 at h
  rw [e.apply_symm_apply, hq] at h
  simpa only [Basis.coord_apply, Basis.repr_self, Finsupp.single_eq_same, one_smul] using h

end Langlands.FiniteTensor
