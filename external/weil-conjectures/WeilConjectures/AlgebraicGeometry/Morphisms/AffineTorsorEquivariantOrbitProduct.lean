/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Morphisms.AffineTorsorEquivariantAlgebra
import Mathlib.Data.Fintype.Card

/-! # Orbit decomposition of equivariant functions

## References

* Stacks Project, Tag 03SF, classification by finite group sets
-/

@[expose] public section
universe u
set_option autoImplicit false
namespace AlgebraicGeometry.Scheme

/-- Evaluation at one representative of each orbit identifies equivariant functions
with a product of stabilizer fixed rings. -/
theorem affine_torsor_equivariant_orbit_product
    (H C : Type u) [CommRing H] [CommRing C] [Algebra H C]
    (G : Type u) [Group G] (ρ : G → C →ₐ[H] C)
    (_hρone : ρ 1 = AlgHom.id H C)
    (hρmul : ∀ a b, ρ (a * b) = (ρ a).comp (ρ b))
    (d : ℕ) (α : G →* Equiv.Perm (Fin d)) :
    ∃ (m : ℕ) (K : Fin m → Subgroup G), m ≤ d ∧
      Nonempty ((affineTorsorEquivariantAlgebra H C G ρ d α) ≃ₐ[H]
        (∀ k : Fin m,
          (⨅ ζ : K k, AlgHom.equalizer (ρ ζ.val) (AlgHom.id H C) : Subalgebra H C))) :=
  by
  classical
  let : MulAction G (Fin d) := MulAction.compHom (Fin d) α
  let Q := MulAction.orbitRel.Quotient G (Fin d)
  let : Fintype Q := Fintype.ofFinite Q
  let m := Fintype.card Q
  let e : Q ≃ Fin m := Fintype.equivFin Q
  let r : Fin m → Fin d := fun k ↦ (e.symm k).out
  let o : Fin d → Fin m := fun i ↦ e (Quotient.mk'' i)
  have hor (k : Fin m) : o (r k) = k := by
    simp [o, r]
  have ho (a : G) (i : Fin d) : o (α a i) = o i := by
    apply congrArg e
    exact MulAction.orbitRel.Quotient.quotient_smul_eq
  have hr (i : Fin d) : ∃ a : G, α a (r (o i)) = i := by
    have heq : (Quotient.mk'' i : Q) = Quotient.mk'' (r (o i)) := by
      simp [r, o]
    exact Quotient.exact heq
  choose t ht using hr
  let K : Fin m → Subgroup G := fun k ↦ MulAction.stabilizer G (r k)
  let A := affineTorsorEquivariantAlgebra H C G ρ d α
  let B := ∀ k : Fin m,
    (⨅ ζ : K k, AlgHom.equalizer (ρ ζ.val) (AlgHom.id H C) : Subalgebra H C)
  have hA (f : Fin d → C) : f ∈ A ↔ ∀ a i, ρ a (f i) = f (α a i) := by
    simp [A, affineTorsorEquivariantAlgebra, Algebra.mem_iInf]
  have hB (k : Fin m) (x : C) :
      x ∈ (⨅ ζ : K k, AlgHom.equalizer (ρ ζ.val) (AlgHom.id H C)) ↔
        ∀ a : G, α a (r k) = r k → ρ a x = x := by
    simp only [Algebra.mem_iInf, AlgHom.mem_equalizer, AlgHom.id_apply]
    constructor
    · intro h a ha
      exact h ⟨a, ha⟩
    · intro h a
      exact h a.val a.property
  let ev : A →ₐ[H] B :=
    AlgHom.pi fun k ↦
      { toFun := fun f ↦ ⟨f.val (r k), (hB k _).mpr fun a ha ↦ by
          rw [(hA f.val).mp f.property a (r k), ha]⟩
        map_one' := rfl
        map_mul' := fun _ _ ↦ rfl
        map_zero' := rfl
        map_add' := fun _ _ ↦ rfl
        commutes' := fun _ ↦ rfl }
  have htransport (b : B) (k : Fin m) (a a' : G)
      (heq : α a (r k) = α a' (r k)) : ρ a (b k).val = ρ a' (b k).val := by
    have hs : α (a'⁻¹ * a) (r k) = r k := by
      simp only [map_mul, map_inv, Equiv.Perm.mul_apply]
      rw [heq]
      exact (α a').symm_apply_apply _
    have hx := (hB k _).mp (b k).property (a'⁻¹ * a) hs
    have hx' := congrArg (ρ a') hx
    simpa only [← AlgHom.comp_apply, ← hρmul, mul_inv_cancel_left] using hx'
  have hsurj : Function.Surjective ev := by
    intro b
    let f : Fin d → C := fun i ↦ ρ (t i) (b (o i)).val
    have hf : f ∈ A := by
      apply (hA f).mpr
      intro a i
      change ρ a (ρ (t i) (b (o i)).val) = ρ (t (α a i)) (b (o (α a i))).val
      rw [ho, ← AlgHom.comp_apply, ← hρmul]
      apply htransport
      rw [map_mul, Equiv.Perm.mul_apply, ht, ← ho a i, ht]
    refine ⟨⟨f, hf⟩, ?_⟩
    apply funext
    intro k
    apply Subtype.ext
    change ρ (t (r k)) (b (o (r k))).val = (b k).val
    rw [hor]
    have hs : α (t (r k)) (r k) = r k := by simpa only [hor] using ht (r k)
    exact (hB k _).mp (b k).property _ hs
  have hinj : Function.Injective ev := by
    intro f f' heq
    apply Subtype.ext
    funext i
    have h := congrArg (fun b : B ↦ (b (o i)).val) heq
    change f.val (r (o i)) = f'.val (r (o i)) at h
    rw [← ht i, ← (hA f.val).mp f.property, ← (hA f'.val).mp f'.property, h]
  refine ⟨m, K, ?_, ⟨AlgEquiv.ofBijective ev ⟨hinj, hsurj⟩⟩⟩
  have hcard := Fintype.card_le_of_surjective
    (Quotient.mk'' : Fin d → Q) Quotient.mk''_surjective
  simpa only [Fintype.card_fin] using hcard

end AlgebraicGeometry.Scheme
