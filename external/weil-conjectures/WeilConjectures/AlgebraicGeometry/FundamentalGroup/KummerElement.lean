/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.FundamentalGroup.ExtendOverInertia
public import WeilConjectures.AlgebraicGeometry.FundamentalGroup.Torsor
public import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots

/-!
# Kummer elements of `ℤ / N`-torsors at geometric points

Let `T` be a `ℤ / N`-torsor over a scheme `Y`, `t : Spec Ω ⟶ T` a point with values in a field
and `ζ ∈ Ω` a primitive `N`-th root of unity. There is a nonzero `x ∈ Ω`
on which every automorphism `σ` of `Ω` fixing `ζ` with `Spec σ ≫ t = t ≫ (m +ᵥ ·)` acts as
multiplication by `ζ ^ m` (`AlgebraicGeometry.Scheme.EtaleTorsor.exists_kummer_element`).

Over an affine open `V` of `T` containing the image of `t` and stable under `ℤ / N`, the points
`t ≫ (i +ᵥ ·)` are ring maps `ψᵢ : Γ(T, V) → Ω`, and `x = ∑ᵢ ζ⁻ⁱ ψᵢ(b)`; it is nonzero for a
suitable `b` because the `ψᵢ` are distinct, hence linearly independent (Artin). This is the
Kummer theory of `ℤ / N`-torsors: `x ^ N` is fixed by every such `σ`, and `x` is an `N`-th root
whose Kummer character is the monodromy of the torsor at the point.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme.EtaleTorsor

variable {N : ℕ} [NeZero N] {Y : Scheme.{u}} (T : EtaleTorsor (ULift.{u + 1} (ZMod N)) Y)
  {Ω : Type u} [Field Ω]

/-- **Kummer elements.** For a point `t : Spec Ω ⟶ T` of a `ℤ / N`-torsor and a primitive
`N`-th root of unity `ζ ∈ Ω`, there is `x ≠ 0` in `Ω` such that every automorphism `σ` of `Ω`
fixing `ζ` and acting on `t` as `m ∈ ℤ / N`, i.e. `Spec σ ≫ t = t ≫ (m +ᵥ ·)`, multiplies `x`
by `ζ ^ m`. -/
theorem exists_kummer_element (t : Spec (.of Ω) ⟶ T.P) {ζ : Ω} (hζ : IsPrimitiveRoot ζ N) :
    ∃ x : Ω, x ≠ 0 ∧ ∀ (σ : Ω ≃+* Ω) (m : ZMod N), σ ζ = ζ →
      Spec.map (CommRingCat.ofHom (σ : Ω →+* Ω)) ≫ t = t ≫ T.vadd ⟨m⟩ →
        σ x = ζ ^ m.val * x := by
  classical
  have := T.isFinite
  -- an affine open of `T` containing the image of `t`, stable under `ℤ / N`
  obtain ⟨_, ⟨V', hV', rfl⟩, hyV', -⟩ := Y.isBasis_affineOpens.exists_subset_of_mem_open
    (Set.mem_univ ((t ≫ T.π) (default : Spec (.of Ω)))) isOpen_univ
  have hV : IsAffineOpen (T.π ⁻¹ᵁ V') := hV'.preimage T.π
  have hrange (i : ZMod N) : Set.range (t ≫ T.vadd ⟨i⟩).base ⊆ T.π ⁻¹ᵁ V' := by
    rintro _ ⟨p, rfl⟩
    change (t ≫ T.vadd ⟨i⟩ ≫ T.π) p ∈ V'
    rw [T.vadd_π, Subsingleton.elim p default]
    exact hyV'
  choose ψ hψ using fun i : ZMod N ↦ hV.exists_specMap_comp_fromSpec _ (hrange i)
  have hψinj : Function.Injective ψ := fun i j hij ↦
    congrArg ULift.down (T.eq_of_comp_vadd_eq t ((hψ i).symm.trans (hij ▸ hψ j)) default)
  -- the `ψ i` are distinct, hence linearly independent
  let f : ZMod N → (Γ(T.P, T.π ⁻¹ᵁ V') →* Ω) := fun i ↦ (ψ i).hom.toMonoidHom
  have hfinj : Function.Injective f := fun i j hij ↦ hψinj (CommRingCat.hom_ext
    (RingHom.ext fun b ↦ DFunLike.congr_fun hij b))
  have hli : LinearIndependent Ω (fun i ↦ (f i : Γ(T.P, T.π ⁻¹ᵁ V') → Ω)) :=
    (linearIndependent_monoidHom Γ(T.P, T.π ⁻¹ᵁ V') Ω).comp f hfinj
  have hζ0 : ζ ≠ 0 := hζ.ne_zero (NeZero.ne N)
  let c : ZMod N → Ω := fun i ↦ (ζ ^ i.val)⁻¹
  obtain ⟨b, hb⟩ : ∃ b, ∑ i, c i * ψ i b ≠ 0 := by
    by_contra! h
    have h0 := Fintype.linearIndependent_iff.mp hli c (funext fun b ↦ by
      simpa [f, Finset.sum_apply] using h b) 0
    simp [c] at h0
  refine ⟨∑ i, c i * ψ i b, hb, fun σ m hσζ hσ ↦ ?_⟩
  -- `σ` permutes the `ψ i`
  have hσψ (i : ZMod N) : σ (ψ i b) = ψ (m + i) b := by
    have : ψ i ≫ CommRingCat.ofHom (σ : Ω →+* Ω) = ψ (m + i) := by
      apply Spec.map_injective
      rw [← cancel_mono hV.fromSpec, Spec.map_comp, Category.assoc, hψ, hψ, ← Category.assoc,
        hσ, Category.assoc, ← T.add_vadd]
      rfl
    exact congrArg (fun φ : Γ(T.P, T.π ⁻¹ᵁ V') ⟶ CommRingCat.of Ω ↦ φ b) this
  have hc (i : ZMod N) : c (i - m) = ζ ^ m.val * c i := by
    have h : ζ ^ i.val = ζ ^ (i - m).val * ζ ^ m.val := by
      rw [← pow_add, ← pow_mod_orderOf ζ ((i - m).val + m.val), ← hζ.eq_orderOf, ← ZMod.val_add,
        sub_add_cancel]
    simp only [c]
    rw [h]
    field_simp
  have hσc (i : ZMod N) : σ (c i) = c i := by simp only [c, map_inv₀, map_pow, hσζ]
  rw [map_sum]
  simp only [map_mul, hσc, hσψ]
  rw [Finset.mul_sum]
  refine Fintype.sum_equiv (Equiv.addLeft m) _ _ fun i ↦ ?_
  simp only [Equiv.coe_addLeft]
  rw [← mul_assoc, ← hc, add_sub_cancel_left]

end AlgebraicGeometry.Scheme.EtaleTorsor
