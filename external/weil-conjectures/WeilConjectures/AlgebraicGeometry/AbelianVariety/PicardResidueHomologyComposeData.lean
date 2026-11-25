/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.Algebra.Group.Equiv.Basic

/-! # Composition of affine and geometric residue comparisons

Source: elementary additive-equivalence composition.
(blueprint: lem-sc-picard-residue-homology-chosen-geometric-maps)

The theorem is the final algebraic glue after the affine and geometric comparison
statements have been supplied separately. -/

@[expose] public section
set_option autoImplicit false
universe u v

/-- Compose an affine residue comparison with a derived-fibre comparison. -/
theorem picard_residue_homology_compose_data
    {I : Type u} {Ksrc A C : Type v} {Tgt B D : I → Type v}
    [AddCommGroup A] [AddCommGroup C] [AddCommGroup Ksrc]
    [∀ i, AddCommGroup (Tgt i)] [∀ i, AddCommGroup (B i)]
    [∀ i, AddCommGroup (D i)]
    (eK : Ksrc ≃+ A) (eC : ∀ i, Tgt i ≃+ B i)
    (map : ∀ i, Ksrc → Tgt i) (e : A ≃+ C) (ei : ∀ i, B i ≃+ D i)
    (F : ∀ i, A → B i) (G : ∀ i, C → D i)
    (hdata : ∀ i z, eC i (map i z) = F i (eK z))
    (hgeom : ∀ i z, ei i (F i z) = G i (e z)) :
    ∀ i z, (eC i).trans (ei i) (map i z) = G i ((eK.trans e) z) := by
  intro i z
  change ei i (eC i (map i z)) = _
  rw [hdata i z]
  simpa using hgeom i (eK z)

end
