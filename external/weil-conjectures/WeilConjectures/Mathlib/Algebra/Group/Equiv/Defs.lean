/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Group.Equiv.Defs
public import Mathlib.Algebra.Group.Hom.Defs

/-!
# Additive equivalences of abelian groups

Variants of `AddEquiv.ofBijective` and of `e.symm ∘ g` stated for morphisms `A →+ B` of abelian
groups. Unlike `AddEquiv.ofBijective` used at a concrete type, the `Add` instances of the
equivalence and of the morphism are compared generically, not by unfolding the group structures,
which keeps the kernel cost low when `A` and `B` are `Ext`-groups.

## Main definitions

- `AddEquiv.ofBijectiveAddMonoidHom`: a bijective morphism of abelian groups, as an additive
  equivalence.
- `AddEquiv.symmComp`: the composite `e⁻¹ ∘ g` of a morphism with the inverse of an equivalence.
-/

@[expose] public section

namespace AddEquiv

variable {A B C : Type*} [AddCommGroup A] [AddCommGroup B] [AddCommGroup C]

/-- A bijective morphism of abelian groups, as an additive equivalence. -/
noncomputable def ofBijectiveAddMonoidHom (f : A →+ B) (hf : Function.Bijective f) : A ≃+ B :=
  AddEquiv.ofBijective f hf

/-- The composite `e⁻¹ ∘ g`, as a morphism of abelian groups. -/
def symmComp (e : B ≃+ C) (g : A →+ C) : A →+ B :=
  e.symm.toAddMonoidHom.comp g

lemma apply_symmComp (e : B ≃+ C) (g : A →+ C) (x : A) : e (e.symmComp g x) = g x :=
  e.apply_symm_apply _

end AddEquiv
