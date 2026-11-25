/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Condensed.CondensedConstantConstructibilitySupplement
public import WeilConjectures.AlgebraicGeometry.ConstantModelExtContinuity
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Basic
public import Mathlib.CategoryTheory.ObjectProperty.Ind

/-! Ind-constructible Ext vanishing from an unrestricted continuity theorem.

Source: blueprint `corollary-ind-heart-b`, vanishing clause.
(blueprint: lem-finite-window-ind-ext-bound-continuity-vanishing)
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

/-- A continuity theorem for constructible sources extends any uniform constructible
Ext bound to ind-constructible targets.

Source: blueprint `corollary-ind-heart-b`, vanishing clause.
(blueprint: lem-finite-window-ind-ext-bound-continuity-vanishing).
Proof: use the filtered presentation supplied by `ObjectProperty.ind`, apply the
factorization property to each derived morphism, and transport the stagewise zero
bound through `Abelian.Ext.homEquiv`. -/
theorem constructibleInd_extBound_of_continuity
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    (X : Scheme.{u})
    (C : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
    (_hC : IsConstantModelConstructible Λ X C)
    (hcont : ConstantModelExtContinuity Λ X)
    (d : ℕ)
    (hbound : ∀ N : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
        (condensedRingObj Λ X),
      IsConstantModelConstructible Λ X N → ∀ r : ℕ, d < r →
        Subsingleton (@Abelian.Ext _ _ _ (HasExt.standard _) C N r))
    (B : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
    (hB : ObjectProperty.ind.{u + 1} (IsConstantModelConstructible Λ X) B)
    (r : ℕ) (hr : d < r) :
    Subsingleton (@Abelian.Ext _ _ _ (HasExt.standard _) C B r) := by
  let A := Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)
  let : HasExt.{u + 2} A := HasExt.standard A
  obtain ⟨I, _, _, pres, hpres⟩ := hB
  have hz (f : Abelian.Ext C B r) : f = 0 := by
    let f' := Abelian.Ext.homEquiv f
    obtain ⟨i, g, hg⟩ := hcont C _hC I pres.diag (Cocone.mk B pres.ι)
      pres.isColimit (r : ℤ) f'
    have hg0 : g = 0 := by
      have hs : Subsingleton (Abelian.Ext.{u + 2} C (pres.diag.obj i) r) :=
        hbound (pres.diag.obj i) (hpres i) r hr
      have heq : Abelian.Ext.homEquiv.symm g = 0 := Subsingleton.elim _ _
      calc
        g = Abelian.Ext.homEquiv (Abelian.Ext.homEquiv.symm g) :=
          (Abelian.Ext.homEquiv.apply_symm_apply g).symm
        _ = Abelian.Ext.homEquiv 0 := congrArg Abelian.Ext.homEquiv heq
        _ = 0 := by simp
    have hf' : f' = 0 := by
      rw [hg, hg0, zero_comp]
    apply Abelian.Ext.homEquiv.injective
    simpa [f'] using hf'
  exact ⟨fun f g ↦ (hz f).trans (hz g).symm⟩

end AlgebraicGeometry.ProEtale
