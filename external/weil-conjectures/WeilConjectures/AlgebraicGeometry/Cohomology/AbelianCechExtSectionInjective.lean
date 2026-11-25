/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Cohomology.AbelianCechComparisonConstruction
import Mathlib.CategoryTheory.Adjunction.Additive
import Mathlib.Algebra.Homology.ShortComplex.ConcreteCategory

/-! # Section homology detects equality of Ext cocycles

Source: Stacks Project, Tags 01EQ and 01FD.
(blueprint: lem-pc-ext-section-injective)
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
namespace AlgebraicGeometry.Scheme.Modules
attribute [local instance] cohomologyHasSheafify cohomologyHasExt

/-- Equality of section homology classes implies equality of the corresponding
Ext classes. Source: Stacks Project, Tag 01EQ, computation of cohomology on an
injective resolution; Mathlib `extMk_eq_zero_iff` and the constant-sheaf
adjunction. (blueprint: lem-pc-ext-section-injective)

Proof: Subtract the two cocycles and their section cycles. In positive degree,
equality of section homology classes makes the difference a section boundary.
Choose a section preimage of this boundary. The constant-sheaf adjunction,
evaluated on the generator of the lifted integers, turns that section into a
morphism to the preceding resolution term. Naturality of the adjunction and
the cycle inclusions identify its differential with a minus b. Apply
extMk_eq_zero_iff and sub_extMk to conclude equality of Ext classes. In degree
zero there are no incoming boundaries, so the cycle inclusion is injective
and equality of homology gives equality of sections; the adjunction then
gives a = b. This also covers the zero sheaf and the empty space. -/
theorem abelianCech_ext_section_injective
    {X : Scheme.{u}} {F : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}}
    (I : InjectiveResolution F) (q : ℕ)
    (a b : (constantSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj
      (AddCommGrpCat.of (ULift.{u} ℤ)) ⟶ I.cocomplex.X q)
    (ha : a ≫ I.cocomplex.d q (q + 1) = 0)
    (hb : b ≫ I.cocomplex.d q (q + 1) = 0)
    (z w : (abelianCechSections I).cycles q)
    (hz : ((constantSheafAdj (Opens.grothendieckTopology X) AddCommGrpCat.{u}
      isTerminalTop).homEquiv _ _ a) (ULift.up 1) =
        (abelianCechSections I).iCycles q z)
    (hw : ((constantSheafAdj (Opens.grothendieckTopology X) AddCommGrpCat.{u}
      isTerminalTop).homEquiv _ _ b) (ULift.up 1) =
        (abelianCechSections I).iCycles q w)
    (h : (abelianCechSections I).homologyπ q z =
      (abelianCechSections I).homologyπ q w) :
    I.extMk a (q + 1) rfl ha = I.extMk b (q + 1) rfl hb := by
  let K := abelianCechSections I
  let adj := constantSheafAdj (Opens.grothendieckTopology X) AddCommGrpCat.{u}
    isTerminalTop
  let e (n : ℕ) :
      ((constantSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj
        (AddCommGrpCat.of (ULift.{u} ℤ)) ⟶ I.cocomplex.X n) ≃+ K.X n :=
    (adj.homAddEquiv _ _).trans (AddCommGrpCat.uliftZMultiplesAddEquiv _)
  have enat (p n : ℕ)
      (g : (constantSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj
        (AddCommGrpCat.of (ULift.{u} ℤ)) ⟶ I.cocomplex.X p) :
      e n (g ≫ I.cocomplex.d p n) = K.d p n (e p g) := by
    have ht := ConcreteCategory.congr_hom
      (adj.homEquiv_naturality_right g (I.cocomplex.d p n)) (ULift.up 1)
    simp only [ConcreteCategory.comp_apply] at ht
    exact ht
  change e q a = K.iCycles q z at hz
  change e q b = K.iCycles q w at hw
  cases q with
  | zero =>
      have : IsIso (K.homologyπ 0) := K.isIso_homologyπ 0 0 (by simp) (by simp)
      have hzw := (ConcreteCategory.bijective_of_isIso (K.homologyπ 0)).injective h
      have hab : a = b := (e 0).injective (hz.trans (hzw ▸ hw.symm))
      subst b
      rfl
  | succ n =>
      let T := ShortComplex.mk (K.toCycles n (n + 1)) (K.homologyπ (n + 1))
        (by simp)
      have hT : T.Exact :=
        T.exact_of_g_is_cokernel (K.homologyIsCokernel n (n + 1) (by simp))
      have hzero : K.homologyπ (n + 1) (z - w) = 0 := by
        rw [map_sub, h, sub_self]
      obtain ⟨t, ht⟩ := (ShortComplex.ab_exact_iff T).1 hT (z - w) hzero
      have ht' := congrArg (fun v ↦ K.iCycles (n + 1) v) ht
      change K.iCycles (n + 1) (K.toCycles n (n + 1) t) = _ at ht'
      rw [← ConcreteCategory.comp_apply, HomologicalComplex.toCycles_i, map_sub] at ht'
      have hboundary : (e n).symm t ≫ I.cocomplex.d n (n + 1) = a - b := by
        apply (e (n + 1)).injective
        rw [enat, AddEquiv.apply_symm_apply, map_sub, hz, hw]
        exact ht'
      rw [← sub_eq_zero, I.sub_extMk a b (n + 2) rfl ha hb]
      exact (I.extMk_eq_zero_iff _ (n + 2) rfl _ n rfl).2 ⟨(e n).symm t, hboundary⟩

end AlgebraicGeometry.Scheme.Modules
