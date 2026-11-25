/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Homology.Embedding.CochainComplex
public import Mathlib.Algebra.Homology.Functor
public import Mathlib.CategoryTheory.Limits.Preserves.Finite

import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology

/-! # Underived lower truncation on cycle classes

Source: Stacks Project, Tag 05TC, and the kernel calculation underlying Tag 08D4 (1).
(blueprint: lem-sc-left-exact-truncation-cycle-formula).
-/

@[expose] public section

universe u v u' v'
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false in
/-- Applying a left exact functor to the good lower truncation computes its bottom
homology, including the map on cycles.

Source: Stacks Project, Tag 05TC; kernel calculation in the proof of Tag 08D4 (1).
(blueprint: lem-sc-left-exact-truncation-cycle-formula).

Proof: The incoming differential of K = truncGE n I is zero. Its homology is
therefore a kernel of the outgoing differential. F preserves that kernel and
the cokernel of the zero incoming boundary, giving H^n(FK) = F(H^n K).
The truncation projection induces an isomorphism H^n(I) to H^n(K). Compose
with its inverse under F. On a cycle, naturality of the homology quotient
and uniqueness of the preserved kernel lift give the formula. This uses
only kernel preservation, not preservation of the homology quotient of I;
it works for zero complexes and every integer cutoff. -/
theorem leftExact_truncation_cycle_formula
    {C : Type u} {D : Type u'} [Category.{v} C] [Category.{v'} D]
    [Abelian C] [Abelian D]
    (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F]
    (I : CochainComplex C ℤ) (n : ℤ) :
    let J := (F.mapHomologicalComplex (.up ℤ)).obj I
    let K := (F.mapHomologicalComplex (.up ℤ)).obj (I.truncGE n)
    let c := (J.sc n).liftCycles (F.map (I.sc n).homologyData.left.i) (by
      change F.map (I.sc n).homologyData.left.i ≫ F.map (I.sc n).g = 0
      rw [← F.map_comp, (I.sc n).homologyData.left.wi, F.map_zero]) ≫
      (J.sc n).homologyπ
    ∃ a : K.homology n ≅ F.obj (I.sc n).homologyData.left.H,
      c ≫ HomologicalComplex.homologyMap
        ((F.mapHomologicalComplex (.up ℤ)).map (I.πTruncGE n)) n ≫ a.hom =
        F.map (I.sc n).homologyData.left.π := by
  dsimp only
  simp only [Category.assoc]
  change ∃ a : ((I.truncGE n).sc n |>.map F).homology ≅
    F.obj (I.sc n).homologyData.left.H,
    (I.sc n |>.map F).liftCycles (F.map (I.sc n).homologyData.left.i) _ ≫
      (I.sc n |>.map F).homologyπ ≫
      ShortComplex.homologyMap (F.mapShortComplex.map
        ((HomologicalComplex.shortComplexFunctor C (.up ℤ) n).map (I.πTruncGE n))) ≫
      a.hom = F.map (I.sc n).homologyData.left.π
  let T := I.truncGE n
  let S := T.sc n
  let h := S.homologyData.left
  have hf : S.f = 0 := by
    change T.d ((ComplexShape.up ℤ).prev n) n = 0
    exact (T.isZero_of_isStrictlyGE n _ (by simp)).eq_of_src _ _
  have hf' : h.f' = 0 := by
    rw [← cancel_mono h.i, ShortComplex.LeftHomologyData.f'_i, zero_comp]
    exact hf
  let : h.IsPreservedBy F :=
    { g := inferInstance
      f' := preservesCokernel_zero' F _ hf' }
  let a₀ := (h.map F).homologyIso
  let p := HomologicalComplex.homologyMap (I.πTruncGE n) n
  have : IsIso p := inferInstance
  let a := a₀ ≪≫ (F.mapIso (asIso p)).symm
  refine ⟨a, ?_⟩
  simp only [a, Iso.trans_hom, Iso.symm_hom]
  apply (cancel_mono (F.map p)).mp
  simp only [Category.assoc, Functor.mapIso_inv, asIso_inv, ← F.map_comp,
    IsIso.inv_hom_id, F.map_id]
  let φ := (HomologicalComplex.shortComplexFunctor C (.up ℤ) n).map (I.πTruncGE n)
  let γ : ShortComplex.LeftHomologyMapData φ (I.sc n).homologyData.left h := default
  have hi :
      (S.map F).liftCycles
          (F.map (I.sc n).homologyData.left.i ≫ F.map φ.τ₂) (by
            change (F.map _ ≫ F.map _) ≫ F.map S.g = 0
            rw [Category.assoc, ← F.map_comp, φ.comm₂₃,
              F.map_comp, ← Category.assoc, ← F.map_comp,
              (I.sc n).homologyData.left.wi, F.map_zero, zero_comp]) ≫
        (h.map F).cyclesIso.hom = F.map γ.φK := by
    rw [← cancel_mono (h.map F).i]
    rw [Category.assoc,
      ShortComplex.LeftHomologyData.cyclesIso_hom_comp_i, ShortComplex.liftCycles_i]
    simp only [ShortComplex.LeftHomologyData.map_i, ← F.map_comp]
    exact F.congr_map γ.commi.symm
  erw [Category.comp_id]
  change _ ≫ _ ≫ ShortComplex.homologyMap (F.mapShortComplex.map φ) ≫
    a₀.hom = _
  erw [ShortComplex.homologyπ_naturality_assoc,
    ShortComplex.liftCycles_comp_cyclesMap_assoc,
    ShortComplex.LeftHomologyData.homologyπ_comp_homologyIso_hom]
  change _ ≫ _ ≫ (h.map F).π = _
  erw [← Category.assoc, hi, ShortComplex.LeftHomologyData.map_π, ← F.map_comp,
    ← γ.commπ]
  congr 1

end AlgebraicGeometry
