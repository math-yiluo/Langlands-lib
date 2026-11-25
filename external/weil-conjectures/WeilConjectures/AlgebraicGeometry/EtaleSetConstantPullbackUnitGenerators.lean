/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.EtaleSetConstantPullbackComparison
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs

/-! # Constant comparison compatibility

Source: Stacks Project, Tags 03CB, 03CC, 0B65, and 03P5.
(blueprint: lem-weil-pbc-etale-set-constant-pullback-unit-generators).
-/

@[expose] public section

universe u
open CategoryTheory Opposite
namespace AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- The inverse constant comparison preserves a unit-pulled generator.
Source: Stacks Project, Tags 0B65 and 03P5.
(blueprint: lem-weil-pbc-etale-set-constant-pullback-unit-generators).
Proof: the defining left-adjoint uniqueness equation identifies the composite
constant-sheaf and inverse-image unit with the constant unit at the terminal object,
using the canonical isomorphism from the pulled terminal object. Naturality of the
sheafification unit restricts the equal-valued generator to any object. Naturality
of the inverse-image unit and of the comparison then restricts the terminal equality
along the unique map from W to the terminal object. The terminal comparison commutes
with these unique maps by terminality. Cancel the forward comparison to obtain the
inverse-comparison formula. This also works for empty A and empty schemes. -/
theorem etaleSetConstantPullbackUnitGenerators
    (P U : Scheme.{u}) (h : U ⟶ P) (A : Type (u + 1)) (W : P.Etale) (e : A) :
    (((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
      (MorphismProperty.Over.pullback @Etale ⊤ h) (Type (u + 1))
      (P.smallGrothendieckTopology @Etale) (U.smallGrothendieckTopology @Etale)).unit.app
      ((constantSheaf P.smallEtaleTopology (Type (u + 1))).obj A)).hom.app (op W))
      ((toSheafify P.smallEtaleTopology ((Functor.const P.Etaleᵒᵖ).obj A)).app (op W) e) =
    ((etaleSetConstantPullbackComparison h).inv.app A).hom.app
      (op ((MorphismProperty.Over.pullback @Etale ⊤ h).obj W))
      ((toSheafify U.smallEtaleTopology ((Functor.const U.Etaleᵒᵖ).obj A)).app
        (op ((MorphismProperty.Over.pullback @Etale ⊤ h).obj W)) e)  := by
  let b := MorphismProperty.Over.pullback @Etale ⊤ h
  let : b.IsContinuous P.smallEtaleTopology U.smallEtaleTopology :=
    Etale.isContinuous_overPullback h
  let adj := Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
    b (Type (u + 1)) (P.smallGrothendieckTopology @Etale)
      (U.smallGrothendieckTopology @Etale)
  let CP := (constantSheaf P.smallEtaleTopology (Type (u + 1))).obj A
  let CU := (constantSheaf U.smallEtaleTopology (Type (u + 1))).obj A
  let LP := (Scheme.etaleSetPullback h).obj CP
  let i := CategoryTheory.Limits.PreservesTerminal.iso b
  let α := (etaleSetConstantPullbackComparison h).hom.app A
  let E : b.sheafPushforwardContinuous (Type (u + 1))
      P.smallEtaleTopology U.smallEtaleTopology ⋙
        (sheafSections P.smallEtaleTopology (Type (u + 1))).obj
          (op (CategoryTheory.Limits.terminal P.Etale)) ≅
      (sheafSections U.smallEtaleTopology (Type (u + 1))).obj
          (op (CategoryTheory.Limits.terminal U.Etale)) :=
    NatIso.ofComponents (fun K ↦ K.obj.mapIso i.op.symm)
      (fun β ↦ (β.hom.naturality _).symm)
  have ht := Adjunction.unit_leftAdjointUniq_hom_app
    (((constantSheafAdj P.smallEtaleTopology (Type (u + 1))
      CategoryTheory.Limits.terminalIsTerminal).comp adj).ofNatIsoRight E)
    (constantSheafAdj U.smallEtaleTopology (Type (u + 1))
      CategoryTheory.Limits.terminalIsTerminal) A
  have ht' := ConcreteCategory.congr_hom ht e
  change α.hom.app (op (CategoryTheory.Limits.terminal U.Etale))
    (LP.obj.map i.inv.op ((adj.unit.app CP).hom.app
      (op (CategoryTheory.Limits.terminal P.Etale))
      ((toSheafify P.smallEtaleTopology ((Functor.const P.Etaleᵒᵖ).obj A)).app
        (op (CategoryTheory.Limits.terminal P.Etale)) e))) =
    (toSheafify U.smallEtaleTopology ((Functor.const U.Etaleᵒᵖ).obj A)).app
      (op (CategoryTheory.Limits.terminal U.Etale)) e at ht'
  let t := b.map (CategoryTheory.Limits.terminal.from W) ≫ i.hom
  let z := (toSheafify P.smallEtaleTopology ((Functor.const P.Etaleᵒᵖ).obj A)).app
    (op (CategoryTheory.Limits.terminal P.Etale)) e
  let y := (adj.unit.app CP).hom.app
    (op (CategoryTheory.Limits.terminal P.Etale)) z
  have hn := ConcreteCategory.congr_hom (α.hom.naturality t.op) (LP.obj.map i.inv.op y)
  simp only [ConcreteCategory.comp_apply] at hn
  have hr := hn.trans (congrArg (fun x ↦ CU.obj.map t.op x) ht')
  have hm : LP.obj.map i.inv.op ≫ LP.obj.map t.op =
      LP.obj.map (b.map (CategoryTheory.Limits.terminal.from W)).op := by
    rw [← Functor.map_comp, ← op_comp]
    simp only [t, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  have hm' := ConcreteCategory.congr_hom hm y
  simp only [ConcreteCategory.comp_apply] at hm'
  have hu := ConcreteCategory.congr_hom ((adj.unit.app CP).hom.naturality
    (CategoryTheory.Limits.terminal.from W).op) z
  simp only [ConcreteCategory.comp_apply] at hu
  have hp := ConcreteCategory.congr_hom
    ((toSheafify P.smallEtaleTopology ((Functor.const P.Etaleᵒᵖ).obj A)).naturality
      (CategoryTheory.Limits.terminal.from W).op) e
  have hv := ConcreteCategory.congr_hom
    ((toSheafify U.smallEtaleTopology ((Functor.const U.Etaleᵒᵖ).obj A)).naturality t.op) e
  simp only [ConcreteCategory.comp_apply, Functor.const_obj_map] at hp hv
  have hg : α.hom.app (op (b.obj W))
      ((adj.unit.app CP).hom.app (op W)
        ((toSheafify P.smallEtaleTopology ((Functor.const P.Etaleᵒᵖ).obj A)).app
          (op W) e)) =
      (toSheafify U.smallEtaleTopology ((Functor.const U.Etaleᵒᵖ).obj A)).app
        (op (b.obj W)) e := by
    calc
      _ = α.hom.app (op (b.obj W))
          ((adj.unit.app CP).hom.app (op W) (CP.obj.map
            (CategoryTheory.Limits.terminal.from W).op z)) :=
        congrArg (fun x ↦ α.hom.app (op (b.obj W)) ((adj.unit.app CP).hom.app (op W) x)) hp
      _ = α.hom.app (op (b.obj W))
          (LP.obj.map (b.map (CategoryTheory.Limits.terminal.from W)).op y) :=
        congrArg (fun x ↦ α.hom.app (op (b.obj W)) x) hu
      _ = α.hom.app (op (b.obj W)) (LP.obj.map t.op (LP.obj.map i.inv.op y)) :=
        congrArg (fun x ↦ α.hom.app (op (b.obj W)) x) hm'.symm
      _ = CU.obj.map t.op
          ((toSheafify U.smallEtaleTopology ((Functor.const U.Etaleᵒᵖ).obj A)).app
            (op (CategoryTheory.Limits.terminal U.Etale)) e) := hr
      _ = _ := hv.symm
  have hg' := congrArg (fun x ↦ ((etaleSetConstantPullbackComparison h).inv.app A).hom.app
    (op (b.obj W)) x) hg
  have hi := ConcreteCategory.congr_hom (NatTrans.congr_app
    (congrArg (fun f ↦ f.hom) ((etaleSetConstantPullbackComparison h).hom_inv_id_app A))
      (op (b.obj W)))
      ((adj.unit.app CP).hom.app (op W)
        ((toSheafify P.smallEtaleTopology ((Functor.const P.Etaleᵒᵖ).obj A)).app (op W) e))
  simp only [ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app,
    ConcreteCategory.comp_apply, ObjectProperty.FullSubcategory.id_hom,
    NatTrans.id_app, types_id_apply] at hi
  exact hi.symm.trans hg'


end AlgebraicGeometry
