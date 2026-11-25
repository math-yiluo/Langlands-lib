/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.EtaleSetConstantPullbackComparison
public import WeilConjectures.AlgebraicGeometry.EtaleSetInverseImageCompositionUnits
import WeilConjectures.AlgebraicGeometry.EtaleSetConstantPullbackUnitGenerators
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs

/-! # Constant comparison compatibility

Source: Stacks Project, Tags 03CB, 03CC, 0B65, and 03P5.
(blueprint: lem-weil-pbc-etale-set-constant-pullback-composition).
-/

@[expose] public section

universe u
open CategoryTheory Opposite
namespace AlgebraicGeometry

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- Constant comparisons respect the chosen inverse-image composition comparison.
Source: Stacks Project, Tags 03CB, 03CC, 0B65, and 03P5.
(blueprint: lem-weil-pbc-etale-set-constant-pullback-composition).
Proof: compare maps from the constant sheaf on V using its adjunction with terminal
sections. Evaluate each map on a constant generator at the terminal object. The
unit equation for the constant comparison replaces each inverse comparison by the
corresponding inverse-image unit. The section formula for the chosen composition
comparison replaces the two successive units by the composite unit, with the
canonical fibre-product comparison. This comparison preserves terminal objects and
therefore takes an equal-valued constant generator to the same generator. The
composite constant unit equation identifies the result with the inverse comparison
for v composed with h. Equality on terminal generators, followed by injectivity of
the constant-sheaf adjunction, proves equality of morphisms. No invertibility of a
map out of a constant sheaf, or condition on the schemes, is used. -/
theorem etaleSetConstantPullbackComposition
    (P U V : Scheme.{u}) (h : U ⟶ P) (v : V ⟶ U) (A : Type (u + 1)) :
    (etaleSetConstantPullbackComparison v).inv.app A ≫
      (Scheme.etaleSetPullback v).map ((etaleSetConstantPullbackComparison h).inv.app A) ≫
      ((Classical.choose etaleSetInverseImageCompositionUnits.2.2)
        P U V h v).hom.app
        ((constantSheaf P.smallEtaleTopology (Type (u + 1))).obj A) =
      (etaleSetConstantPullbackComparison (v ≫ h)).inv.app A  := by
  let c := Classical.choose etaleSetInverseImageCompositionUnits.2.2
  let CP := (constantSheaf P.smallEtaleTopology (Type (u + 1))).obj A
  let CU := (constantSheaf U.smallEtaleTopology (Type (u + 1))).obj A
  let CV := (constantSheaf V.smallEtaleTopology (Type (u + 1))).obj A
  let bh : P.Etale ⥤ U.Etale := MorphismProperty.Over.pullback @Etale ⊤ h
  let bv : U.Etale ⥤ V.Etale := MorphismProperty.Over.pullback @Etale ⊤ v
  let T := CategoryTheory.Limits.terminal P.Etale
  let W : U.Etale := bh.obj T
  let Z : V.Etale := bv.obj W
  let m : CV ⟶ (Scheme.etaleSetPullback (v ≫ h)).obj CP :=
    (etaleSetConstantPullbackComparison v).inv.app A ≫
      (Scheme.etaleSetPullback v).map ((etaleSetConstantPullbackComparison h).inv.app A) ≫
      (c P U V h v).hom.app CP
  let n : CV ⟶ (Scheme.etaleSetPullback (v ≫ h)).obj CP :=
    (etaleSetConstantPullbackComparison (v ≫ h)).inv.app A
  have hz (e : A) : m.hom.app (op Z)
      ((toSheafify V.smallEtaleTopology ((Functor.const V.Etaleᵒᵖ).obj A)).app (op Z) e) =
      n.hom.app (op Z)
      ((toSheafify V.smallEtaleTopology ((Functor.const V.Etaleᵒᵖ).obj A)).app (op Z) e) := by
    have hv := etaleSetConstantPullbackUnitGenerators U V v A W e
    have hh := etaleSetConstantPullbackUnitGenerators P U h A T e
    have hn := etaleSetInverseImageCompositionUnits.2.1 U V v CU
      ((Scheme.etaleSetPullback h).obj CP)
      ((etaleSetConstantPullbackComparison h).inv.app A) W
      ((toSheafify U.smallEtaleTopology ((Functor.const U.Etaleᵒᵖ).obj A)).app (op W) e)
    have hc := (Classical.choose_spec etaleSetInverseImageCompositionUnits.2.2).1
      P U V h v CP T
      ((toSheafify P.smallEtaleTopology ((Functor.const P.Etaleᵒᵖ).obj A)).app (op T) e)
    have hk := etaleSetConstantPullbackUnitGenerators P V (v ≫ h) A T e
    dsimp only [m, ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app]
    simp only [ConcreteCategory.comp_apply]
    dsimp only [CU, CP] at hn hc hk
    rw [← hv]
    dsimp only [Z, bv]
    erw [← hn]
    dsimp only [W, bh]
    erw [← hh]
    dsimp only [Z, W, bv, bh, c]
    erw [hc, hk]
    have hn' := ConcreteCategory.congr_hom (n.hom.naturality
      ((MorphismProperty.Over.pullbackComp (P := @Etale) (Q := ⊤) v h).inv.app T).op)
      ((toSheafify V.smallEtaleTopology ((Functor.const V.Etaleᵒᵖ).obj A)).app
        (op ((MorphismProperty.Over.pullback @Etale ⊤ (v ≫ h)).obj T)) e)
    simp only [ConcreteCategory.comp_apply] at hn'
    have he := ConcreteCategory.congr_hom
      ((toSheafify V.smallEtaleTopology ((Functor.const V.Etaleᵒᵖ).obj A)).naturality
        ((MorphismProperty.Over.pullbackComp (P := @Etale) (Q := ⊤) v h).inv.app T).op) e
    simp only [ConcreteCategory.comp_apply, Functor.const_obj_map] at he
    exact hn'.symm.trans (congrArg (fun z ↦ n.hom.app (op Z) z) he.symm)
  apply (constantSheafAdj V.smallEtaleTopology (Type (u + 1))
    CategoryTheory.Limits.terminalIsTerminal).homEquiv A _ |>.injective
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
  ext e
  let i := CategoryTheory.Limits.PreservesTerminal.iso
    ((MorphismProperty.Over.pullback @Etale ⊤ h) ⋙
      (MorphismProperty.Over.pullback @Etale ⊤ v))
  have hm := ConcreteCategory.congr_hom (m.hom.naturality i.inv.op)
    ((toSheafify V.smallEtaleTopology ((Functor.const V.Etaleᵒᵖ).obj A)).app (op Z) e)
  have hn := ConcreteCategory.congr_hom (n.hom.naturality i.inv.op)
    ((toSheafify V.smallEtaleTopology ((Functor.const V.Etaleᵒᵖ).obj A)).app (op Z) e)
  have he := ConcreteCategory.congr_hom
    ((toSheafify V.smallEtaleTopology ((Functor.const V.Etaleᵒᵖ).obj A)).naturality i.inv.op) e
  simp only [ConcreteCategory.comp_apply] at hm hn
  simp only [ConcreteCategory.comp_apply, Functor.const_obj_map] at he
  have hterm := hm.trans ((congrArg (fun z ↦
    ((Scheme.etaleSetPullback (v ≫ h)).obj CP).obj.map i.inv.op z) (hz e)).trans hn.symm)
  have he' : (toSheafify V.smallEtaleTopology ((Functor.const V.Etaleᵒᵖ).obj A)).app
      (op (CategoryTheory.Limits.terminal V.Etale)) e =
      CV.obj.map i.inv.op
        ((toSheafify V.smallEtaleTopology ((Functor.const V.Etaleᵒᵖ).obj A)).app
          (op Z) e) := he
  have hf := (congrArg (fun z ↦ m.hom.app
    (op (CategoryTheory.Limits.terminal V.Etale)) z) he').trans
      (hterm.trans (congrArg (fun z ↦ n.hom.app
        (op (CategoryTheory.Limits.terminal V.Etale)) z) he'.symm))
  exact hf

end AlgebraicGeometry
