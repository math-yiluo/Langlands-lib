/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module
public import WeilConjectures.AlgebraicGeometry.Cohomology.InverseImageCoefficientComposition
import WeilConjectures.CategoryTheory.Abelian.Ext.MapExactFunctorExtension

/-! # Composition of exact inverse-image cohomology maps

Source: Stacks Project, Tag 01F7, cohomology-equation-functorial.
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory
namespace AlgebraicGeometry.Scheme.Modules
attribute [local instance] cohomologyHasSheafify cohomologyHasExt

/-- The constant comparison is characterized by its adjunct on global sections. -/
private lemma constant_adjunct_invImage {X Y : Scheme.{u}} (f : Y ⟶ X)
    (F : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})
    (m : (constantSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj
      (AddCommGrpCat.of (ULift.{u} ℤ)) ⟶ F) :
    (constantSheafAdj (Opens.grothendieckTopology Y) AddCommGrpCat.{u}
      CategoryTheory.Limits.isTerminalTop).homEquiv _ _ ((constIso f).inv ≫ (invImage f).map m) =
    (constantSheafAdj (Opens.grothendieckTopology X) AddCommGrpCat.{u}
      CategoryTheory.Limits.isTerminalTop).homEquiv _ _ m ≫
      ((TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{u} f.base).unit.app
        F).hom.app (Opposite.op ⊤) := by
  let a := constantSheafAdj (Opens.grothendieckTopology X) AddCommGrpCat.{u}
    CategoryTheory.Limits.isTerminalTop
  let b := (TopologicalSpace.Opens.map f.base).sheafAdjunctionContinuous AddCommGrpCat.{u}
    (Opens.grothendieckTopology X) (Opens.grothendieckTopology Y)
  let e := (TopologicalSpace.Opens.map f.base).sheafPushforwardContinuousCompSheafSectionsObjIso
    AddCommGrpCat.{u} (Opens.grothendieckTopology X)
    (Opens.grothendieckTopology Y) (Opposite.op ⊤)
  let c := (a.comp b).ofNatIsoRight e
  let d := constantSheafAdj (Opens.grothendieckTopology Y) AddCommGrpCat.{u}
    CategoryTheory.Limits.isTerminalTop
  have hc : d.homEquiv _ _ ((constIso f).inv ≫ (invImage f).map m) =
      c.homEquiv _ _ ((invImage f).map m) := by
    change d.homEquiv _ _ ((c.leftAdjointUniq d).inv.app _ ≫ (invImage f).map m) = _
    rw [Adjunction.leftAdjointUniq_inv_app, Adjunction.homEquiv_naturality_right,
      Adjunction.homEquiv_leftAdjointUniq_hom_app, Adjunction.homEquiv_unit]
    rfl
  rw [hc]
  change c.homEquiv _ _ ((invImage f).map m) = _
  rw [Adjunction.homEquiv_ofNatIsoRight_apply, Adjunction.comp_homEquiv]
  change a.homEquiv _ _ (b.homEquiv _ _ ((invImage f).map m)) ≫
    e.hom.app ((invImage f).obj F) = _
  dsimp only [invImage]
  rw [Adjunction.homEquiv_unit b, b.unit_naturality m,
    Adjunction.homEquiv_naturality_right]
  change a.homEquiv _ _ m ≫
    ((TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{u} f.base).unit.app
      F).hom.app (Opposite.op ⊤) ≫ 𝟙 _ = _
  rw [Category.comp_id]

/-- Inverse-image maps on cohomology compose under the canonical comparison.
Source: Stacks Project, Tag 01F7, cohomology-equation-functorial;
Mathlib's exact-functor action on Ext and uniqueness of left-adjoint comparisons.
(blueprint: lem-pbc-inverse-image-cohomology-composition)

Proof: The constant integer comparison for the composite is the comparison
for g followed by the inverse image under g of the comparison for f, then
invImageComp g f evaluated at the constant integer sheaf. This follows by
applying the composite adjunction: both comparisons are adjoint to the same
constant sections map, so uniqueness of adjuncts identifies them. Expand
H.mapFunctor as precomposition by the constant comparison followed by the
exact-functor action on Ext. The exact-functor action preserves composition
and degree-zero morphisms. Its action for a composite functor agrees with
the successive actions; naturality in the natural isomorphism invImageComp
identifies the composite action with the action of inverse image along g ≫ f.
Associativity of Ext composition and the constant comparison identity give
the displayed equality. No coefficient morphisms occur here. This works for
any abelian sheaf, including zero, every nonnegative degree, identities and
empty schemes.
-/
theorem inverseImageCohomology_comp {X Y Z : Scheme.{u}}
    (g : Z ⟶ Y) (f : Y ⟶ X)
    (F : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})
    (n : ℕ) (x : F.H n) :
    Sheaf.H.map ((invImageComp g f).hom.app F) n
        (Sheaf.H.mapFunctor (invImage g) (constIso g).symm ((invImage f).obj F) n
          (Sheaf.H.mapFunctor (invImage f) (constIso f).symm F n x)) =
      Sheaf.H.mapFunctor (invImage (g ≫ f)) (constIso (g ≫ f)).symm F n x := by
  have hc : (constIso g).inv ≫ (invImage g).map (constIso f).inv =
      (constIso (g ≫ f)).inv ≫ (invImageComp g f).inv.app
        ((constantSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj
          (AddCommGrpCat.of (ULift.{u} ℤ))) := by
    let A := (constantSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj
      (AddCommGrpCat.of (ULift.{u} ℤ))
    let af := TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{u} f.base
    let ag := TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{u} g.base
    let ac := TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{u} (g ≫ f).base
    apply (constantSheafAdj (Opens.grothendieckTopology Z) AddCommGrpCat.{u}
      CategoryTheory.Limits.isTerminalTop).homEquiv _ _ |>.injective
    rw [constant_adjunct_invImage]
    rw [Adjunction.homEquiv_naturality_right]
    have hf := constant_adjunct_invImage f A (𝟙 A)
    have hfg := constant_adjunct_invImage (g ≫ f) A (𝟙 A)
    erw [CategoryTheory.Functor.map_id, Category.comp_id] at hf hfg
    rw [hf, hfg, Category.assoc]
    have hu := unit_conjugateEquiv_symm (af.comp ag) ac (𝟙 _) A
    change (af.comp ag).unit.app A ≫ 𝟙 _ =
      ac.unit.app A ≫ _ at hu
    rw [Category.comp_id] at hu
    erw [Adjunction.comp_unit_app] at hu
    have ht := congrArg (fun m ↦ m.hom.app (Opposite.op ⊤)) hu
    exact congrArg (fun m ↦
      (constantSheafAdj (Opens.grothendieckTopology X) AddCommGrpCat.{u}
        CategoryTheory.Limits.isTerminalTop).homEquiv _ _ (𝟙 A) ≫ m) ht
  have he := Abelian.Ext.mapExactFunctor_comp_mk₀_eq_sheaf
    (invImage f) (invImage g) (invImage (g ≫ f)) (invImageComp g f).symm x
  simp only [Iso.symm_hom] at he
  simp only [Sheaf.H.map_apply, Sheaf.H.mapFunctor_apply, Iso.symm_hom,
    Abelian.Ext.mapExactFunctor_comp, Abelian.Ext.mapExactFunctor_mk₀]
  rw [Abelian.Ext.mk₀_comp_mk₀_assoc, hc]
  rw [← Abelian.Ext.mk₀_comp_mk₀_assoc, ← he]
  simp only [Abelian.Ext.comp_assoc_of_third_deg_zero,
    Abelian.Ext.mk₀_comp_mk₀, Iso.inv_hom_id_app, Abelian.Ext.comp_mk₀_id]

end AlgebraicGeometry.Scheme.Modules
