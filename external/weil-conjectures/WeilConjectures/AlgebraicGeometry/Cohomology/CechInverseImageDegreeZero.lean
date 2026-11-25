/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Cohomology.FlatCohomologyComparison
public import WeilConjectures.AlgebraicGeometry.Cohomology.CechInverseImageCochainMap

/-! # Degree-zero normalization under inverse image

Source: Stacks Project, Tag 01FD, section faces of Lemma 20.15.1;
Tag 01EQ, degree-zero restriction augmentation.
(blueprint: lem-pc-cech-inverse-image-degree-zero)
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian TopologicalSpace Opposite
namespace AlgebraicGeometry.Scheme.Modules
attribute [local instance] cohomologyHasSheafify cohomologyHasExt

/-- Restricting a global section commutes with the coefficient Čech map.
Source: Stacks Project, Tags 01EQ and 01FD, augmentation naturality. -/
private theorem cech_augmentation_naturality
    {X Y : Scheme.{u}} {ι : Type u} (g : Y ⟶ X)
    (U : ι → X.Opens) (V : ι → Y.Opens)
    (hinter : ∀ (k : ℕ) (y : Fin (k + 1) → ι),
      (⨅ l, V (y l)) ≤ g ⁻¹ᵁ (⨅ l, U (y l)))
    (F : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})
    (G : Sheaf (Opens.grothendieckTopology Y) AddCommGrpCat.{u})
    (α : F.obj ⟶ (Opens.map g.base).op ⋙ G.obj) :
    (TopCat.Sheaf.toCechCohomologyZero U).app F ≫
        HomologicalComplex.homologyMap (cechInverseImageCochainMap g U V hinter F G α) 0 =
      α.app (op ⊤) ≫ G.obj.map (homOfLE (by simp : ⊤ ≤ g ⁻¹ᵁ ⊤)).op ≫
        (TopCat.Sheaf.toCechCohomologyZero V).app G := by
  have h : TopCat.Sheaf.toCechCochainZero U F ≫
      (cechInverseImageCochainMap g U V hinter F G α).f 0 =
      α.app (op ⊤) ≫ G.obj.map (homOfLE (by simp : ⊤ ≤ g ⁻¹ᵁ ⊤)).op ≫
        TopCat.Sheaf.toCechCochainZero V G := by
    ext s
    funext z
    change G.obj.map (homOfLE (hinter 0 z)).op
        (α.app _ (F.obj.map (homOfLE le_top).op s)) =
      G.obj.map (homOfLE le_top).op
        (G.obj.map (homOfLE (by simp : ⊤ ≤ g ⁻¹ᵁ ⊤)).op (α.app (op ⊤) s))
    have hn := NatTrans.naturality_apply α
      (homOfLE (le_top (a := ⨅ l, U (z l)))).op s
    change α.app _ (F.obj.map _ s) = G.obj.map _ (α.app (op ⊤) s) at hn
    refine (congrArg (G.obj.map (homOfLE (hinter 0 z)).op) hn).trans ?_
    exact (TopCat.Presheaf.map_homOfLE_map_homOfLE_apply G.obj _ _ _).trans
      (TopCat.Presheaf.map_homOfLE_map_homOfLE_apply G.obj _ _ _).symm
  simp only [TopCat.Sheaf.toCechCohomologyZero, Category.assoc,
    HomologicalComplex.homologyπ_naturality,
    HomologicalComplex.liftCycles_comp_cyclesMap_assoc,
    HomologicalComplex.comp_liftCycles_assoc]
  simp only [h]

/-- The canonical constant-sheaf comparison transposes to the inverse-image unit.
Source: Stacks Project, Tag 01FD; uniqueness of the constant-sheaf adjunction. -/
private theorem constant_adjunct_pullback
    {X Y : Scheme.{u}} (g : Y ⟶ X)
    (F : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})
    (f : (constantSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj
      (AddCommGrpCat.of (ULift.{u} ℤ)) ⟶ F) :
    (constantSheafAdj (Opens.grothendieckTopology Y) AddCommGrpCat.{u}
      isTerminalTop).homEquiv _ _ ((constIso g).inv ≫ (invImage g).map f) =
    (constantSheafAdj (Opens.grothendieckTopology X) AddCommGrpCat.{u}
      isTerminalTop).homEquiv _ _ f ≫
      ((TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{u} g.base).unit.app
        F).hom.app (op ⊤) ≫
      ((invImage g).obj F).obj.map (homOfLE (by simp : ⊤ ≤ g ⁻¹ᵁ ⊤)).op := by
  let a := constantSheafAdj (Opens.grothendieckTopology X) AddCommGrpCat.{u}
    isTerminalTop
  let b := (Opens.map g.base).sheafAdjunctionContinuous AddCommGrpCat.{u}
    (Opens.grothendieckTopology X) (Opens.grothendieckTopology Y)
  let e := (Opens.map g.base).sheafPushforwardContinuousCompSheafSectionsObjIso
    AddCommGrpCat.{u} (Opens.grothendieckTopology X)
    (Opens.grothendieckTopology Y) (op ⊤)
  let c := (a.comp b).ofNatIsoRight e
  let d := constantSheafAdj (Opens.grothendieckTopology Y) AddCommGrpCat.{u}
    isTerminalTop
  have hc : d.homEquiv _ _ ((constIso g).inv ≫ (invImage g).map f) =
      c.homEquiv _ _ ((invImage g).map f) := by
    change d.homEquiv _ _ ((c.leftAdjointUniq d).inv.app _ ≫ (invImage g).map f) = _
    rw [Adjunction.leftAdjointUniq_inv_app, Adjunction.homEquiv_naturality_right,
      Adjunction.homEquiv_leftAdjointUniq_hom_app, Adjunction.homEquiv_unit]
    rfl
  rw [hc]
  change c.homEquiv _ _ ((invImage g).map f) = _
  rw [Adjunction.homEquiv_ofNatIsoRight_apply, Adjunction.comp_homEquiv]
  change a.homEquiv _ _ (b.homEquiv _ _ ((invImage g).map f)) ≫
    e.hom.app ((invImage g).obj F) = _
  dsimp only [invImage]
  rw [Adjunction.homEquiv_unit b, b.unit_naturality f,
    Adjunction.homEquiv_naturality_right]
  change a.homEquiv _ _ f ≫
    ((TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{u} g.base).unit.app
      F).hom.app (op ⊤) ≫ 𝟙 _ =
    a.homEquiv _ _ f ≫
      ((TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{u} g.base).unit.app
        F).hom.app (op ⊤) ≫ ((invImage g).obj F).obj.map (𝟙 (op ⊤))
  exact congrArg (fun m ↦ a.homEquiv _ _ f ≫
    ((TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{u} g.base).unit.app
      F).hom.app (op ⊤) ≫ m) (((invImage g).obj F).obj.map_id (op ⊤)).symm

/-- In degree zero, exact inverse image acts on sections by the adjunction unit.
Source: Stacks Project, Tag 01FD; the degree-zero Ext description of sections. -/
private theorem ext_zero_sections
    {X Y : Scheme.{u}} (g : Y ⟶ X)
    (F : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})
    (x : Sheaf.H F 0) :
    Sheaf.H.equiv₀ ((invImage g).obj F) isTerminalTop
        (Sheaf.H.mapFunctor (invImage g) (constIso g).symm F 0 x) =
      ((invImage g).obj F).obj.map (homOfLE (by simp : ⊤ ≤ g ⁻¹ᵁ ⊤)).op
        (((TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{u} g.base).unit.app
          F).hom.app (op ⊤) (Sheaf.H.equiv₀ F isTerminalTop x)) := by
  obtain ⟨f, rfl⟩ := (Ext.mk₀_bijective _ F).surjective x
  simp only [Sheaf.H.mapFunctor_apply, Ext.mapExactFunctor_mk₀,
    Ext.mk₀_comp_mk₀]
  have hf : Ext.addEquiv₀ (Ext.mk₀ f) = f := Ext.addEquiv₀.apply_symm_apply f
  have hf' : Ext.addEquiv₀ (Ext.mk₀ ((constIso g).inv ≫ (invImage g).map f)) =
      (constIso g).inv ≫ (invImage g).map f := Ext.addEquiv₀.apply_symm_apply _
  simp only [Sheaf.H.equiv₀, AddEquiv.trans_apply, Adjunction.homAddEquiv_apply,
    Iso.symm_hom, hf, hf']
  have h := congrArg (((invImage g).obj F).obj.obj (op ⊤)).uliftZMultiplesAddEquiv
    (constant_adjunct_pullback g F f)
  refine h.trans ?_
  rfl

/-- Degree-zero Čech pullback agrees with the constant-sheaf Ext pullback.

Source: Stacks Project, Tags 01FD and 01EQ, degree-zero section augmentations.
(blueprint: lem-pc-cech-inverse-image-degree-zero)

Proof: Express x as the restriction class of its unique global section s using
cechCohomologyZeroIso. In each V-member the explicit cochain map sends the
restriction of s to the restriction of the adjunction unit applied to s.
Naturality of the unit and composition of restriction maps prove this equality
of cochains, hence of their degree-zero classes. For Ext, write the degree-zero
class as mk₀ f for a morphism from the constant integer sheaf. Exact inverse
image sends this to mk₀ of the composite constIso.inv followed by the inverse
image of f. The definition of constIso as uniqueness of left adjoints identifies
its constant-sheaf adjunct with the inverse-image unit composed with f. Evaluating
at the integer 1 gives precisely the same pulled-back global section. Apply the
inverse global-section equivalence to conclude. This uses only degree zero and
no comparison system or positive-degree connecting map. If a cover is empty,
the covered scheme and its inverse image are empty and all sections are zero. -/
theorem cechInverseImage_degree_zero
    {X Y : Scheme.{u}} {ι : Type u} (g : Y ⟶ X)
    (U : ι → X.Opens) (V : ι → Y.Opens) (hcover : iSup U = ⊤)
    (hcover' : iSup V = ⊤)
    (hinter : ∀ (k : ℕ) (y : Fin (k + 1) → ι),
      (⨅ l, V (y l)) ≤ g ⁻¹ᵁ (⨅ l, U (y l)))
    (F : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})
    (x : (TopCat.Sheaf.cechCohomologyFunctor U 0).obj F) :
    (((TopCat.Sheaf.cechCohomologyZeroIso V hcover').inv ≫
        (Sheaf.functorHZeroIso.{u} (Opens.grothendieckTopology Y) isTerminalTop).inv).app
        ((invImage g).obj F))
      (HomologicalComplex.homologyMap
        (cechInverseImageCochainMap g U V hinter F ((invImage g).obj F)
          ((TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{u} g.base).unit.app
            F).hom) 0 x) =
      Sheaf.H.mapFunctor (invImage g) (constIso g).symm F 0
        ((((TopCat.Sheaf.cechCohomologyZeroIso U hcover).inv ≫
          (Sheaf.functorHZeroIso.{u} (Opens.grothendieckTopology X) isTerminalTop).inv).app F)
          x) := by
  let G := (invImage g).obj F
  let α := ((TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{u} g.base).unit.app
    F).hom
  let eU := (TopCat.Sheaf.cechCohomologyZeroIso U hcover).app F
  let eV := (TopCat.Sheaf.cechCohomologyZeroIso V hcover').app G
  obtain ⟨s, rfl⟩ := eU.addCommGroupIsoToAddEquiv.surjective x
  let t := G.obj.map (homOfLE (by simp : ⊤ ≤ g ⁻¹ᵁ ⊤)).op (α.app (op ⊤) s)
  have hn := ConcreteCategory.congr_hom
    (cech_augmentation_naturality g U V hinter F G α) s
  have hc : HomologicalComplex.homologyMap
      (cechInverseImageCochainMap g U V hinter F G α) 0 (eU.hom s) = eV.hom t := hn
  change (Sheaf.H.equiv₀ G isTerminalTop).symm
      (eV.inv (HomologicalComplex.homologyMap
        (cechInverseImageCochainMap g U V hinter F G α) 0 (eU.hom s))) =
    Sheaf.H.mapFunctor (invImage g) (constIso g).symm F 0
      ((Sheaf.H.equiv₀ F isTerminalTop).symm (eU.inv (eU.hom s)))
  rw [hc]
  simp only [Iso.hom_inv_id_apply]
  apply (Sheaf.H.equiv₀ G isTerminalTop).injective
  simp only [AddEquiv.apply_symm_apply]
  exact ((ext_zero_sections g F ((Sheaf.H.equiv₀ F isTerminalTop).symm s)).trans
    (congrArg (fun v ↦ G.obj.map (homOfLE (by simp : ⊤ ≤ g ⁻¹ᵁ ⊤)).op
      (α.app (op ⊤) v))
      ((Sheaf.H.equiv₀ F isTerminalTop).apply_symm_apply s))).symm

end AlgebraicGeometry.Scheme.Modules
