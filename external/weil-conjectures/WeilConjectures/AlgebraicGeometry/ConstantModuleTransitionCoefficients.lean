/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.ConstructibleSheaf.Defs

@[expose] public section

set_option autoImplicit false
universe u v
open CategoryTheory Limits Opposite
namespace AlgebraicGeometry.Etale

/-- The adjoint of the constant-sheaf pullback comparison. -/
private noncomputable def constantTransition
    (A : Type v) [Category.{u + 1} A] [Abelian A]
    [IsGrothendieckAbelian.{u + 1} A] [HasSmallSiteSheafify A] (M : A)
    {Y Z : Scheme.{u}} (g : Z ⟶ Y) :
    (constantSheaf Y.smallEtaleTopology A).obj M ⟶
      (lowerStar A g).obj
        ((constantSheaf Z.smallEtaleTopology A).obj M) :=
  (upperStarLowerStarAdjunction A g).unit.app _ ≫
    (lowerStar A g).map
      ((Scheme.upperStarConstantSheafIso A g).hom.app M)

set_option backward.isDefEq.respectTransparency false in
/-- The transition preserves the sheafification generator at the terminal object.
This is the unit equation for uniqueness of left adjoints, followed by naturality. -/
private lemma constantTransition_terminal
    (A : Type v) [Category.{u + 1} A] [Abelian A]
    [IsGrothendieckAbelian.{u + 1} A] [HasSmallSiteSheafify A] (M : A)
    {Y Z : Scheme.{u}} (g : Z ⟶ Y) :
    (toSheafify Y.smallEtaleTopology ((Functor.const Y.Etaleᵒᵖ).obj M)).app
        (Opposite.op (⊤_ Y.Etale)) ≫
      (((upperStarLowerStarAdjunction A g).unit.app _ ≫
        (lowerStar A g).map
          ((Scheme.upperStarConstantSheafIso A g).hom.app M)).hom).app
            (Opposite.op (⊤_ Y.Etale)) ≫
      ((lowerStarCompSheafSectionsTerminalIso A g).hom.app _) =
    (toSheafify Z.smallEtaleTopology ((Functor.const Z.Etaleᵒᵖ).obj M)).app
        (Opposite.op (⊤_ Z.Etale)) := by
  have h := Adjunction.unit_leftAdjointUniq_hom_app
    (((constantSheafAdj Y.smallEtaleTopology A
        terminalIsTerminal).comp
        (upperStarLowerStarAdjunction A g)).ofNatIsoRight
      (lowerStarCompSheafSectionsTerminalIso A g))
    (constantSheafAdj Z.smallEtaleTopology A terminalIsTerminal) M
  have hn := (lowerStarCompSheafSectionsTerminalIso A g).hom.naturality
    ((Scheme.upperStarConstantSheafIso A g).hom.app M)
  simp only [ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app, Category.assoc]
  change
    ((lowerStar A g).map
        ((Scheme.upperStarConstantSheafIso A g).hom.app M)).hom.app
          (Opposite.op (⊤_ Y.Etale)) ≫
      (lowerStarCompSheafSectionsTerminalIso A g).hom.app _ =
    (lowerStarCompSheafSectionsTerminalIso A g).hom.app _ ≫
      ((Scheme.upperStarConstantSheafIso A g).hom.app M).hom.app
        (Opposite.op (⊤_ Z.Etale)) at hn
  exact (congrArg (fun k ↦
    (toSheafify Y.smallEtaleTopology ((Functor.const Y.Etaleᵒᵖ).obj M)).app
      (Opposite.op (⊤_ Y.Etale)) ≫
    ((upperStarLowerStarAdjunction A g).unit.app _).hom.app
      (Opposite.op (⊤_ Y.Etale)) ≫ k) hn).trans (by
      simpa only [Scheme.upperStarConstantSheafIso, Category.assoc,
        Adjunction.ofNatIsoRight, constantSheafAdj, ObjectProperty.ι_map,
        Adjunction.comp_unit_app, NatTrans.comp_app,
        Functor.whiskerLeft_app, constantPresheafAdj_unit_app,
        Functor.constCompEvaluationObj_hom_app,
        Category.id_comp, sheafificationAdjunction_unit_app, Functor.comp_obj,
        evaluation, constantSheaf, sheafSections, Functor.flip, sheafToPresheaf] using h)

set_option backward.isDefEq.respectTransparency false in
/-- The transition preserves all constant-presheaf generators.
Transport the terminal-object equation along the unique map to the terminal object. -/
private lemma constantTransition_generators
    (A : Type v) [Category.{u + 1} A] [Abelian A]
    [IsGrothendieckAbelian.{u + 1} A] [HasSmallSiteSheafify A] (M : A)
    {Y Z : Scheme.{u}} (g : Z ⟶ Y) (U : Y.Etaleᵒᵖ) :
    (toSheafify Y.smallEtaleTopology ((Functor.const Y.Etaleᵒᵖ).obj M)).app U ≫
      (constantTransition A M g).hom.app U =
    (toSheafify Z.smallEtaleTopology ((Functor.const Z.Etaleᵒᵖ).obj M)).app
        (g.Etale.op.obj U) := by
  let CY := (constantSheaf Y.smallEtaleTopology A).obj M
  let CZ := (constantSheaf Z.smallEtaleTopology A).obj M
  let t : CY ⟶ (lowerStar A g).obj CZ :=
    (upperStarLowerStarAdjunction A g).unit.app _ ≫
      (lowerStar A g).map
        ((Scheme.upperStarConstantSheafIso A g).hom.app M)
  let eY := toSheafify Y.smallEtaleTopology ((Functor.const Y.Etaleᵒᵖ).obj M)
  let eZ := toSheafify Z.smallEtaleTopology ((Functor.const Z.Etaleᵒᵖ).obj M)
  let a := (terminalIsTerminal.from U.unop).op
  let i := PreservesTerminal.iso g.Etale
  have ht := constantTransition_terminal A M g
  change eY.app (Opposite.op (⊤_ Y.Etale)) ≫ t.hom.app _ ≫
    CZ.obj.map i.inv.op = eZ.app (Opposite.op (⊤_ Z.Etale)) at ht
  have ht' := congrArg (fun k ↦ k ≫ CZ.obj.map i.hom.op) ht
  simp only [Category.assoc, ← Functor.map_comp, ← op_comp,
    Iso.hom_inv_id, op_id] at ht'
  change eY.app (Opposite.op (⊤_ Y.Etale)) ≫
    t.hom.app (Opposite.op (⊤_ Y.Etale)) ≫ CZ.obj.map (𝟙 _) = _ at ht'
  rw [CZ.obj.map_id] at ht'
  have ht'' : eY.app (Opposite.op (⊤_ Y.Etale)) ≫ t.hom.app _ =
      eZ.app (Opposite.op (⊤_ Z.Etale)) ≫ CZ.obj.map i.hom.op := by
    exact (Category.comp_id _).symm.trans ((Category.assoc _ _ _).trans ht')
  have hY := eY.naturality a
  have hZ := eZ.naturality ((terminalIsTerminal.from (g.Etale.obj U.unop)).op)
  dsimp only [Functor.const_obj_map, Functor.const_obj_obj] at hY hZ
  simp only [Category.id_comp] at hY hZ
  have hn := t.hom.naturality a
  dsimp only [CY, CZ, constantSheaf, Functor.comp_obj] at hn ⊢
  change eY.app U ≫ t.hom.app U = eZ.app (g.Etale.op.obj U)
  rw [hY, Category.assoc, hn, ← Category.assoc, ht'']
  rw [Category.assoc]
  change eZ.app (Opposite.op (⊤_ Z.Etale)) ≫
    CZ.obj.map i.hom.op ≫ CZ.obj.map (g.Etale.map a.unop).op = _
  dsimp only [CZ, constantSheaf, Functor.comp_obj] at *
  rw [← Functor.map_comp, ← op_comp]
  have he : g.Etale.map a.unop ≫ i.hom =
      terminalIsTerminal.from (g.Etale.obj U.unop) := terminalIsTerminal.hom_ext _ _
  rw [he]
  exact hZ.symm

set_option backward.isDefEq.respectTransparency false in
/-- The coefficient comparison preserves constant-presheaf generators, by the
factorization equation of the sheafification comparison. -/
private lemma coefficient_generators
    (Λ : Type (u + 1)) [CommRing Λ] (M : ModuleCat.{u + 1} Λ)
    (X : Scheme.{u}) (U : X.Etaleᵒᵖ)
    [X.smallEtaleTopology.PreservesSheafification
      (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})] :
    let V := forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}
    V.map ((toSheafify X.smallEtaleTopology
        ((Functor.const X.Etaleᵒᵖ).obj M)).app U) ≫
      ((constantCommuteCompose X.smallEtaleTopology V).hom.app M).hom.app U =
    (toSheafify X.smallEtaleTopology
      ((Functor.const X.Etaleᵒᵖ).obj (V.obj M))).app U := by
  let V := forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}
  have h := sheafComposeIso_inv_fac X.smallEtaleTopology V
    ((Functor.const X.Etaleᵒᵖ).obj M)
  have hn := toSheafify_naturality X.smallEtaleTopology
    (Functor.constComp X.Etaleᵒᵖ M V).hom
  have he := congrArg (fun k ↦ k ≫ sheafifyMap X.smallEtaleTopology
    (Functor.constComp X.Etaleᵒᵖ M V).hom) h
  rw [Category.assoc, ← hn] at he
  simpa only [constantCommuteCompose_hom_app_hom, NatTrans.comp_app,
    V, Functor.whiskerRight_app, Functor.constComp_hom_app, Category.id_comp, Category.assoc] using
    congrArg (fun k ↦ k.app U) he

set_option backward.isDefEq.respectTransparency false in
/-- Forgetting scalars respects the adjoint constant-sheaf transition.

Source: Stacks Project, Tags 03DB and 03CO.
(blueprint: lem-weil-pbc-constant-module-transition-coefficients).

Proof: The adjoint constant comparison sends each sheafification generator to
its base change with the same value. This follows from the unit equation for
uniqueness of left adjoints to terminal evaluation, transported to every object
by naturality. The constantCommuteCompose comparison also sends a generator to
the generator of its underlying abelian group, by the defining equation for
sheafifyComposeIso. Thus both composites agree on every constant-presheaf
generator. Since forgetting scalars preserves sheafification, the source is
canonically the sheafification of the constant underlying abelian presheaf;
the universal property of sheafification proves equality. This argument applies
to zero modules, empty schemes and arbitrary morphisms. -/
theorem constantModuleTransition_coefficients
    (Λ : Type (u + 1)) [CommRing Λ] (M : ModuleCat.{u + 1} Λ)
    {Z W : Scheme.{u}} (g : W ⟶ Z)
    [Z.smallEtaleTopology.PreservesSheafification
      (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})]
    [W.smallEtaleTopology.PreservesSheafification
      (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})] :
    let V := forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}
    let A := AddCommGrpCat.{u + 1}
    (sheafCompose Z.smallEtaleTopology V).map
        ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) g).unit.app _ ≫
          (lowerStar (ModuleCat.{u + 1} Λ) g).map
            ((Scheme.upperStarConstantSheafIso (ModuleCat.{u + 1} Λ) g).hom.app M)) ≫
      (lowerStar A g).map ((constantCommuteCompose W.smallEtaleTopology V).hom.app M) =
    (constantCommuteCompose Z.smallEtaleTopology V).hom.app M ≫
      (upperStarLowerStarAdjunction A g).unit.app _ ≫
      (lowerStar A g).map ((Scheme.upperStarConstantSheafIso A g).hom.app (V.obj M)) := by
  let V := forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}
  let A := AddCommGrpCat.{u + 1}
  let eZ := (constantCommuteCompose Z.smallEtaleTopology V).app M
  let eW := (constantCommuteCompose W.smallEtaleTopology V).app M
  change (sheafCompose Z.smallEtaleTopology V).map
      (constantTransition (ModuleCat.{u + 1} Λ) M g) ≫
    (lowerStar A g).map eW.hom =
      eZ.hom ≫ constantTransition A (V.obj M) g
  apply (cancel_epi eZ.inv).mp
  simp only [eZ.inv_hom_id_assoc]
  apply Sheaf.hom_ext
  apply sheafify_hom_ext _ _ _
    ((lowerStar A g).obj ((constantSheaf W.smallEtaleTopology A).obj (V.obj M))).property
  apply NatTrans.ext
  funext U
  change (toSheafify Z.smallEtaleTopology
      ((Functor.const Z.Etaleᵒᵖ).obj (V.obj M))).app U ≫
      eZ.inv.hom.app U ≫
        V.map ((constantTransition (ModuleCat.{u + 1} Λ) M g).hom.app U) ≫
          eW.hom.hom.app (g.Etale.op.obj U) =
    (toSheafify Z.smallEtaleTopology
      ((Functor.const Z.Etaleᵒᵖ).obj (V.obj M))).app U ≫
      (constantTransition A (V.obj M) g).hom.app U
  have hc := coefficient_generators Λ M Z U
  change V.map ((toSheafify Z.smallEtaleTopology
      ((Functor.const Z.Etaleᵒᵖ).obj M)).app U) ≫ eZ.hom.hom.app U = _ at hc
  have hi := congrArg (fun k ↦ k.hom.app U) eZ.hom_inv_id
  change eZ.hom.hom.app U ≫ eZ.inv.hom.app U = 𝟙 _ at hi
  have hinv : (toSheafify Z.smallEtaleTopology
      ((Functor.const Z.Etaleᵒᵖ).obj (V.obj M))).app U ≫ eZ.inv.hom.app U =
      V.map ((toSheafify Z.smallEtaleTopology
        ((Functor.const Z.Etaleᵒᵖ).obj M)).app U) := by
    rw [← hc, Category.assoc, hi]
    exact Category.comp_id _
  rw [← Category.assoc, hinv, ← V.map_comp_assoc, constantTransition_generators]
  change V.map ((toSheafify W.smallEtaleTopology
      ((Functor.const W.Etaleᵒᵖ).obj M)).app (g.Etale.op.obj U)) ≫
      ((constantCommuteCompose W.smallEtaleTopology V).hom.app M).hom.app
        (g.Etale.op.obj U) = _
  rw [coefficient_generators, constantTransition_generators]

end AlgebraicGeometry.Etale
