/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.DerivedGlobalGerm
public import WeilConjectures.SixFunctors.BaseChange.Square

/-! # Underived global germ and exchange

Source: Stacks Project, Tags 095T, 01F8 and 08J6.
-/

@[expose] public section

universe u
open CategoryTheory Limits
namespace AlgebraicGeometry.Etale
open Scheme
attribute [local instance] GrothendieckTopology.Point.sheafFiber_additive
noncomputable local instance instAB5OfSizeAddCommGrpCat_underivedGlobalGermExchange
    : AB5OfSize.{u, u} AddCommGrpCat.{u + 1} :=
  AB5OfSize_shrink.{u, u, u + 1, u + 1} _

-- Abelian-coefficient version of the proved private helper in FiniteEtaleUnitStalkInclusion.
private theorem pullback_unit_germ
    {X Y : Scheme.{u}} (f : Y ⟶ X)
    {Ω : Type u} [Field Ω] [IsSepClosed Ω] (t : Spec (.of Ω) ⟶ Y)
    (G : Sheaf X.smallEtaleTopology (AddCommGrpCat.{u + 1})) (U : X.Etale)
    (v : (Scheme.pointSmallEtale (t ≫ f)).fiber.obj U) :
    ((upperStarLowerStarAdjunction (AddCommGrpCat.{u + 1}) f).unit.app G).hom.app
        (Opposite.op U) ≫
      (Scheme.pointSmallEtale t).toPresheafFiber (f.Etale.obj U)
        ((Scheme.pointSmallEtaleFiberEtaleIso f t).inv.app U v)
        ((f)^*[AddCommGrpCat.{u + 1}].obj G).obj ≫
      ((upperStarCompSheafFiberIso (AddCommGrpCat.{u + 1}) f t).app G).hom =
    (Scheme.pointSmallEtale (t ≫ f)).toPresheafFiber U v G.obj := by
  rw [← Category.assoc]
  apply (Iso.eq_comp_inv _).1
  simp only [upperStarCompSheafFiberIso, Iso.app_inv, Iso.trans_inv, Iso.symm_inv,
    NatTrans.comp_app, Functor.isoWhiskerRight_inv, Functor.whiskerRight_app,
    Category.assoc]
  erw [GrothendieckTopology.Point.toPresheafFiber_sheafFiberIso_inv_app_assoc,
    GrothendieckTopology.Point.toPresheafFiber_sheafFiberComapIso_hom_app_assoc]
  erw [show (Scheme.pointSmallEtale t).sheafFiber.map _ =
    (Scheme.pointSmallEtale t).presheafFiber.map _ from rfl,
    GrothendieckTopology.Point.toPresheafFiber_naturality]
  have hu := Adjunction.unit_leftAdjointUniq_hom_app
    (Functor.sheafAdjunctionContinuous
      (MorphismProperty.Over.pullback @Etale ⊤ f) (AddCommGrpCat.{u + 1})
      (X.smallGrothendieckTopology (P := @Etale))
      (Y.smallGrothendieckTopology (P := @Etale)))
    (upperStarLowerStarAdjunction (AddCommGrpCat.{u + 1}) f) G
  have huU := NatTrans.congr_app (Sheaf.hom_ext_iff.1 hu) (Opposite.op U)
  erw [← Category.assoc, ← huU]
  rfl

-- The terminal-evaluation calculation also used in GlobalSectionsStalkComparison.
private lemma eval_eq_res {C : Type u} [Category C]
    (J : GrothendieckTopology C) (A : Type (u + 1)) [Category A]
    [HasWeakSheafify J A] [HasTerminal C] {T : C} (hT : IsTerminal T)
    (F : Sheaf J A) :
    (Sheaf.ΓNatIsoSheafSections J A hT).hom.app F = F.ΓRes (Opposite.op T) := by
  simp only [Sheaf.ΓNatIsoSheafSections, Sheaf.ΓRes, Sheaf.coneΓ, Sheaf.ΓHomEquiv,
    Adjunction.rightAdjointUniq, conjugateIsoEquiv_apply_hom, conjugateEquiv_apply_app]
  dsimp
  erw [Adjunction.homEquiv_counit]
  erw [Adjunction.homEquiv_unit]
  simp [constantSheafAdj, Adjunction.comp_unit_app]

private theorem pulledGlobalGerm_app
    {Y Y' : Scheme.{u}} (g : Y' ⟶ Y)
    {Ω : Type u} [Field Ω] [IsSepClosed Ω] (t : Spec (.of Ω) ⟶ Y')
    (P : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}) :
    (pulledGlobalGerm g t).app P =
      (Sheaf.Γ Y.smallEtaleTopology AddCommGrpCat.{u + 1}).map
          ((upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} g).unit.app P) ≫
        (lowerStarCompGlobalSectionsIso AddCommGrpCat.{u + 1} g).hom.app
          (((g)^*[AddCommGrpCat.{u + 1}]).obj P) ≫
        (globalGerm t).app (((g)^*[AddCommGrpCat.{u + 1}]).obj P) := by
  let q : Scheme.Etale.mk (𝟙 Y) ⟶ ⊤_ Y.Etale := terminal.from _
  let r : Scheme.Etale.mk (𝟙 Y') ⟶ ⊤_ Y'.Etale := terminal.from _
  let x := (pointSmallEtale (t ≫ g)).fiber.map q
    (Over.homMk (t ≫ g) (Category.comp_id (t ≫ g)))
  have hc := pullback_unit_germ g t P (⊤_ Y.Etale) x
  have hp : (pointSmallEtale t).fiber.map (r ≫ (PreservesTerminal.iso g.Etale).inv)
      (Over.homMk t (Category.comp_id t)) =
      (pointSmallEtaleFiberEtaleIso g t).inv.app (⊤_ Y.Etale) x := by
    have ht := (terminalIsTerminal.isTerminalObj g.Etale).isTerminalObj
      (Scheme.Etale.forget Y')
    exact ht.hom_ext _ _
  let Q := ((g)^*[AddCommGrpCat.{u + 1}]).obj P
  have hY : (Sheaf.ΓNatIsoSheafSections _ _ terminalIsTerminal).inv.app Q ≫
      Q.ΓRes (Opposite.op (Scheme.Etale.mk (𝟙 Y'))) = Q.obj.map r.op := by
    rw [← Sheaf.ΓRes_map Q r.op, ← eval_eq_res _ _ terminalIsTerminal Q]
    simp
  change (globalGerm (t ≫ g)).app P ≫
    (upperStarCompSheafFiberIso _ g t).inv.app P = _
  apply (Iso.comp_inv_eq ((upperStarCompSheafFiberIso _ g t).app P)).2
  simp only [globalGerm, lowerStarCompGlobalSectionsIso,
    Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app, Functor.isoWhiskerLeft_hom,
    Functor.whiskerLeft_app, Category.assoc, eval_eq_res]
  rw [reassoc_of% hY]
  simp only [lowerStarCompSheafSectionsTerminalIso, NatIso.ofComponents_hom_app,
    Functor.mapIso_hom, Iso.op_inv, Iso.symm_hom,
    GrothendieckTopology.Point.toPresheafFiberNatTrans]
  rw [reassoc_of% (Sheaf.ΓRes_naturality
    ((upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} g).unit.app P)
    (Opposite.op (⊤_ Y.Etale)))]
  rw [← Category.assoc (Q.obj.map _) (Q.obj.map _), ← Functor.map_comp, ← op_comp]
  erw [GrothendieckTopology.Point.toPresheafFiber_w_assoc, hp]
  erw [hc]
  rw [← Sheaf.ΓRes_map P q.op, Category.assoc]
  erw [GrothendieckTopology.Point.toPresheafFiber_w]

private theorem lowerStarCompGlobalSectionsIso_comp
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (h : X ⟶ Z) (hh : h = f ≫ g)
    (P : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) :
    (Sheaf.Γ Z.smallEtaleTopology AddCommGrpCat.{u + 1}).map
        ((lowerStarComp AddCommGrpCat.{u + 1} f g h hh).hom.app P) ≫
      (lowerStarCompGlobalSectionsIso AddCommGrpCat.{u + 1} h).hom.app P =
    (lowerStarCompGlobalSectionsIso AddCommGrpCat.{u + 1} g).hom.app
        (((f)_*[AddCommGrpCat.{u + 1}]).obj P) ≫
      (lowerStarCompGlobalSectionsIso AddCommGrpCat.{u + 1} f).hom.app P := by
  apply (cancel_mono ((Sheaf.ΓNatIsoSheafSections _ _ terminalIsTerminal).hom.app P)).1
  simp only [lowerStarCompGlobalSectionsIso, Iso.trans_hom, Iso.symm_hom,
    NatTrans.comp_app, Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app, Category.assoc,
    Iso.inv_hom_id_app, Iso.inv_hom_id_app_assoc, Category.comp_id]
  rw [reassoc_of% ((Sheaf.ΓNatIsoSheafSections Z.smallEtaleTopology
    AddCommGrpCat.{u + 1} terminalIsTerminal).hom.naturality
    ((lowerStarComp AddCommGrpCat.{u + 1} f g h hh).hom.app P))]
  simp only [lowerStarCompSheafSectionsTerminalIso, NatIso.ofComponents_hom_app,
    Functor.mapIso_hom, Iso.symm_hom, Iso.op_inv]
  congr 1
  change ((lowerStarComp AddCommGrpCat.{u + 1} f g h hh).hom.app P).hom.app
    (Opposite.op (⊤_ Z.Etale)) ≫ P.obj.map (PreservesTerminal.iso h.Etale).inv.op = _
  simp only [lowerStarComp, Functor.sheafPushforwardContinuousComp'_hom_app_hom_app,
    Iso.symm_inv, lowerStar_obj_val_map, ← Functor.map_comp, ← op_comp]
  congr 2
  exact ((terminalIsTerminal.isTerminalObj g.Etale).isTerminalObj f.Etale).hom_ext _ _

private theorem squareLowerStarIso_globalSections
    {X X' Y Y' : Scheme.{u}} {f : X ⟶ Y} {f' : X' ⟶ Y'}
    {g : Y' ⟶ Y} {g' : X' ⟶ X} (sq : CommSq g' f' f g)
    (P : Sheaf X'.smallEtaleTopology AddCommGrpCat.{u + 1}) :
    (Sheaf.Γ Y.smallEtaleTopology AddCommGrpCat.{u + 1}).map
        ((squareLowerStarIso AddCommGrpCat.{u + 1} sq).hom.app P) ≫
      (lowerStarCompGlobalSectionsIso AddCommGrpCat.{u + 1} g).hom.app
        (((f')_*[AddCommGrpCat.{u + 1}]).obj P) ≫
      (lowerStarCompGlobalSectionsIso AddCommGrpCat.{u + 1} f').hom.app P =
    (lowerStarCompGlobalSectionsIso AddCommGrpCat.{u + 1} f).hom.app
        (((g')_*[AddCommGrpCat.{u + 1}]).obj P) ≫
      (lowerStarCompGlobalSectionsIso AddCommGrpCat.{u + 1} g').hom.app P := by
  simp only [squareLowerStarIso, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    Functor.map_comp, Category.assoc]
  rw [← lowerStarCompGlobalSectionsIso_comp f' g (g' ≫ f) sq.w P]
  simp only [← Functor.map_comp_assoc, Iso.inv_hom_id_app, Category.comp_id]
  exact lowerStarCompGlobalSectionsIso_comp g' f (g' ≫ f) rfl P

/-- Global germs identify underived exchange with pullback of global sections.
Source: Stacks Project, etale-cohomology.tex, Tag 095T, final map-on-stalks paragraph;
cohomology.tex, Tag 01F8.
(blueprint: lem-weil-pbc-underived-global-germ-exchange)

Proof: Evaluate both transformations on a sheaf and a global section. The inverse of
`lowerStarCompGlobalSectionsIso` views the section on the terminal object over Y.
The pulled germ is its germ at the image of t, transported to the inverse-image stalk.
Expand the exchange as the mate of the pullback-square isomorphism. The adjunction
triangle identities cancel the counit and the unit on the Y side. What remains is the
unit into g'_*g'^* applied to the original section, followed by the terminal-object
identification over X' and its germ over Y'. Expand the stalk identification into
`sheafPullbackIso`, `sheafFiberComapIso` and `pointSmallEtaleComapIso`; their unit-germ
formulas give this equality already on each representative in the stalk colimit.
The terminal-section identifications give exactly the three remaining components of b.
This uses only commutativity of the square and works for separably closed Ω. -/
theorem underivedGlobalGerm_exchange
    {X X' Y Y' : Scheme.{u}} (f : X ⟶ Y) (f' : X' ⟶ Y')
    (g : Y' ⟶ Y) (g' : X' ⟶ X) (sq : CommSq g' f' f g)
    {Ω : Type u} [Field Ω] [IsSepClosed Ω] (t : Spec (.of Ω) ⟶ Y') :
    let B := AddCommGrpCat.{u + 1}
    let F := lowerStar B f
    let F' := lowerStar B f'
    let G := upperStar B g
    let G' := upperStar B g'
    let R := lowerStar B g'
    let H := Sheaf.Γ X.smallEtaleTopology B
    let S := (pointSmallEtale t).sheafFiber
    let a : H ⟶ G' ⋙ F' ⋙ S :=
      (lowerStarCompGlobalSectionsIso B f).inv ≫
        Functor.whiskerLeft F (pulledGlobalGerm g t) ≫
        (Functor.associator F G S).inv ≫
        Functor.whiskerRight (baseChangeMap B sq) S ≫
        (Functor.associator G' F' S).hom
    let b : H ⟶ G' ⋙ F' ⋙ S :=
      (Functor.leftUnitor H).inv ≫
        Functor.whiskerRight (upperStarLowerStarAdjunction B g').unit H ≫
        (Functor.associator G' R H).hom ≫
        Functor.whiskerLeft G' (lowerStarCompGlobalSectionsIso B g').hom ≫
        Functor.whiskerLeft G' (lowerStarCompGlobalSectionsIso B f').inv ≫
        Functor.whiskerLeft G' (Functor.whiskerLeft F' (globalGerm t))
    a = b := by
  dsimp only
  apply NatTrans.ext
  funext P
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_hom_app, Functor.associator_inv_app, Functor.leftUnitor_inv_app,
    Category.comp_id, Category.id_comp]
  rw [pulledGlobalGerm_app]
  simp only [Category.assoc]
  erw [← ((globalGerm t).naturality
    ((baseChangeMap AddCommGrpCat.{u + 1} sq).app P))]
  erw [← reassoc_of% ((lowerStarCompGlobalSectionsIso AddCommGrpCat.{u + 1} g).hom.naturality
    ((baseChangeMap AddCommGrpCat.{u + 1} sq).app P))]
  rw [← Functor.map_comp_assoc, unit_map_baseChangeMap_app]
  simp only [Functor.map_comp, Category.assoc]
  erw [← reassoc_of% ((lowerStarCompGlobalSectionsIso AddCommGrpCat.{u + 1} f).inv.naturality
    ((upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} g').unit.app P))]
  congr 1
  have hc := squareLowerStarIso_globalSections sq (((g')^*[AddCommGrpCat.{u + 1}]).obj P)
  have hc' := congrArg (fun k ↦
    (lowerStarCompGlobalSectionsIso AddCommGrpCat.{u + 1} f).inv.app
      (((g')_*[AddCommGrpCat.{u + 1}]).obj (((g')^*[AddCommGrpCat.{u + 1}]).obj P)) ≫
      k ≫ (lowerStarCompGlobalSectionsIso AddCommGrpCat.{u + 1} f').inv.app
        (((g')^*[AddCommGrpCat.{u + 1}]).obj P) ≫
      (globalGerm t).app (((f')_*[AddCommGrpCat.{u + 1}]).obj
        (((g')^*[AddCommGrpCat.{u + 1}]).obj P))) hc
  simpa only [Functor.comp_obj, Category.assoc, Iso.hom_inv_id_app_assoc,
    Iso.inv_hom_id_app_assoc] using hc'

end AlgebraicGeometry.Etale
