/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Proetale
public import WeilConjectures.AlgebraicGeometry.EtaleSetTerminalTransport
import WeilConjectures.AlgebraicGeometry.EtaleSetSectionComparisonIdentity
import WeilConjectures.AlgebraicGeometry.EtaleSetSectionComparisonComposition
import WeilConjectures.AlgebraicGeometry.ProEtale.Comparison.ProEtaleComparisonSectionDescent

/-! # The section-valued comparison sheaf functor

## References

* Stacks Project, Tag 0GLZ (first proof paragraph)
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry

private noncomputable abbrev L {S T : Scheme.{u}} (f : T ⟶ S) :=
  Scheme.etaleSetPullback f

private noncomputable abbrev b {S T : Scheme.{u}} (f : T ⟶ S) :=
  MorphismProperty.Over.pullback @Etale ⊤ f

private noncomputable def terminalIso {X Y : Scheme.{u}} (f : Y ⟶ X) :
    (b f).obj (Scheme.Etale.mk (𝟙 X)) ≅ Scheme.Etale.mk (𝟙 Y) :=
  MorphismProperty.Over.isoMk (asIso (pullback.snd (𝟙 X) f)) (Category.comp_id _)

private noncomputable def sectionIso {X Y : Scheme.{u}} (f : Y ⟶ X)
    (F : Sheaf X.smallEtaleTopology (Type (u + 1))) :
    ((L f).obj F).obj.obj (op (Scheme.Etale.mk (𝟙 Y))) ≅
      ((L f).obj F).obj.obj (op ((b f).obj (Scheme.Etale.mk (𝟙 X)))) :=
  ((L f).obj F).obj.mapIso (terminalIso f).op

set_option backward.isDefEq.respectTransparency false in
private noncomputable def rawPresheaf {X : Scheme.{u}}
    (F : Sheaf X.smallEtaleTopology (Type (u + 1))) : X.ProEtᵒᵖ ⥤ Type (u + 1) where
  obj Y := ((L Y.unop.hom).obj F).obj.obj
    (op ((b Y.unop.hom).obj (Scheme.Etale.mk (𝟙 X))))
  map {Y Z} g := etaleSetSectionComparison g.unop.left Y.unop.hom Z.unop.hom
    (MorphismProperty.Over.w g.unop) F (Scheme.Etale.mk (𝟙 X))
  map_id Y := by
    exact etaleSetSectionComparisonIdentity Y.unop.hom F (Scheme.Etale.mk (𝟙 X))
  map_comp {Y Z W} g h := by
    exact (etaleSetSectionComparisonComposition g.unop.left h.unop.left
      Y.unop.hom Z.unop.hom W.unop.hom (MorphismProperty.Over.w g.unop) (MorphismProperty.Over.w
        h.unop) F
      (Scheme.Etale.mk (𝟙 X))).symm

set_option backward.isDefEq.respectTransparency false in
private lemma sectionIso_restriction {R S T : Scheme.{u}}
    (f : S ⟶ R) (g : T ⟶ S) (k : T ⟶ R) (hk : g ≫ f = k)
    (F : Sheaf R.smallEtaleTopology (Type (u + 1))) :
    (sectionIso f F).hom ≫
        etaleSetSectionComparison g f k hk F (Scheme.Etale.mk (𝟙 R)) ≫
        (sectionIso k F).inv =
      ((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
        (b g) (Type (u + 1)) (S.smallGrothendieckTopology @Etale)
        (T.smallGrothendieckTopology @Etale)).unit.app
          ((L f).obj F)).hom.app (op (Scheme.Etale.mk (𝟙 S))) ≫
        (etaleSetTerminalTransport f g k hk F).inv := by
  subst k
  let c := (Classical.choose etaleSetInverseImageCompositionUnits.2.2
    R S T f g).hom.app F
  let η := ((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
    (b g) (Type (u + 1)) (S.smallGrothendieckTopology @Etale)
    (T.smallGrothendieckTopology @Etale)).unit.app ((L f).obj F)).hom
  have hn := η.naturality (terminalIso f).hom.op
  simp only [sectionIso, Functor.mapIso_hom, Functor.mapIso_inv,
    Iso.op_hom, Iso.op_inv, etaleSetSectionComparison, etaleSetTerminalTransport,
    eqToHom_refl, Iso.trans_inv, Iso.symm_inv, eqToIso_refl, Iso.refl_hom,
    Category.comp_id, ObjectProperty.FullSubcategory.id_hom, NatTrans.id_app]
  change ((L f).obj F).obj.map (terminalIso f).hom.op ≫
      η.app (op ((b f).obj (Scheme.Etale.mk (𝟙 R)))) ≫
      c.hom.app (op ((b g).obj ((b f).obj (Scheme.Etale.mk (𝟙 R))))) ≫
      ((L (g ≫ f)).obj F).obj.map _ ≫ ((L (g ≫ f)).obj F).obj.map _ =
    η.app (op (Scheme.Etale.mk (𝟙 S))) ≫
      ((L g).obj ((L f).obj F)).obj.map (terminalIso g).inv.op ≫
      c.hom.app (op (Scheme.Etale.mk (𝟙 T)))
  change ((L f).obj F).obj.map (terminalIso f).hom.op ≫
      η.app (op ((b f).obj (Scheme.Etale.mk (𝟙 R)))) =
    η.app (op (Scheme.Etale.mk (𝟙 S))) ≫
      ((L g).obj ((L f).obj F)).obj.map ((b g).map (terminalIso f).hom).op at hn
  rw [reassoc_of% hn]
  rw [reassoc_of% (c.hom.naturality ((b g).map (terminalIso f).hom).op)]
  rw [← Functor.map_comp, ← Functor.map_comp, ← op_comp, ← op_comp]
  erw [c.hom.naturality (terminalIso g).inv.op]
  congr 2
  congr 1
  apply Quiver.Hom.unop_inj
  apply (cancel_mono (terminalIso g).hom).1
  exact (MorphismProperty.Over.mkIdTerminal (P := @Etale) T).hom_ext _ _

set_option backward.isDefEq.respectTransparency false in
private lemma sectionComparison_map {R S T : Scheme.{u}}
    (f : S ⟶ R) (g : T ⟶ S) (k : T ⟶ R) (hk : g ≫ f = k)
    {F F' : Sheaf R.smallEtaleTopology (Type (u + 1))} (ψ : F ⟶ F')
    (U : R.Etale) :
    etaleSetSectionComparison g f k hk F U ≫
        ((L k).map ψ).hom.app (op ((b k).obj U)) =
      ((L f).map ψ).hom.app (op ((b f).obj U)) ≫
        etaleSetSectionComparison g f k hk F' U := by
  subst k
  let p := (MorphismProperty.Over.pullbackComp (P := @Etale) (Q := ⊤) g f).hom.app U
  let c := Classical.choose etaleSetInverseImageCompositionUnits.2.2 R S T f g
  let η := (Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
    (b g) (Type (u + 1)) (S.smallGrothendieckTopology @Etale)
    (T.smallGrothendieckTopology @Etale)).unit
  have hu := NatTrans.congr_app (congrArg (fun q ↦ q.hom)
    (η.naturality ((L f).map ψ))) (op ((b f).obj U))
  have hc := NatTrans.congr_app (congrArg (fun q ↦ q.hom)
    (c.hom.naturality ψ)) (op ((b g).obj ((b f).obj U)))
  change ((L f).map ψ).hom.app (op ((b f).obj U)) ≫
      (η.app ((L f).obj F')).hom.app (op ((b f).obj U)) =
    (η.app ((L f).obj F)).hom.app (op ((b f).obj U)) ≫
      ((L g).map ((L f).map ψ)).hom.app (op ((b g).obj ((b f).obj U))) at hu
  change ((L g).map ((L f).map ψ)).hom.app (op ((b g).obj ((b f).obj U))) ≫
      (c.hom.app F').hom.app (op ((b g).obj ((b f).obj U))) =
    (c.hom.app F).hom.app (op ((b g).obj ((b f).obj U))) ≫
      ((L (g ≫ f)).map ψ).hom.app (op ((b g).obj ((b f).obj U))) at hc
  simp only [etaleSetSectionComparison, eqToHom_refl,
    ObjectProperty.FullSubcategory.id_hom, NatTrans.id_app, Category.id_comp,
    Category.assoc]
  change (η.app ((L f).obj F)).hom.app (op ((b f).obj U)) ≫
      (c.hom.app F).hom.app (op ((b g).obj ((b f).obj U))) ≫
      ((L (g ≫ f)).obj F).obj.map p.op ≫
      ((L (g ≫ f)).map ψ).hom.app (op ((b (g ≫ f)).obj U)) =
    ((L f).map ψ).hom.app (op ((b f).obj U)) ≫
      (η.app ((L f).obj F')).hom.app (op ((b f).obj U)) ≫
      (c.hom.app F').hom.app (op ((b g).obj ((b f).obj U))) ≫
      ((L (g ≫ f)).obj F').obj.map p.op
  rw [(((L (g ≫ f)).map ψ).hom.naturality p.op)]
  erw [← reassoc_of% hc, ← reassoc_of% hu]

private noncomputable def rawMap {X : Scheme.{u}}
    {F F' : Sheaf X.smallEtaleTopology (Type (u + 1))} (ψ : F ⟶ F') :
    rawPresheaf F ⟶ rawPresheaf F' where
  app Y := ((L Y.unop.hom).map ψ).hom.app
    (op ((b Y.unop.hom).obj (Scheme.Etale.mk (𝟙 X))))
  naturality {Y Z} g := sectionComparison_map Y.unop.hom g.unop.left Z.unop.hom
    (MorphismProperty.Over.w g.unop) ψ (Scheme.Etale.mk (𝟙 X))

private noncomputable def rawEquiv {X : Scheme.{u}}
    (F : Sheaf X.smallEtaleTopology (Type (u + 1))) (Y : X.ProEt) :
    (rawPresheaf F).obj (op Y) ≃
      ((L Y.hom).obj F).obj.obj (op (Scheme.Etale.mk (𝟙 Y.left))) :=
  (sectionIso (X := X) (Y := Y.left) Y.hom F).symm.toEquiv

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency.types false in
private lemma rawEquiv_restriction {X : Scheme.{u}}
    (F : Sheaf X.smallEtaleTopology (Type (u + 1))) {Y Z : X.ProEt} (g : Z ⟶ Y)
    (s : (rawPresheaf F).obj (op Y)) :
    rawEquiv F Z ((rawPresheaf F).map g.op s) =
      (((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
        (b g.left) (Type (u + 1)) (Y.left.smallGrothendieckTopology @Etale)
        (Z.left.smallGrothendieckTopology @Etale)).unit.app
          ((L Y.hom).obj F)).hom.app (op (Scheme.Etale.mk (𝟙 Y.left))) ≫
        (etaleSetTerminalTransport Y.hom g.left Z.hom (MorphismProperty.Over.w g) F).inv)
          (rawEquiv F Y s) := by
  have hh := sectionIso_restriction (R := X) (S := Y.left) (T := Z.left)
    Y.hom g.left Z.hom (MorphismProperty.Over.w g) F
  have hh' := congrArg (fun t ↦ (sectionIso (X := X) (Y := Y.left) Y.hom F).inv ≫ t) hh
  simp only [← Category.assoc, Iso.inv_hom_id, Category.id_comp] at hh'
  change (sectionIso (X := X) (Y := Z.left) Z.hom F).inv ((rawPresheaf F).map g.op s) =
    (((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
      (b g.left) (Type (u + 1)) (Y.left.smallGrothendieckTopology @Etale)
      (Z.left.smallGrothendieckTopology @Etale)).unit.app
        ((L Y.hom).obj F)).hom.app (op (Scheme.Etale.mk (𝟙 Y.left))) ≫
      (etaleSetTerminalTransport Y.hom g.left Z.hom (MorphismProperty.Over.w g) F).inv)
        ((sectionIso (X := X) (Y := Y.left) Y.hom F).inv s)
  convert ConcreteCategory.congr_hom hh' s using 1 <;> rfl

/-- There is a functor `A` from étale sheaves to pro-étale sheaves whose sections over `Y` are
the terminal sections of the étale pullback of `F` to `Y`, compatibly with restriction and
with morphisms of sheaves. -/
theorem proEtaleComparisonSectionFunctor (X : Scheme.{u}) :
    ∃ A : Sheaf X.smallEtaleTopology (Type (u + 1)) ⥤
        Sheaf (Scheme.ProEt.topology X) (Type (u + 1)),
      ∃ e : ∀ (F : Sheaf X.smallEtaleTopology (Type (u + 1))) (Y : X.ProEt),
        (A.obj F).obj.obj (op Y) ≃
          ((Scheme.etaleSetPullback Y.hom).obj F).obj.obj
            (op (Scheme.Etale.mk (𝟙 Y.left))),
      (∀ (F : Sheaf X.smallEtaleTopology (Type (u + 1)))
        (Y Z : X.ProEt) (g : Z ⟶ Y) (s : (A.obj F).obj.obj (op Y)),
        e F Z ((A.obj F).obj.map g.op s) =
          (((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
            (MorphismProperty.Over.pullback @Etale ⊤ g.left) (Type (u + 1))
            (Y.left.smallGrothendieckTopology @Etale)
            (Z.left.smallGrothendieckTopology @Etale)).unit.app
              ((Scheme.etaleSetPullback Y.hom).obj F)).hom.app
                (op (Scheme.Etale.mk (𝟙 Y.left))) ≫
            (etaleSetTerminalTransport Y.hom g.left Z.hom (MorphismProperty.Over.w g) F).inv) (e F
              Y s)) ∧
      (∀ (F F' : Sheaf X.smallEtaleTopology (Type (u + 1))) (ψ : F ⟶ F')
        (Y : X.ProEt) (s : (A.obj F).obj.obj (op Y)),
        e F' Y ((A.map ψ).hom.app (op Y) s) =
          ((Scheme.etaleSetPullback Y.hom).map ψ).hom.app
            (op (Scheme.Etale.mk (𝟙 Y.left))) (e F Y s)) := by
  let A : Sheaf X.smallEtaleTopology (Type (u + 1)) ⥤
      Sheaf (Scheme.ProEt.topology X) (Type (u + 1)) :=
    { obj := fun F ↦ ⟨rawPresheaf F, proEtaleComparisonSectionDescent X F
        (rawPresheaf F) (rawEquiv F) (fun _ _ g s ↦ rawEquiv_restriction F g s)⟩
      map := fun ψ ↦ ⟨rawMap ψ⟩
      map_id := by
        intro F
        ext Y s
        change ((L Y.unop.hom).map (𝟙 F)).hom.app
          (op ((b Y.unop.hom).obj (Scheme.Etale.mk (𝟙 X)))) s = s
        rw [(L Y.unop.hom).map_id]
        rfl
      map_comp := by
        intro F F' F'' ψ χ
        ext Y s
        simp only [rawMap, Functor.map_comp,
          ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app] }
  refine ⟨A, rawEquiv, ?_, ?_⟩
  · intro F Y Z g s
    exact rawEquiv_restriction F g s
  · intro F F' ψ Y s
    exact ConcreteCategory.congr_hom
      (((L Y.hom).map ψ).hom.naturality (terminalIso Y.hom).inv.op).symm s

end AlgebraicGeometry
