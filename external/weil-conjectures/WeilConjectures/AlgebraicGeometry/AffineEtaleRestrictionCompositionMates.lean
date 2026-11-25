/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.FullAffineEtaleTopos
public import WeilConjectures.AlgebraicGeometry.EtaleSheaves
public import Mathlib.AlgebraicGeometry.Morphisms.Affine
import Mathlib.CategoryTheory.Adjunction.Mates

/-! # Affine étale inverse-image composition coherence -/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- Source: Stacks Project, Sites 03CB and 03CC, Categories 0B65.
(blueprint: lem-weil-pbc-affine-etale-restriction-composition-mates)
Proof: precomposition by gamma gives a right-adjoint isomorphism. Compose a_f and a_g,
then take the mate of that isomorphism to construct d. The mate unit equation, evaluated
at V and s, is the first conclusion. For coherence let E be e_g followed by L_g(e_f).
Precompose both routes by E inverse and transpose with the composed affine adjunction.
The equations he and hc turn the iterated units into the composite full-site unit;
hgamma identifies the base-change restrictions and he for gf identifies the affine
composite unit. Thus both transposes equal the transpose of d at every V and s.
Injectivity of transposition and cancellation of E inverse give the second conclusion. -/
theorem affineEtale_restriction_composition_mates
    (U : ∀ {X Y : Scheme.{u}} (h : Y ⟶ X) [IsAffineHom h],
        X.FullAffineEtale ⥤ Y.FullAffineEtale)
      (t : ∀ {X Y : Scheme.{u}} (h : Y ⟶ X) [IsAffineHom h],
        U h ⋙ fullAffineEtaleInclusion Y ≅
          fullAffineEtaleInclusion X ⋙ (MorphismProperty.Over.pullback @Etale ⊤ h))
    [hu : ∀ (X Y : Scheme.{u}) (h : Y ⟶ X) [IsAffineHom h],
      (U h).IsContinuous (fullAffineEtaleTopology X) (fullAffineEtaleTopology Y)]
    (L : ∀ {X Y : Scheme.{u}} (h : Y ⟶ X) [IsAffineHom h],
        Sheaf (fullAffineEtaleTopology X) (Type (u + 1)) ⥤
          Sheaf (fullAffineEtaleTopology Y) (Type (u + 1)))
      (a : ∀ {X Y : Scheme.{u}} (h : Y ⟶ X) [IsAffineHom h],
        L h ⊣ (U h).sheafPushforwardContinuous (Type (u + 1))
          (fullAffineEtaleTopology X) (fullAffineEtaleTopology Y))
    (e : ∀ {X Y : Scheme.{u}} (h : Y ⟶ X) [IsAffineHom h],
        etaleSetPullback h ⋙ ((fullAffineEtaleInclusion Y).sheafPushforwardContinuous (Type (u + 1))
          (fullAffineEtaleTopology Y) Y.smallEtaleTopology) ≅
          ((fullAffineEtaleInclusion X).sheafPushforwardContinuous (Type (u + 1))
          (fullAffineEtaleTopology X) X.smallEtaleTopology) ⋙ L h)
    (he : (∀ (X Y : Scheme.{u}) (h : Y ⟶ X) [IsAffineHom h]
      (G : Sheaf X.smallEtaleTopology (Type (u + 1)))
      (V : X.FullAffineEtale) (s : G.obj.obj (op V.obj)),
      ((e h).hom.app G).hom.app (op ((U h).obj V))
          (((etaleSetPullback h).obj G).obj.map ((t h).hom.app V).op
            ((((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
          (MorphismProperty.Over.pullback @Etale ⊤ h) (Type (u + 1))
          (X.smallGrothendieckTopology @Etale) (Y.smallGrothendieckTopology @Etale)).unit).app
          G).hom.app (op V.obj) s)) =
        ((a h).unit.app (((fullAffineEtaleInclusion X).sheafPushforwardContinuous (Type (u + 1))
          (fullAffineEtaleTopology X) X.smallEtaleTopology).obj G)).hom.app (op V) s))
    (c : ∀ {X Y Z : Scheme.{u}} (f : Y ⟶ X) (g : Z ⟶ Y)
        [IsAffineHom f] [IsAffineHom g],
        etaleSetPullback f ⋙ etaleSetPullback g ≅ etaleSetPullback (g ≫ f))
    (hc : (∀ (X Y Z : Scheme.{u}) (f : Y ⟶ X) (g : Z ⟶ Y)
      [IsAffineHom f] [IsAffineHom g]
      (G : Sheaf X.smallEtaleTopology (Type (u + 1)))
      (V : X.Etale) (s : G.obj.obj (op V)),
      ((c f g).hom.app G).hom.app (op ((MorphismProperty.Over.pullback @Etale ⊤ g).obj
          ((MorphismProperty.Over.pullback @Etale ⊤ f).obj V)))
        ((((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
          (MorphismProperty.Over.pullback @Etale ⊤ g) (Type (u + 1))
          (Y.smallGrothendieckTopology @Etale) (Z.smallGrothendieckTopology @Etale)).unit).app
          ((etaleSetPullback f).obj G)).hom.app
          (op ((MorphismProperty.Over.pullback @Etale ⊤ f).obj V))
          ((((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
          (MorphismProperty.Over.pullback @Etale ⊤ f) (Type (u + 1))
          (X.smallGrothendieckTopology @Etale) (Y.smallGrothendieckTopology @Etale)).unit).app
          G).hom.app (op V) s)) =
        ((etaleSetPullback (g ≫ f)).obj G).obj.map
          ((MorphismProperty.Over.pullbackComp (P := @Etale) (Q := ⊤) g f).inv.app V).op
          ((((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
          (MorphismProperty.Over.pullback @Etale ⊤ (g ≫ f)) (Type (u + 1))
          (X.smallGrothendieckTopology @Etale) (Z.smallGrothendieckTopology @Etale)).unit).app
          G).hom.app (op V) s)))
    (gamma : ∀ {X Y Z : Scheme.{u}} (f : Y ⟶ X) (g : Z ⟶ Y)
        [IsAffineHom f] [IsAffineHom g], U f ⋙ U g ≅ U (g ≫ f))
    (hgamma : (∀ (X Y Z : Scheme.{u}) (f : Y ⟶ X) (g : Z ⟶ Y)
      [IsAffineHom f] [IsAffineHom g] (V : X.FullAffineEtale),
      (fullAffineEtaleInclusion Z).map ((gamma f g).hom.app V) ≫ (t (g ≫ f)).hom.app V =
        (t g).hom.app ((U f).obj V) ≫
          (MorphismProperty.Over.pullback @Etale ⊤ g).map ((t f).hom.app V) ≫
          (MorphismProperty.Over.pullbackComp (P := @Etale) (Q := ⊤) g f).inv.app V.obj)) :
    ∃ (d : ∀ {X Y Z : Scheme.{u}} (f : Y ⟶ X) (g : Z ⟶ Y)
        [IsAffineHom f] [IsAffineHom g], L f ⋙ L g ≅ L (g ≫ f)),
   (∀ (X Y Z : Scheme.{u}) (f : Y ⟶ X) (g : Z ⟶ Y)
      [IsAffineHom f] [IsAffineHom g]
      (F : Sheaf (fullAffineEtaleTopology X) (Type (u + 1)))
      (V : X.FullAffineEtale) (s : F.obj.obj (op V)),
      ((d f g).hom.app F).hom.app (op ((U g).obj ((U f).obj V)))
          (((a g).unit.app ((L f).obj F)).hom.app (op ((U f).obj V))
            (((a f).unit.app F).hom.app (op V) s)) =
        ((L (g ≫ f)).obj F).obj.map ((gamma f g).hom.app V).op
          (((a (g ≫ f)).unit.app F).hom.app (op V) s)) ∧
    (∀ (X Y Z : Scheme.{u}) (f : Y ⟶ X) (g : Z ⟶ Y)
      [IsAffineHom f] [IsAffineHom g]
      (G : Sheaf X.smallEtaleTopology (Type (u + 1))),
      ((fullAffineEtaleInclusion Z).sheafPushforwardContinuous (Type (u + 1))
          (fullAffineEtaleTopology Z) Z.smallEtaleTopology).map ((c f g).hom.app G) ≫
          (e (g ≫ f)).hom.app G =
        (e g).hom.app ((etaleSetPullback f).obj G) ≫
          (L g).map ((e f).hom.app G) ≫ (d f g).hom.app (((fullAffineEtaleInclusion
          X).sheafPushforwardContinuous (Type (u + 1))
          (fullAffineEtaleTopology X) X.smallEtaleTopology).obj G)) := by
  let d : ∀ {X Y Z : Scheme.{u}} (f : Y ⟶ X) (g : Z ⟶ Y)
      [IsAffineHom f] [IsAffineHom g], L f ⋙ L g ≅ L (g ≫ f) :=
    fun {X Y Z} f g ↦
      (conjugateIsoEquiv (a (g ≫ f)) ((a f).comp (a g))).symm
        ((Functor.sheafPushforwardContinuousComp' (gamma f g) (Type (u + 1))
          (fullAffineEtaleTopology X) (fullAffineEtaleTopology Y)
          (fullAffineEtaleTopology Z)).symm)
  have hd : ∀ (X Y Z : Scheme.{u}) (f : Y ⟶ X) (g : Z ⟶ Y)
      [IsAffineHom f] [IsAffineHom g]
      (F : Sheaf (fullAffineEtaleTopology X) (Type (u + 1)))
      (V : X.FullAffineEtale) (s : F.obj.obj (op V)),
      ((d f g).hom.app F).hom.app (op ((U g).obj ((U f).obj V)))
          (((a g).unit.app ((L f).obj F)).hom.app (op ((U f).obj V))
            (((a f).unit.app F).hom.app (op V) s)) =
        ((L (g ≫ f)).obj F).obj.map ((gamma f g).hom.app V).op
          (((a (g ≫ f)).unit.app F).hom.app (op V) s) := by
    intro X Y Z f g _ _ F V s
    have h := unit_conjugateEquiv_symm (a (g ≫ f)) ((a f).comp (a g))
      (Functor.sheafPushforwardContinuousComp' (gamma f g) (Type (u + 1))
        (fullAffineEtaleTopology X) (fullAffineEtaleTopology Y)
        (fullAffineEtaleTopology Z)).inv F
    rw [Adjunction.comp_unit_app] at h
    have h' := congrArg (fun k ↦ k.hom.app (op V) s) h
    exact h'.symm
  refine ⟨d, hd, ?_⟩
  intro X Y Z f g _ _ G
  let R (X : Scheme.{u}) := (fullAffineEtaleInclusion X).sheafPushforwardContinuous
    (Type (u + 1)) (fullAffineEtaleTopology X) X.smallEtaleTopology
  let η {X Y : Scheme.{u}} (h : Y ⟶ X) :=
    (Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
      (MorphismProperty.Over.pullback @Etale ⊤ h) (Type (u + 1))
      (X.smallGrothendieckTopology @Etale) (Y.smallGrothendieckTopology @Etale)).unit
  let E := (e g).app ((etaleSetPullback f).obj G) ≪≫
    (L g).mapIso ((e f).app G)
  have hE (V : X.FullAffineEtale) (s : G.obj.obj (op V.obj)) :
      E.hom.hom.app (op ((U g).obj ((U f).obj V)))
        (((etaleSetPullback g).obj ((etaleSetPullback f).obj G)).obj.map
          ((t g).hom.app ((U f).obj V)).op
          (((η g).app ((etaleSetPullback f).obj G)).hom.app (op ((U f).obj V).obj)
            (((etaleSetPullback f).obj G).obj.map ((t f).hom.app V).op
              (((η f).app G).hom.app (op V.obj) s)))) =
      (((a f).comp (a g)).unit.app ((R X).obj G)).hom.app (op V) s := by
    dsimp only [E, Iso.trans_hom, Functor.mapIso_hom]
    rw [Adjunction.comp_unit_app]
    change ((L g).map ((e f).hom.app G)).hom.app _
      (((e g).hom.app _).hom.app _ _) = _
    rw [he Y Z g]
    have hn := (a g).unit.naturality ((e f).hom.app G)
    have hn' := congrArg (fun k ↦ k.hom.app (op ((U f).obj V))
      (((etaleSetPullback f).obj G).obj.map ((t f).hom.app V).op
        (((η f).app G).hom.app (op V.obj) s))) hn
    dsimp only [Functor.id_map, Functor.comp_map] at hn'
    change ((a g).unit.app ((L f).obj ((R X).obj G))).hom.app _
      (((e f).hom.app G).hom.app _ _) =
      ((L g).map ((e f).hom.app G)).hom.app _
        (((a g).unit.app ((R Y).obj ((etaleSetPullback f).obj G))).hom.app _ _) at hn'
    exact hn'.symm.trans (congrArg
      (fun z ↦ ((a g).unit.app ((L f).obj ((R X).obj G))).hom.app
        (op ((U f).obj V)) z) (he X Y f G V s))
  have hC (V : X.FullAffineEtale) (s : G.obj.obj (op V.obj)) :
      (((R Z).map ((c f g).hom.app G) ≫ (e (g ≫ f)).hom.app G).hom.app
        (op ((U g).obj ((U f).obj V))))
        (((etaleSetPullback g).obj ((etaleSetPullback f).obj G)).obj.map
          ((t g).hom.app ((U f).obj V)).op
          (((η g).app ((etaleSetPullback f).obj G)).hom.app (op ((U f).obj V).obj)
            (((etaleSetPullback f).obj G).obj.map ((t f).hom.app V).op
              (((η f).app G).hom.app (op V.obj) s)))) =
      ((L (g ≫ f)).obj ((R X).obj G)).obj.map ((gamma f g).hom.app V).op
        (((a (g ≫ f)).unit.app ((R X).obj G)).hom.app (op V) s) := by
    let Pf := MorphismProperty.Over.pullback @Etale ⊤ f
    let Pg := MorphismProperty.Over.pullback @Etale ⊤ g
    let H := (etaleSetPullback g).obj ((etaleSetPullback f).obj G)
    let K := (etaleSetPullback (g ≫ f)).obj G
    let q := (((η f).app G).hom.app (op V.obj) s)
    let w := ((η g).app ((etaleSetPullback f).obj G)).hom.app (op (Pf.obj V.obj)) q
    let α := (t g).hom.app ((U f).obj V) ≫ Pg.map ((t f).hom.app V)
    let β := (MorphismProperty.Over.pullbackComp (P := @Etale) (Q := ⊤) g f).inv.app V.obj
    have hn := ((η g).app ((etaleSetPullback f).obj G)).hom.naturality
      ((t f).hom.app V).op
    have hn' := (congrArg (fun k ↦ k q) hn).symm
    change H.obj.map (Pg.map ((t f).hom.app V)).op w =
      ((η g).app ((etaleSetPullback f).obj G)).hom.app (op ((U f).obj V).obj)
        (((etaleSetPullback f).obj G).obj.map ((t f).hom.app V).op q) at hn'
    have hcn := ((c f g).hom.app G).hom.naturality α.op
    have hcn' := (congrArg (fun k ↦ k w) hcn).symm
    change K.obj.map α.op (((c f g).hom.app G).hom.app (op (Pg.obj (Pf.obj V.obj))) w) =
      ((c f g).hom.app G).hom.app (op ((U g).obj ((U f).obj V)).obj)
        (H.obj.map α.op w) at hcn'
    have hcc := hc X Y Z f g G V.obj s
    change ((c f g).hom.app G).hom.app (op (Pg.obj (Pf.obj V.obj))) w =
      K.obj.map β.op (((η (g ≫ f)).app G).hom.app (op V.obj) s) at hcc
    have hg := hgamma X Y Z f g V
    have hen := ((e (g ≫ f)).hom.app G).hom.naturality ((gamma f g).hom.app V).op
    let z := ((η (g ≫ f)).app G).hom.app (op V.obj) s
    let ea := ((e (g ≫ f)).hom.app G).hom.app (op ((U g).obj ((U f).obj V)))
    let ca := ((c f g).hom.app G).hom.app (op ((U g).obj ((U f).obj V)).obj)
    change ea (ca (H.obj.map ((t g).hom.app ((U f).obj V)).op
      (((η g).app ((etaleSetPullback f).obj G)).hom.app (op ((U f).obj V).obj)
        (((etaleSetPullback f).obj G).obj.map ((t f).hom.app V).op q)))) = _
    refine (congrArg (fun x ↦ ea (ca (H.obj.map
      ((t g).hom.app ((U f).obj V)).op x))) hn'.symm).trans ?_
    have hm : H.obj.map α.op w =
        H.obj.map ((t g).hom.app ((U f).obj V)).op
          (H.obj.map (Pg.map ((t f).hom.app V)).op w) := by
      exact congrArg (fun k ↦ k w) (H.obj.map_comp
        (Pg.map ((t f).hom.app V)).op ((t g).hom.app ((U f).obj V)).op)
    refine (congrArg (fun x ↦ ea (ca x)) hm.symm).trans ?_
    refine (congrArg (fun x ↦ ea x) hcn'.symm).trans ?_
    refine (congrArg (fun x ↦ ea (K.obj.map α.op x)) hcc).trans ?_
    have hmap : K.obj.map α.op (K.obj.map β.op z) =
        K.obj.map (α ≫ β).op z :=
      (congrArg (fun k ↦ k z) (K.obj.map_comp β.op α.op)).symm
    refine (congrArg (fun x ↦ ea x) hmap).trans ?_
    have hg' : α ≫ β =
        (fullAffineEtaleInclusion Z).map ((gamma f g).hom.app V) ≫
          (t (g ≫ f)).hom.app V := by
      simpa only [α, β, Category.assoc] using hg.symm
    refine (congrArg (fun k ↦ ea (K.obj.map k.op z)) hg').trans ?_
    have hmap' := congrArg (fun k ↦ k z) (K.obj.map_comp
      ((t (g ≫ f)).hom.app V).op
      ((fullAffineEtaleInclusion Z).map ((gamma f g).hom.app V)).op)
    refine (congrArg (fun x ↦ ea x) hmap').trans ?_
    have hen' := congrArg (fun k ↦ k (K.obj.map ((t (g ≫ f)).hom.app V).op z)) hen
    refine hen'.trans ?_
    exact congrArg (fun x ↦
      ((L (g ≫ f)).obj ((R X).obj G)).obj.map ((gamma f g).hom.app V).op x)
      (he X Z (g ≫ f) G V s)
  apply (cancel_epi E.inv).mp
  change E.inv ≫ ((R Z).map ((c f g).hom.app G) ≫ (e (g ≫ f)).hom.app G) =
    E.inv ≫ E.hom ≫ (d f g).hom.app ((R X).obj G)
  rw [Iso.inv_hom_id_assoc]
  apply (((a f).comp (a g)).homEquiv _ _).injective
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
  ext V s
  obtain ⟨V⟩ := V
  have h := hE V s
  have h' := congrArg (fun z ↦ E.inv.hom.app
    (op ((U g).obj ((U f).obj V))) z) h
  have hi := congrArg (fun k ↦ k.hom.app
    (op ((U g).obj ((U f).obj V)))
      (((etaleSetPullback g).obj ((etaleSetPullback f).obj G)).obj.map
        ((t g).hom.app ((U f).obj V)).op
        (((η g).app ((etaleSetPullback f).obj G)).hom.app (op ((U f).obj V).obj)
          (((etaleSetPullback f).obj G).obj.map ((t f).hom.app V).op
            (((η f).app G).hom.app (op V.obj) s))))) E.hom_inv_id
  dsimp only at hi
  have hInv := h'.symm.trans hi
  dsimp only at hInv
  change (((R Z).map ((c f g).hom.app G) ≫ (e (g ≫ f)).hom.app G).hom.app
    (op ((U g).obj ((U f).obj V))))
      (E.inv.hom.app (op ((U g).obj ((U f).obj V)))
        ((((a f).comp (a g)).unit.app ((R X).obj G)).hom.app (op V) s)) =
    ((d f g).hom.app ((R X).obj G)).hom.app (op ((U g).obj ((U f).obj V)))
      ((((a f).comp (a g)).unit.app ((R X).obj G)).hom.app (op V) s)
  exact (congrArg (fun z ↦
      (((R Z).map ((c f g).hom.app G) ≫ (e (g ≫ f)).hom.app G).hom.app
        (op ((U g).obj ((U f).obj V)))) z) hInv).trans
    ((hC V s).trans (hd X Y Z f g ((R X).obj G) V s).symm)

end AlgebraicGeometry.Scheme
