/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Compactification.Tower
public import WeilConjectures.AlgebraicGeometry.SmoothPurity.CompactifiableCompatibleTower
public import WeilConjectures.Compactification.CategoryBaseChange

/-!
# Abstract proper/open interchange data

`A` specifies the schemes in the ambient category. All arrows below are actual
scheme morphisms, and no category or functor outside `A` is required.
The compositors accept a named composite and its equality, avoiding hidden transports.

## References

* Stacks Project, Tags 0F7C, 0F7D, 0F7J and 0F7K, the formal pasting calculus
* Stacks 0F7J, six-square diagram
* Stacks 0F7K, identity towers
-/

@[expose] public section
set_option autoImplicit false

universe u v w

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

set_option linter.checkUnivs false in
/-- Categories, proper and quasi-compact open functors, and coherent invertible interchanges on the
specified schemes. Opens are quasi-compact because the ambient arrows are finite type.
The equations are at every object and hence
are equations of natural transformations, not merely objectwise isomorphism assertions. -/
structure ProperOpenCalculus (A : Scheme.{u} → Prop) where
  obj : {X : Scheme.{u} // A X} → Type w
  [category (X : {X : Scheme.{u} // A X}) : Category.{v} (obj X)]
  P (X Y : {X : Scheme.{u} // A X}) (p : X.1 ⟶ Y.1) [IsProper p] : obj X ⥤ obj Y
  J (X Y : {X : Scheme.{u} // A X}) (j : X.1 ⟶ Y.1)
    [IsOpenImmersion j] [QuasiCompact j] : obj X ⥤ obj Y
  pId (X : {X : Scheme.{u} // A X}) : P X X (𝟙 X.1) ≅ 𝟭 (obj X)
  jId (X : {X : Scheme.{u} // A X}) : J X X (𝟙 X.1) ≅ 𝟭 (obj X)
  pComp (X Y Z : {X : Scheme.{u} // A X})
    (f : X.1 ⟶ Y.1) (g : Y.1 ⟶ Z.1) (fg : X.1 ⟶ Z.1)
    [IsProper f] [IsProper g] [IsProper fg] (_h : f ≫ g = fg) :
    P X Y f ⋙ P Y Z g ≅ P X Z fg
  pAssoc (X Y Z W : {X : Scheme.{u} // A X})
    (f : X.1 ⟶ Y.1) (g : Y.1 ⟶ Z.1) (h : Z.1 ⟶ W.1)
    (fg : X.1 ⟶ Z.1) (gh : Y.1 ⟶ W.1) (fgh : X.1 ⟶ W.1)
    [IsProper f] [IsProper g] [IsProper h]
    [IsProper fg] [IsProper gh] [IsProper fgh]
    (hfg : f ≫ g = fg) (hgh : g ≫ h = gh)
    (hl : fg ≫ h = fgh) (hr : f ≫ gh = fgh) (M : obj X) :
    (P Z W h).map ((pComp X Y Z f g fg hfg).hom.app M) ≫
        (pComp X Z W fg h fgh hl).hom.app M =
      (pComp Y Z W g h gh hgh).hom.app ((P X Y f).obj M) ≫
        (pComp X Y W f gh fgh hr).hom.app M
  pLeft (X Y : {X : Scheme.{u} // A X}) (f : X.1 ⟶ Y.1)
    [IsProper f] (M : obj X) :
    (pComp X X Y (𝟙 X.1) f f (Category.id_comp f)).hom.app M =
      (P X Y f).map ((pId X).hom.app M)
  pRight (X Y : {X : Scheme.{u} // A X}) (f : X.1 ⟶ Y.1)
    [IsProper f] (M : obj X) :
    (pComp X Y Y f (𝟙 Y.1) f (Category.comp_id f)).hom.app M =
      (pId Y).hom.app ((P X Y f).obj M)
  jComp (X Y Z : {X : Scheme.{u} // A X})
    (f : X.1 ⟶ Y.1) (g : Y.1 ⟶ Z.1) (fg : X.1 ⟶ Z.1)
    [IsOpenImmersion f] [IsOpenImmersion g] [IsOpenImmersion fg]
    [QuasiCompact f] [QuasiCompact g] [QuasiCompact fg] (_h : f ≫ g = fg) :
    J X Y f ⋙ J Y Z g ≅ J X Z fg
  jAssoc (X Y Z W : {X : Scheme.{u} // A X})
    (f : X.1 ⟶ Y.1) (g : Y.1 ⟶ Z.1) (h : Z.1 ⟶ W.1)
    (fg : X.1 ⟶ Z.1) (gh : Y.1 ⟶ W.1) (fgh : X.1 ⟶ W.1)
    [IsOpenImmersion f] [IsOpenImmersion g] [IsOpenImmersion h]
    [QuasiCompact f] [QuasiCompact g] [QuasiCompact h]
    [IsOpenImmersion fg] [IsOpenImmersion gh] [IsOpenImmersion fgh]
    [QuasiCompact fg] [QuasiCompact gh] [QuasiCompact fgh]
    (hfg : f ≫ g = fg) (hgh : g ≫ h = gh)
    (hl : fg ≫ h = fgh) (hr : f ≫ gh = fgh) (M : obj X) :
    (J Z W h).map ((jComp X Y Z f g fg hfg).hom.app M) ≫
        (jComp X Z W fg h fgh hl).hom.app M =
      (jComp Y Z W g h gh hgh).hom.app ((J X Y f).obj M) ≫
        (jComp X Y W f gh fgh hr).hom.app M
  jLeft (X Y : {X : Scheme.{u} // A X}) (f : X.1 ⟶ Y.1)
    [IsOpenImmersion f] [QuasiCompact f] (M : obj X) :
    (jComp X X Y (𝟙 X.1) f f (Category.id_comp f)).hom.app M =
      (J X Y f).map ((jId X).hom.app M)
  jRight (X Y : {X : Scheme.{u} // A X}) (f : X.1 ⟶ Y.1)
    [IsOpenImmersion f] [QuasiCompact f] (M : obj X) :
    (jComp X Y Y f (𝟙 Y.1) f (Category.comp_id f)).hom.app M =
      (jId Y).hom.app ((J X Y f).obj M)
  gamma (U V W Z : {X : Scheme.{u} // A X})
    (k : U.1 ⟶ V.1) (r : U.1 ⟶ W.1) (p : V.1 ⟶ Z.1) (i : W.1 ⟶ Z.1)
    [IsOpenImmersion k] [IsOpenImmersion i] [QuasiCompact k] [QuasiCompact i]
    [IsProper r] [IsProper p]
    (_h : k ≫ p = r ≫ i) : P U W r ⋙ J W Z i ≅ J U V k ⋙ P V Z p
  vertical (U V W Z E F : {X : Scheme.{u} // A X})
    (k : U.1 ⟶ V.1) (i : W.1 ⟶ Z.1) (j : E.1 ⟶ F.1)
    (r₁ : U.1 ⟶ W.1) (r₂ : W.1 ⟶ E.1) (p₁ : V.1 ⟶ Z.1) (p₂ : Z.1 ⟶ F.1)
    [IsOpenImmersion k] [IsOpenImmersion i] [IsOpenImmersion j]
    [QuasiCompact k] [QuasiCompact i] [QuasiCompact j]
    [IsProper r₁] [IsProper r₂] [IsProper p₁] [IsProper p₂]
    (h₁ : k ≫ p₁ = r₁ ≫ i) (h₂ : i ≫ p₂ = r₂ ≫ j)
    (h : k ≫ (p₁ ≫ p₂) = (r₁ ≫ r₂) ≫ j) (M : obj U) :
    (J E F j).map ((pComp U W E r₁ r₂ (r₁ ≫ r₂) rfl).hom.app M) ≫
        (gamma U V E F k (r₁ ≫ r₂) (p₁ ≫ p₂) j h).hom.app M ≫
        (pComp V Z F p₁ p₂ (p₁ ≫ p₂) rfl).inv.app ((J U V k).obj M) =
      (gamma W Z E F i r₂ p₂ j h₂).hom.app ((P U W r₁).obj M) ≫
        (P Z F p₂).map ((gamma U V W Z k r₁ p₁ i h₁).hom.app M)
  horizontal (U V E W Z F : {X : Scheme.{u} // A X})
    (k : U.1 ⟶ V.1) (l : V.1 ⟶ E.1) (i : W.1 ⟶ Z.1) (j : Z.1 ⟶ F.1)
    (r : U.1 ⟶ W.1) (p : V.1 ⟶ Z.1) (q : E.1 ⟶ F.1)
    [IsOpenImmersion k] [IsOpenImmersion l] [IsOpenImmersion i] [IsOpenImmersion j]
    [QuasiCompact k] [QuasiCompact l] [QuasiCompact i] [QuasiCompact j]
    [IsProper r] [IsProper p] [IsProper q]
    (h₁ : k ≫ p = r ≫ i) (h₂ : l ≫ q = p ≫ j)
    (h : (k ≫ l) ≫ q = r ≫ (i ≫ j)) (M : obj U) :
    (jComp W Z F i j (i ≫ j) rfl).hom.app ((P U W r).obj M) ≫
        (gamma U E W F (k ≫ l) r q (i ≫ j) h).hom.app M ≫
        (P E F q).map ((jComp U V E k l (k ≫ l) rfl).inv.app M) =
      (J Z F j).map ((gamma U V W Z k r p i h₁).hom.app M) ≫
        (gamma V E Z F l p q j h₂).hom.app ((J U V k).obj M)
  verticalIdentity (U V : {X : Scheme.{u} // A X}) (j : U.1 ⟶ V.1)
    [IsOpenImmersion j] [QuasiCompact j] (h : j ≫ 𝟙 V.1 = 𝟙 U.1 ≫ j) (M : obj U) :
    (gamma U V U V j (𝟙 U.1) (𝟙 V.1) j h).hom.app M ≫
        (pId V).hom.app ((J U V j).obj M) =
      (J U V j).map ((pId U).hom.app M)
  horizontalIdentity (U V : {X : Scheme.{u} // A X}) (p : U.1 ⟶ V.1)
    [IsProper p] (h : (𝟙 U.1) ≫ p = p ≫ 𝟙 V.1) (M : obj U) :
    (gamma U U V V (𝟙 U.1) p p (𝟙 V.1) h).hom.app M ≫
        (P U V p).map ((jId U).hom.app M) =
      (jId V).hom.app ((P U V p).obj M)

namespace ProperOpenCalculus

attribute [instance] category

variable {A : Scheme.{u} → Prop} (F : ProperOpenCalculus.{u, v, w} A)

/-- The specified open/proper composite, not an independently chosen shriek functor. -/
def H (X Y : {X : Scheme.{u} // A X}) {f : X.1 ⟶ Y.1}
    (c : Compactification f) (hc : A c.Z) [QuasiCompact f] : F.obj X ⥤ F.obj Y :=
  letI : QuasiCompact c.i := c.quasiCompact_openImmersion inferInstance
  F.J X ⟨c.Z, hc⟩ c.i ⋙ F.P ⟨c.Z, hc⟩ Y c.g

/-- Refinement comparison: insert the proper identity, apply the specified gamma,
then compose the proper functors. No cartesian hypothesis is imposed on the refinement. -/
def rho (X Y : {X : Scheme.{u} // A X}) {f : X.1 ⟶ Y.1}
    {c d : Compactification f} (hc : A c.Z) (hd : A d.Z) (r : d.Refinement c) [QuasiCompact f] :
    F.H X Y c hc ≅ F.H X Y d hd :=
  letI : QuasiCompact c.i := c.quasiCompact_openImmersion inferInstance
  letI : QuasiCompact d.i := d.quasiCompact_openImmersion inferInstance
  Functor.isoWhiskerRight
    ((Functor.leftUnitor (F.J X ⟨c.Z, hc⟩ c.i)).symm ≪≫
      Functor.isoWhiskerRight (F.pId X).symm (F.J X ⟨c.Z, hc⟩ c.i) ≪≫
      F.gamma X ⟨d.Z, hd⟩ X ⟨c.Z, hc⟩ d.i (𝟙 X.1) r.hom c.i
        (r.i_hom.trans (Category.id_comp c.i).symm)) (F.P ⟨c.Z, hc⟩ Y c.g) ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (F.J X ⟨d.Z, hd⟩ d.i)
      (F.pComp ⟨d.Z, hd⟩ ⟨c.Z, hc⟩ Y r.hom c.g d.g r.hom_g)

/-- Comparison from `c₂` to `c₁` computed on a supplied common refinement. -/
def compare (X Y : {X : Scheme.{u} // A X}) {f : X.1 ⟶ Y.1}
    {c₁ c₂ d : Compactification f} (h₁ : A c₁.Z) (h₂ : A c₂.Z) (hd : A d.Z)
    (r₁ : d.Refinement c₁) (r₂ : d.Refinement c₂) [QuasiCompact f] :
    F.H X Y c₂ h₂ ≅ F.H X Y c₁ h₁ :=
  F.rho X Y h₂ hd r₂ ≪≫ (F.rho X Y h₁ hd r₁).symm

/-- The ambient membership certificates of a compatible binary tower. -/
def TriangleObjects {X Y Z : Scheme.{u}} {f : X ⟶ Y} {g : Y ⟶ Z}
    (T : Compactification.Triangle f g) : Prop :=
  A T.cf.Z ∧ A T.cg.Z ∧ A T.cfg.Z

/-- A refining tower has arbitrary proper refinements, with the two ambient compatibility
squares; no additional cartesianness over X or Y is required. -/
structure TowerRefinement {X Y Z : Scheme.{u}} {f : X ⟶ Y} {g : Y ⟶ Z}
    (T' T : Compactification.Triangle f g) where
  rf : T'.cf.Refinement T.cf
  rg : T'.cg.Refinement T.cg
  rfg : T'.cfg.Refinement T.cfg
  q_comm : T'.q ≫ rfg.hom = rf.hom ≫ T.q
  p_comm : rfg.hom ≫ T.p = T'.p ≫ rg.hom

/-- The tower transformation is gamma whiskered by the outside proper/open functors,
followed by the open and proper compositors. -/
def towerIso (X Y Z : {X : Scheme.{u} // A X})
    {f : X.1 ⟶ Y.1} {g : Y.1 ⟶ Z.1} (T : Compactification.Triangle f g)
    (hT : TriangleObjects (A := A) T) [QuasiCompact f] [QuasiCompact g] :
    F.H X Y T.cf hT.1 ⋙ F.H Y Z T.cg hT.2.1 ≅ F.H X Z T.cfg hT.2.2 :=
  letI : QuasiCompact T.cf.i := T.cf.quasiCompact_openImmersion inferInstance
  letI : QuasiCompact T.cg.i := T.cg.quasiCompact_openImmersion inferInstance
  letI : QuasiCompact T.cfg.i := T.cfg.quasiCompact_openImmersion inferInstance
  letI : QuasiCompact T.q :=
    MorphismProperty.of_isPullback T.isPullback (inferInstance : QuasiCompact T.cg.i)
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (F.J X ⟨T.cf.Z, hT.1⟩ T.cf.i)
      ((Functor.associator _ _ _).symm ≪≫
        Functor.isoWhiskerRight
          (F.gamma ⟨T.cf.Z, hT.1⟩ ⟨T.cfg.Z, hT.2.2⟩ Y ⟨T.cg.Z, hT.2.1⟩
            T.q T.cf.g T.p T.cg.i T.isPullback.w.symm)
          (F.P ⟨T.cg.Z, hT.2.1⟩ Z T.cg.g) ≪≫ Functor.associator _ _ _) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight
      (F.jComp X ⟨T.cf.Z, hT.1⟩ ⟨T.cfg.Z, hT.2.2⟩ T.cf.i T.q T.cfg.i T.i_q)
      (F.P ⟨T.cfg.Z, hT.2.2⟩ ⟨T.cg.Z, hT.2.1⟩ T.p ⋙
        F.P ⟨T.cg.Z, hT.2.1⟩ Z T.cg.g) ≪≫
    Functor.isoWhiskerLeft (F.J X ⟨T.cfg.Z, hT.2.2⟩ T.cfg.i)
      (F.pComp ⟨T.cfg.Z, hT.2.2⟩ ⟨T.cg.Z, hT.2.1⟩ Z T.p T.cg.g T.cfg.g T.p_g)

/-- The six ambient schemes of a three-map staircase belong to the specified category. -/
def TowerObjects {X Y Z W : Scheme.{u}} {f : X ⟶ Y} {g : Y ⟶ Z} {h : Z ⟶ W}
    (T : Compactification.Tower f g h) : Prop :=
  A T.cf.Z ∧ A T.cg.Z ∧ A T.ch.Z ∧ A T.cfg.Z ∧ A T.cgh.Z ∧ A T.cfgh.Z

/-- The identification of the trivial identity compactification with the identity functor. -/
def identityIso (X : {X : Scheme.{u} // A X}) :
    F.H X X (Compactification.ofIsProper (𝟙 X.1)) X.2 ≅ 𝟭 (F.obj X) :=
  Functor.isoWhiskerRight (F.jId X) (F.P X X (𝟙 X.1)) ≪≫
    Functor.leftUnitor _ ≪≫ F.pId X

/-- Precisely the assumed geometric existence: cofiltered compactifications inside A,
common refining binary towers, and compatible three-map staircases. These are hypotheses,
not consequences of the proper/open axioms. -/
structure Geometry (A : Scheme.{u} → Prop) : Prop where
  nonempty (X Y : {X : Scheme.{u} // A X}) (f : X.1 ⟶ Y.1)
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f] :
    ∃ c : Compactification f, A c.Z
  common (X Y : {X : Scheme.{u} // A X}) (f : X.1 ⟶ Y.1)
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (c d : Compactification f) (_hc : A c.Z) (_hd : A d.Z) :
    ∃ e : Compactification f, A e.Z ∧ Nonempty (e.Refinement c) ∧ Nonempty (e.Refinement d)
  equalize (X Y : {X : Scheme.{u} // A X}) (f : X.1 ⟶ Y.1)
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (c d : Compactification f) (_hc : A c.Z) (_hd : A d.Z) (r s : c.Refinement d) :
    ∃ (e : Compactification f) (_he : A e.Z) (t : e.Refinement c), t.comp r = t.comp s
  compatible (X Y Z : {X : Scheme.{u} // A X})
    (f : X.1 ⟶ Y.1) (g : Y.1 ⟶ Z.1)
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    [IsSeparated g] [LocallyOfFiniteType g] [QuasiCompact g]
    (d : Compactification g) (c : Compactification (f ≫ g)) (_hd : A d.Z) (_hc : A c.Z) :
    ∃ (T : Compactification.Triangle f g), TriangleObjects (A := A) T ∧
      T.cg = d ∧ Nonempty (T.cfg.Refinement c)
  towers (X Y Z : {X : Scheme.{u} // A X}) (f : X.1 ⟶ Y.1) (g : Y.1 ⟶ Z.1)
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    [IsSeparated g] [LocallyOfFiniteType g] [QuasiCompact g]
    (T S : Compactification.Triangle f g)
    (_hT : TriangleObjects (A := A) T) (_hS : TriangleObjects (A := A) S) :
    ∃ (R : Compactification.Triangle f g), TriangleObjects (A := A) R ∧
      Nonempty (TowerRefinement R T) ∧ Nonempty (TowerRefinement R S)
  staircases (X Y Z W : {X : Scheme.{u} // A X})
    (f : X.1 ⟶ Y.1) (g : Y.1 ⟶ Z.1) (h : Z.1 ⟶ W.1)
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    [IsSeparated g] [LocallyOfFiniteType g] [QuasiCompact g]
    [IsSeparated h] [LocallyOfFiniteType h] [QuasiCompact h] :
    ∃ T : Compactification.Tower f g h, TowerObjects (A := A) T

end ProperOpenCalculus
end AlgebraicGeometry
