import Langlands.AbelianScheme.BaseChangeCoherence
import Mathlib.CategoryTheory.Action.Basic
import Mathlib.CategoryTheory.InducedCategory

/-! # Actual abelian schemes with rational algebra action -/

noncomputable section
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory AlgebraicGeometry

universe u v

namespace Langlands.AbelianScheme

/-- An actual abelian scheme and a unital rational algebra action on it. -/
structure RationalAlgebraActionData (S : Scheme.{u}) (D : Type v)
    [Ring D] [Algebra ℚ D] where
  abelianScheme : AbelianScheme S
  action : D →ₐ[ℚ] End0 abelianScheme

/-- Retain the actual rationalized object and the multiplicative part of its action. -/
def RationalAlgebraActionData.toAction {S : Scheme.{u}} {D : Type v}
    [Ring D] [Algebra ℚ D] (X : RationalAlgebraActionData S D) :
    Action (RationalCategory S) D where
  V := Rationalization.of X.abelianScheme
  ρ := X.action.toMonoidHom

/-- The category of actual abelian schemes with rational algebra action.
Morphisms are actual rational homomorphisms intertwining every algebra element. -/
abbrev RationalAlgebraAction (S : Scheme.{u}) (D : Type v)
    [Ring D] [Algebra ℚ D] :=
  InducedCategory (Action (RationalCategory S) D)
    (RationalAlgebraActionData.toAction (S := S) (D := D))

namespace RationalAlgebraAction

variable {S S' S'' : Scheme.{u}} {D : Type v} [Ring D] [Algebra ℚ D]

/-- Bundle an actual abelian scheme equipped with an actual rational algebra map. -/
def of (A : AbelianScheme S) (i : D →ₐ[ℚ] End0 A) : RationalAlgebraAction S D :=
  ⟨A, i⟩

/-- Forget the algebra action, retaining the actual rationalized abelian scheme. -/
def forget (S : Scheme.{u}) (D : Type v) [Ring D] [Algebra ℚ D] :
    RationalAlgebraAction S D ⥤ RationalCategory S :=
  inducedFunctor RationalAlgebraActionData.toAction ⋙ Action.forget _ _

instance : (forget S D).Faithful := inferInstanceAs
  (inducedFunctor RationalAlgebraActionData.toAction ⋙ Action.forget _ _).Faithful

/-- The actual rational homomorphism underlying an equivariant morphism. -/
def hom0 {X Y : RationalAlgebraAction S D} (f : X ⟶ Y) :
    Hom0 X.abelianScheme Y.abelianScheme :=
  f.hom.hom

@[ext] theorem hom_ext {X Y : RationalAlgebraAction S D}
    {f g : X ⟶ Y} (h : hom0 f = hom0 g) : f = g :=
  InducedCategory.hom_ext (Action.hom_ext _ _ h)

/-- The defining equivariance equation, in actual rational Hom groups. -/
theorem intertwines {X Y : RationalAlgebraAction S D} (f : X ⟶ Y) (d : D) :
    comp0 _ _ _ (X.action d) (hom0 f) = comp0 _ _ _ (hom0 f) (Y.action d) :=
  f.hom.comm d

/-- Construct an equivariant morphism from an intertwining actual rational map. -/
def homMk {X Y : RationalAlgebraAction S D}
    (f : Hom0 X.abelianScheme Y.abelianScheme)
    (hf : ∀ d : D, comp0 _ _ _ (X.action d) f = comp0 _ _ _ f (Y.action d)) :
    X ⟶ Y :=
  InducedCategory.homMk { hom := f, comm := hf }

@[simp] theorem hom0_homMk {X Y : RationalAlgebraAction S D}
    (f : Hom0 X.abelianScheme Y.abelianScheme)
    (hf : ∀ d : D, comp0 _ _ _ (X.action d) f = comp0 _ _ _ f (Y.action d)) :
    hom0 (homMk f hf) = f := rfl

@[simp] theorem hom0_id (X : RationalAlgebraAction S D) :
    hom0 (𝟙 X) = id0 X.abelianScheme := rfl

@[simp] theorem hom0_comp {X Y Z : RationalAlgebraAction S D}
    (f : X ⟶ Y) (g : Y ⟶ Z) :
    hom0 (f ≫ g) = comp0 _ _ _ (hom0 f) (hom0 g) := rfl

@[simp] theorem forget_map {X Y : RationalAlgebraAction S D} (f : X ⟶ Y) :
    (forget S D).map f = hom0 f := rfl

/-- An equivariant isomorphism is in particular an actual rational isomorphism. -/
def underlyingIso {X Y : RationalAlgebraAction S D} (e : X ≅ Y) :
    Rationalization.of X.abelianScheme ≅ Rationalization.of Y.abelianScheme :=
  (forget S D).mapIso e

@[simp] theorem underlyingIso_hom {X Y : RationalAlgebraAction S D} (e : X ≅ Y) :
    (underlyingIso e).hom = hom0 e.hom := rfl

@[simp] theorem underlyingIso_inv {X Y : RationalAlgebraAction S D} (e : X ≅ Y) :
    (underlyingIso e).inv = hom0 e.inv := rfl

/-- An actual rational isomorphism whose forward map intertwines the actions
has an equivariant inverse, obtained from its actual inverse equations. -/
def isoMk {X Y : RationalAlgebraAction S D}
    (e : Rationalization.of X.abelianScheme ≅ Rationalization.of Y.abelianScheme)
    (he : ∀ d : D, comp0 _ _ _ (X.action d) e.hom =
      comp0 _ _ _ e.hom (Y.action d)) : X ≅ Y :=
  InducedCategory.isoMk (Action.mkIso e he)

@[simp] theorem hom0_isoMk_hom {X Y : RationalAlgebraAction S D}
    (e : Rationalization.of X.abelianScheme ≅ Rationalization.of Y.abelianScheme)
    (he : ∀ d : D, comp0 _ _ _ (X.action d) e.hom =
      comp0 _ _ _ e.hom (Y.action d)) :
    hom0 (isoMk e he).hom = e.hom := rfl

@[simp] theorem hom0_isoMk_inv {X Y : RationalAlgebraAction S D}
    (e : Rationalization.of X.abelianScheme ≅ Rationalization.of Y.abelianScheme)
    (he : ∀ d : D, comp0 _ _ _ (X.action d) e.hom =
      comp0 _ _ _ e.hom (Y.action d)) :
    hom0 (isoMk e he).inv = e.inv := rfl

/-- The actual pulled-back abelian scheme with its induced rational algebra action. -/
def pullbackObj (b : S' ⟶ S) (X : RationalAlgebraAction S D) :
    RationalAlgebraAction S' D :=
  of ((baseChange b).obj X.abelianScheme)
    ((rationalBaseChangeEnd b X.abelianScheme).comp X.action)

/-- Pullback of an equivariant rational homomorphism is equivariant. -/
def pullbackMap (b : S' ⟶ S) {X Y : RationalAlgebraAction S D} (f : X ⟶ Y) :
    pullbackObj b X ⟶ pullbackObj b Y :=
  homMk (rationalBaseChangeHom b (hom0 f)) (by
    intro d
    have h := congrArg
      (rationalBaseChangeHom b (A := X.abelianScheme) (B := Y.abelianScheme))
      (intertwines f d)
    exact (rationalBaseChangeHom_comp b
      (A := X.abelianScheme) (B := X.abelianScheme) (C := Y.abelianScheme)
      (X.action d) (hom0 f)).symm.trans (h.trans
      (rationalBaseChangeHom_comp b
        (A := X.abelianScheme) (B := Y.abelianScheme) (C := Y.abelianScheme)
        (hom0 f) (Y.action d))))

/-- Pull back both the actual abelian scheme and its actual rational algebra action. -/
def pullback (b : S' ⟶ S) : RationalAlgebraAction S D ⥤ RationalAlgebraAction S' D where
  obj := pullbackObj b
  map := pullbackMap b
  map_id X := by
    apply hom_ext
    exact rationalBaseChangeHom_identity b X.abelianScheme
  map_comp {X Y Z} f g := by
    apply hom_ext
    exact rationalBaseChangeHom_comp b
      (A := X.abelianScheme) (B := Y.abelianScheme) (C := Z.abelianScheme)
      (hom0 f) (hom0 g)

@[simp] theorem pullback_obj_abelianScheme (b : S' ⟶ S)
    (X : RationalAlgebraAction S D) :
    ((pullback b).obj X).abelianScheme = (baseChange b).obj X.abelianScheme := rfl

@[simp] theorem pullback_obj_action (b : S' ⟶ S)
    (X : RationalAlgebraAction S D) (d : D) :
    ((pullback b).obj X).action d = rationalBaseChangeHom b (X.action d) := rfl

@[simp] theorem hom0_pullback_map (b : S' ⟶ S)
    {X Y : RationalAlgebraAction S D} (f : X ⟶ Y) :
    hom0 ((pullback b).map f) = rationalBaseChangeHom b (hom0 f) := rfl

/-- Forgetting the action commutes with actual rational pullback. -/
def pullbackForgetIso (b : S' ⟶ S) :
    pullback b ⋙ forget S' D ≅ forget S D ⋙ rationalBaseChange b :=
  Iso.refl _

/-- The actual identity pullback comparison intertwines the algebra actions. -/
def pullbackIdIso (X : RationalAlgebraAction S D) :
    (pullback (𝟙 S)).obj X ≅ X :=
  isoMk (rationalBaseChangeIdIso X.abelianScheme)
    (fun d => rationalBaseChangeHom_id (X.action d))

/-- The actual direct-to-successive pullback comparison intertwines the actions. -/
def pullbackCompIso (b : S' ⟶ S) (c : S'' ⟶ S')
    (X : RationalAlgebraAction S D) :
    (pullback (c ≫ b)).obj X ≅ (pullback c).obj ((pullback b).obj X) :=
  isoMk (rationalBaseChangeCompIso b c X.abelianScheme)
    (fun d => rationalBaseChangeHom_base_comp b c
      (A := X.abelianScheme) (B := X.abelianScheme) (X.action d))

@[simp] theorem underlyingIso_pullbackIdIso (X : RationalAlgebraAction S D) :
    underlyingIso (pullbackIdIso X) = rationalBaseChangeIdIso X.abelianScheme := by
  ext
  rfl

@[simp] theorem underlyingIso_pullbackCompIso (b : S' ⟶ S) (c : S'' ⟶ S')
    (X : RationalAlgebraAction S D) :
    underlyingIso (pullbackCompIso b c X) =
      rationalBaseChangeCompIso b c X.abelianScheme := by
  ext
  rfl

/-- Identity pullback is naturally isomorphic to the identity action functor. -/
def pullbackIdNatIso :
    pullback (𝟙 S) ≅ 𝟭 (RationalAlgebraAction S D) :=
  NatIso.ofComponents pullbackIdIso (by
    intro X Y f
    apply hom_ext
    exact rationalBaseChangeHom_id (hom0 f))

/-- Direct and successive pullback are naturally isomorphic on the action category. -/
def pullbackCompNatIso (b : S' ⟶ S) (c : S'' ⟶ S') :
    pullback (D := D) (c ≫ b) ≅ pullback b ⋙ pullback c :=
  NatIso.ofComponents (pullbackCompIso b c) (by
    intro X Y f
    apply hom_ext
    exact rationalBaseChangeHom_base_comp b c
      (A := X.abelianScheme) (B := Y.abelianScheme) (hom0 f))

end RationalAlgebraAction
end Langlands.AbelianScheme
