/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.FiniteDiscreteCondensedRing
public import WeilConjectures.AlgebraicGeometry.FiniteDiscreteSchemeRing
import WeilConjectures.AlgebraicGeometry.FiniteDiscreteCoefficientTerminal

/-! # The coefficient maps on sections under direct image -/

@[expose] public section

universe u

open CategoryTheory Limits
open scoped CategoryTheory.Obj

attribute [local instance] _root_.instEssentiallySmallProfinite_weilConjectures

private theorem constant_naturality {C A : Type*} [Category C] [Category A]
    {a : A} {P : C ⥤ A} (q : (Functor.const C).obj a ⟶ P)
    {X Y : C} (f : X ⟶ Y) : q.app Y = q.app X ≫ P.map f := by
  have h := q.naturality f
  change 𝟙 a ≫ q.app Y = q.app X ≫ P.map f at h
  exact (Category.id_comp _).symm.trans h

private theorem constant_transport {C D A : Type*}
    [Category C] [Category D] [Category A] (F : C ⥤ D)
    {a : A} {P : C ⥤ A} {Q : D ⥤ A}
    (q : (Functor.const C).obj a ⟶ P) (r : (Functor.const D).obj a ⟶ Q)
    (p : P ⟶ F ⋙ Q) {W V : C} (f : W ⟶ V)
    (h : q.app W ≫ p.app W = r.app (F.obj W)) :
    q.app V ≫ p.app V = r.app (F.obj V) := by
  have hq := constant_naturality q f
  have hr := constant_naturality r (F.map f)
  rw [hq, Category.assoc, p.naturality f, ← Category.assoc, h]
  exact hr.symm

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (B : Type) [CommRing B] [TopologicalSpace B] [IsTopologicalRing B]

attribute [local irreducible] upperStar upperStarLowerStarAdjunction

private theorem terminal_map_exists (T : Scheme.{u}) (V : T.ProEt) :
    Nonempty (V ⟶ (MorphismProperty.Over.pullback @WeaklyEtale ⊤ (toSpecZ T)).obj
      (proEtTerminal specZ)) :=
  ⟨(proEtIsTerminal _).from V⟩

set_option backward.isDefEq.respectTransparency.types false in
/-- The constant coefficients give the same map before and after direct image.
Source: Bhatt--Scholze, Proposition 5.3.2; the canonical constant-ring comparison.
(auxiliary; not a blueprint node)

Proof in words. Use the coefficient comparison at the pullback of the terminal
object over Spec Z. For an arbitrary V, the unique map from V to this terminal
object gives an arrow in the opposite site. Naturality of the two coefficient
maps from constant presheaves and of condensedPushforwardHom propagates the
terminal comparison along that arrow. -/
theorem finiteDiscreteCoefficient_coefficientUnit_pushforward
    (eR : Sheaf.sheafifyRingPresheaf.{u + 1, u, u + 1}
      (coherentTopology Profinite.{u}) ((Functor.const Profinite.{u}ᵒᵖ).obj
        (RingCat.of (ULift.{u + 1} B))) ≅ Profinite.continuousMapRingObj.{u} B)
    (T U : Scheme.{u}) (j : U ⟶ T) (V : T.ProEtᵒᵖ) :
    ((sheafificationAdjunction (ProEt.topology T) Ab.{u + 1}).unit.app
        ((Functor.const T.ProEtᵒᵖ).obj (AddCommGrpCat.of (ULift.{u + 1} B))) ≫
      (finiteDiscreteSchemeRingIso B T eR).hom.hom).app V ≫
        (condensedPushforwardHom (Profinite.continuousMapRingObj.{u} B) j).hom.app V =
    ((sheafificationAdjunction (ProEt.topology U) Ab.{u + 1}).unit.app
        ((Functor.const U.ProEtᵒᵖ).obj (AddCommGrpCat.of (ULift.{u + 1} B))) ≫
      (finiteDiscreteSchemeRingIso B U eR).hom.hom).app
        ((MorphismProperty.Over.pullback @WeaklyEtale ⊤ j).op.obj V) := by
  obtain ⟨f⟩ := terminal_map_exists T V.unop
  have hbase := finiteDiscreteCoefficient_coefficientUnit_pushforward_terminal B eR T U j
  have htransport := constant_transport (V := V)
    (MorphismProperty.Over.pullback @WeaklyEtale ⊤ j).op
    ((sheafificationAdjunction (ProEt.topology T) Ab.{u + 1}).unit.app
      ((Functor.const T.ProEtᵒᵖ).obj (AddCommGrpCat.of (ULift.{u + 1} B))) ≫
      (finiteDiscreteSchemeRingIso B T eR).hom.hom)
    ((sheafificationAdjunction (ProEt.topology U) Ab.{u + 1}).unit.app
      ((Functor.const U.ProEtᵒᵖ).obj (AddCommGrpCat.of (ULift.{u + 1} B))) ≫
      (finiteDiscreteSchemeRingIso B U eR).hom.hom)
    (condensedPushforwardHom (Profinite.continuousMapRingObj.{u} B) j).hom
      f.op hbase
  exact htransport

end AlgebraicGeometry.ProEtale.CondensedRing
