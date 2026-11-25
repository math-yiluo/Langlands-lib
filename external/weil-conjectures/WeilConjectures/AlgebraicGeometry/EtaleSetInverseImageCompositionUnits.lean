/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.EtaleInverseImageAlgebraicStructures
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
import WeilConjectures.Mathlib.CategoryTheory.Adjunction.Mates
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Coherence

/-! # Composition of inverse images of étale sheaves of sets, with units

Source: Stacks Project, Sites, Tags 03CB and 03CC, and Étale Cohomology, Tag 09ZF,
third paragraph of the proof
(blueprint: lem-weil-pbc-sets-etale-inverse-image-composition-units).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

local notation "L" => Scheme.etaleSetPullback
local notation "b" => MorphismProperty.Over.pullback @Etale ⊤
local notation "η[" S "," T "]" e =>
  Adjunction.unit
    (Functor.sheafPullbackConstruction.sheafAdjunctionContinuous (b e) _
      (Scheme.smallGrothendieckTopology @Etale S)
      (Scheme.smallGrothendieckTopology @Etale T))

private noncomputable def setPush {S T : Scheme.{u}} (e : T ⟶ S) :=
  Functor.sheafPushforwardContinuous (b e) (Type (u + 1))
    (S.smallGrothendieckTopology @Etale) (T.smallGrothendieckTopology @Etale)

private noncomputable def setAdj {S T : Scheme.{u}} (e : T ⟶ S) :
    L e ⊣ setPush e :=
  Functor.sheafPullbackConstruction.sheafAdjunctionContinuous (b e) (Type (u + 1))
    (S.smallGrothendieckTopology @Etale) (T.smallGrothendieckTopology @Etale)

private noncomputable def setPushComp {X Y W : Scheme.{u}} (f : Y ⟶ X) (g : W ⟶ Y)
    (k : W ⟶ X := g ≫ f) (hk : k = g ≫ f := by cat_disch) :
    setPush g ⋙ setPush f ≅ setPush k :=
  Functor.sheafPushforwardContinuousComp'
    (eFG := (MorphismProperty.Over.pullbackComp (P := @Etale) (Q := ⊤) g f k hk).symm)
    (Type (u + 1)) (X.smallGrothendieckTopology @Etale)
    (Y.smallGrothendieckTopology @Etale) (W.smallGrothendieckTopology @Etale)

private noncomputable def setPullComp {X Y W : Scheme.{u}} (f : Y ⟶ X) (g : W ⟶ Y)
    (k : W ⟶ X := g ≫ f) (hk : k = g ≫ f := by cat_disch) :
    L f ⋙ L g ≅ L k :=
  (conjugateIsoEquiv (setAdj k) ((setAdj f).comp (setAdj g))).symm
    (setPushComp f g k hk).symm

private lemma setPullComp_conjugate {X Y W : Scheme.{u}} (f : Y ⟶ X) (g : W ⟶ Y)
    (k : W ⟶ X := g ≫ f) (hk : k = g ≫ f := by cat_disch) :
    conjugateIsoEquiv ((setAdj f).comp (setAdj g)) (setAdj k)
      (setPullComp f g k hk).symm = setPushComp f g k hk := by
  ext : 1
  simp only [setPullComp, conjugateIsoEquiv_apply_hom, Iso.symm_hom,
    conjugateIsoEquiv_symm_apply_inv, Iso.symm_inv]
  exact Equiv.apply_symm_apply _ _

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
private lemma setPullComp_assoc_iso {X Y W V : Scheme.{u}}
    (f : Y ⟶ X) (g : W ⟶ Y) (h : V ⟶ W)
    (k : V ⟶ X := h ≫ g ≫ f) (hk : k = h ≫ g ≫ f := by cat_disch) :
    (setPullComp (g ≫ f) h k hk).symm ≪≫
        Functor.isoWhiskerRight (setPullComp f g).symm (L h) ≪≫
          (L f).associator (L g) (L h) =
      (setPullComp f (h ≫ g) k (by rw [hk, Category.assoc])).symm ≪≫
        Functor.isoWhiskerLeft (L f) (setPullComp g h).symm := by
  refine (conjugateIsoEquiv ((setAdj f).comp ((setAdj g).comp (setAdj h)))
    (setAdj k)).injective ?_
  rw [conjugateIsoEquiv_trans _ ((setAdj (g ≫ f)).comp (setAdj h)) _,
    conjugateIsoEquiv_trans _ (((setAdj f).comp (setAdj g)).comp (setAdj h)) _,
    conjugateIsoEquiv_trans _ ((setAdj f).comp (setAdj (h ≫ g))) _]
  simp only [setPullComp_conjugate, conjugateIsoEquiv_isoWhiskerRight,
    conjugateIsoEquiv_isoWhiskerLeft, conjugateIsoEquiv_associator, Iso.trans_assoc]
  exact Etale.lowerStarComp_assoc (Type (u + 1)) h g f k hk

private lemma setPullComp_transport {X Y W : Scheme.{u}}
    (f : Y ⟶ X) (g : W ⟶ Y) (k : W ⟶ X) (hk : k = g ≫ f)
    (F : Sheaf X.smallEtaleTopology (Type (u + 1))) :
    (setPullComp f g k hk).hom.app F = (setPullComp f g).hom.app F ≫
      eqToHom (congrArg (fun k ↦ (L k).obj F) hk.symm) := by
  subst k
  simp

private lemma setPullComp_unit {X Y W : Scheme.{u}} (f : Y ⟶ X) (g : W ⟶ Y)
    (F : Sheaf X.smallEtaleTopology (Type (u + 1))) :
    (setAdj (g ≫ f)).unit.app F ≫ (setPushComp f g).inv.app ((L (g ≫ f)).obj F) =
      ((setAdj f).comp (setAdj g)).unit.app F ≫
        (setPush g ⋙ setPush f).map ((setPullComp f g).hom.app F) := by
  exact unit_conjugateEquiv_symm (setAdj (g ≫ f)) ((setAdj f).comp (setAdj g))
    (setPushComp f g).inv F

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- Source: Stacks Project, Sites, Tags 03CB and 03CC; Étale Cohomology, Tag 09ZF,
third paragraph of the proof
(blueprint: lem-weil-pbc-sets-etale-inverse-image-composition-units).
The inverse image `L e` is left Kan extension followed by sheafification, and `η[S, T] e`
is the unit of its adjunction to restriction along base change. The isomorphisms
are natural in the sheaf, preserve pulled-back sections, are unique even for a
fixed sheaf, and satisfy associativity. The base-change comparison in the section
formula is the canonical fibre-product pasting isomorphism.

Proof:
1. By situation-conventions, the unit sends a
   section to its identity-indexed colimit representative followed by sheafification.
   Naturality in site objects and in sheaves gives the two equations in clause (0),
   using situation-conventions and def-weil-pbc-sheafification.
2. By lem-weil-pbc-cartesian-square-pasting and def-pc-fibre-product, iterated base
   change is canonically isomorphic to composite base change, naturally in objects.
   Both triple comparisons have the same projections, hence agree.
3. Apply def-weil-pbc-composite-adjunction to the two inverse-image adjunctions,
   and situation-conventions to the direct-image comparison.
   This gives the natural composition isomorphism and its unit equation.
4. By lem-weil-pbc-site-sheafification-sections-local, applied twice, every section
   of an iterated inverse image is locally a restriction of an iterated pulled-back
   section. Pull back the intermediate covering using
   situation-conventions. A morphism satisfying the unit equation
   therefore agrees locally with the comparison, hence equals it by the sheaf axiom
   of situation-conventions. This proves fixed-sheaf uniqueness.
5. On locally generating triple pulled-back sections, unit naturality and the
   composition equations identify both associative composites with the pullback
   along the composite morphism. The triple fibre-product comparisons agree by
   their projections. Local equality and the sheaf axiom give associativity. -/
theorem etaleSetInverseImageCompositionUnits :
    (∀ (S T : Scheme.{u}) (e : T ⟶ S)
      (G : Sheaf S.smallEtaleTopology (Type (u + 1)))
      (U U' : S.Etale) (a : U' ⟶ U) (s : G.obj.obj (op U)),
      ((η[S, T] e).app G).hom.app (op U') (G.obj.map a.op s) =
        ((L e).obj G).obj.map ((b e).map a).op (((η[S, T] e).app G).hom.app (op U) s)) ∧
    (∀ (S T : Scheme.{u}) (e : T ⟶ S)
      (G G' : Sheaf S.smallEtaleTopology (Type (u + 1))) (ψ : G ⟶ G')
      (U : S.Etale) (s : G.obj.obj (op U)),
      ((η[S, T] e).app G').hom.app (op U) (ψ.hom.app (op U) s) =
        ((L e).map ψ).hom.app (op ((b e).obj U))
          (((η[S, T] e).app G).hom.app (op U) s)) ∧
    ∃ c : ∀ (X Y W : Scheme.{u}) (f : Y ⟶ X) (g : W ⟶ Y),
      L f ⋙ L g ≅ L (g ≫ f),
      (∀ (X Y W : Scheme.{u}) (f : Y ⟶ X) (g : W ⟶ Y)
        (F : Sheaf X.smallEtaleTopology (Type (u + 1)))
        (U : X.Etale) (s : F.obj.obj (op U)),
        ((c X Y W f g).hom.app F).hom.app (op ((b g).obj ((b f).obj U)))
          (((η[Y, W] g).app ((L f).obj F)).hom.app (op ((b f).obj U))
            (((η[X, Y] f).app F).hom.app (op U) s)) =
          ((L (g ≫ f)).obj F).obj.map
            ((MorphismProperty.Over.pullbackComp (P := @Etale) (Q := ⊤) g f).inv.app U).op
            (((η[X, W] (g ≫ f)).app F).hom.app (op U) s)) ∧
      (∀ (X Y W : Scheme.{u}) (f : Y ⟶ X) (g : W ⟶ Y)
        (F : Sheaf X.smallEtaleTopology (Type (u + 1)))
        (q : (L g).obj ((L f).obj F) ⟶ (L (g ≫ f)).obj F),
        (∀ (U : X.Etale) (s : F.obj.obj (op U)),
          q.hom.app (op ((b g).obj ((b f).obj U)))
            (((η[Y, W] g).app ((L f).obj F)).hom.app (op ((b f).obj U))
              (((η[X, Y] f).app F).hom.app (op U) s)) =
            ((L (g ≫ f)).obj F).obj.map
              ((MorphismProperty.Over.pullbackComp (P := @Etale) (Q := ⊤) g f).inv.app U).op
              (((η[X, W] (g ≫ f)).app F).hom.app (op U) s)) →
          q = (c X Y W f g).hom.app F) ∧
      (∀ (X Y W V : Scheme.{u}) (f : Y ⟶ X) (g : W ⟶ Y) (h : V ⟶ W)
        (F : Sheaf X.smallEtaleTopology (Type (u + 1))),
        (L h).map ((c X Y W f g).hom.app F) ≫
            (c X W V (g ≫ f) h).hom.app F =
          (c Y W V g h).hom.app ((L f).obj F) ≫
            (c X Y V f (h ≫ g)).hom.app F ≫
              eqToHom (congrArg (fun k : V ⟶ X ↦ (L k).obj F) (Category.assoc h g f))) := by
  refine ⟨?_, ?_, ?_⟩
  · intro S T e G U U' a s
    exact ConcreteCategory.congr_hom (((η[S, T] e).app G).hom.naturality a.op) s
  · intro S T e G G' ψ U s
    exact ConcreteCategory.congr_hom (NatTrans.congr_app
      (congrArg (fun k ↦ k.hom) ((η[S, T] e).naturality ψ)) (op U)) s
  · refine ⟨fun _ _ _ f g ↦ setPullComp f g, ?_, ?_, ?_⟩
    · intro X Y W f g F U s
      have h := ConcreteCategory.congr_hom (NatTrans.congr_app
        (congrArg (fun k ↦ k.hom) (setPullComp_unit f g F)) (op U)) s
      simpa [Adjunction.comp_unit_app, setPushComp, setPush, setAdj,
        Scheme.etaleSetPullback] using h.symm
    · intro X Y W f g F q hq
      apply ((setAdj f).comp (setAdj g)).homEquiv F ((L (g ≫ f)).obj F) |>.injective
      rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
      ext U s
      obtain ⟨U⟩ := U
      have hc := ConcreteCategory.congr_hom (NatTrans.congr_app
        (congrArg (fun k ↦ k.hom) (setPullComp_unit f g F)) (op U)) s
      simpa [Adjunction.comp_unit_app, setPushComp, setPush, setAdj,
        Scheme.etaleSetPullback] using (hq U s).trans hc
    · intro X Y W V f g h F
      have key := congrArg (fun e ↦ e.inv.app F)
        (setPullComp_assoc_iso f g h)
      simp only [Functor.comp_obj, Iso.trans_inv, Functor.isoWhiskerRight_inv,
        Iso.symm_inv, Category.assoc, NatTrans.comp_app, Functor.associator_inv_app,
        Functor.whiskerRight_app, Category.id_comp, Functor.isoWhiskerLeft_inv,
        Functor.whiskerLeft_app] at key
      rw [setPullComp_transport f (h ≫ g) (h ≫ g ≫ f) _ F] at key
      exact key

end AlgebraicGeometry
