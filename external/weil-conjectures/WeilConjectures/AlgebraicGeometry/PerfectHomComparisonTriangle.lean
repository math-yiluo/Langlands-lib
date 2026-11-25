/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.PerfectHomTransport


public import WeilConjectures.AlgebraicGeometry.PerfectHomTransportExtension
import all WeilConjectures.AlgebraicGeometry.PerfectHomTransportExtension

/-! # Projection triangles for derived pullback
Source: Stacks Project, Tag 0D5S, composition of derived pullbacks.
(blueprint: lem-pc-perfect-hom-comparison-triangle). -/

@[expose] public section
universe u w
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
attribute [local irreducible] perfectHomComposition

variable [∀ X : Scheme.{u},
  HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]

private noncomputable def compositionTo {X Y Z : Scheme.{u}} (f : X ⟶ Y)
    (p : Y ⟶ Z) (q : X ⟶ Z) (e : f ≫ p = q) :
    derivedPullback p ⋙ derivedPullback f ≅ derivedPullback q :=
  perfectHomComposition f p ≪≫ eqToIso (congrArg (fun k ↦ derivedPullback k) e)

private theorem compositionTo_triangle {W X Y Z : Scheme.{u}}
    (h : W ⟶ X) (f : X ⟶ Y) (p : Y ⟶ Z)
    (q : X ⟶ Z) (r : W ⟶ Z) (t : W ⟶ Y)
    (eq : f ≫ p = q) (er : h ≫ q = r) (et : h ≫ f = t)
    (P : schemeDerivedCategory Z) :
    (derivedPullback h).mapIso ((compositionTo f p q eq).app P) ≪≫
      (compositionTo h q r er).app P =
    (compositionTo h f t et).app ((derivedPullback p).obj P) ≪≫
      (compositionTo t p r (by rw [← et, Category.assoc, eq, er])).app P := by
  subst q
  subst r
  subst t
  have hh := congrArg (fun α ↦ α.hom.app P) (cc_assoc h f p)
  apply Iso.ext
  simp only [compositionTo, Iso.trans_hom, NatTrans.comp_app,
    Functor.mapIso_hom, Iso.app_hom, eqToIso_refl, Iso.refl_hom,
    Category.comp_id, Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom,
    Functor.whiskerRight_app, Functor.whiskerLeft_app, Functor.associator_hom_app,
    Category.id_comp] at hh ⊢
  exact hh

private theorem comparison_symm {X S : Scheme.{u}} (s : X ⟶ S)
    {T T' : Over S} (g : T' ⟶ T) (P : schemeDerivedCategory X) :
    ((perfectHomComparison s g).app P).symm =
      (compositionTo (baseChangeMap s g) (pullback.fst s T.hom)
        (pullback.fst s T'.hom) (baseChangeMap_fst s g)).app P := by
  apply Iso.ext
  simp only [perfectHomComparison, compositionTo, Iso.symm_hom, Iso.app_hom,
    Iso.app_inv, Iso.trans_inv, Iso.trans_hom, Iso.symm_inv, NatTrans.comp_app,
    eqToIso.hom, eqToIso.inv]

/-- The projection comparisons satisfy the object triangle for two over-category arrows.
Source: Stacks Project, Tag 0D5S, associativity of derived pullback.
(blueprint: lem-pc-perfect-hom-comparison-triangle).

Proof: the inverse perfectHomComparison is the fixed composition comparison followed
by transport along baseChangeMap_fst. Apply the associativity clause of
exists_derivedPullbackComposition to baseChangeMap s h, baseChangeMap s g and the
projection of T. Evaluate at P. Transport the first two composites along their
projection equations and the composite base-change map along baseChangeMap_comp
and ht. The functor associator has identity components. The resulting equality
is exactly the displayed triangle. Identity arrows and empty schemes use the same
associativity equation, with no geometric hypotheses. -/
theorem perfectHomComparison_triangle {X S : Scheme.{u}} (s : X ⟶ S)
    {T T' T'' : Over S} (g : T' ⟶ T) (h : T'' ⟶ T') (t : T'' ⟶ T)
    (ht : h ≫ g = t) (P : schemeDerivedCategory X) :
    (derivedPullback (baseChangeMap s h)).mapIso
        ((perfectHomComparison s g).app P).symm ≪≫
      ((perfectHomComparison s h).app P).symm =
    (perfectHomComposition (baseChangeMap s h) (baseChangeMap s g) ≪≫
      eqToIso (congrArg (fun f ↦ derivedPullback f)
        ((baseChangeMap_comp s h g).symm.trans
          (congrArg (baseChangeMap s) ht)))).app
        ((derivedPullback (pullback.fst s T.hom)).obj P) ≪≫
      ((perfectHomComparison s t).app P).symm := by
  have hh := compositionTo_triangle (baseChangeMap s h) (baseChangeMap s g)
    (pullback.fst s T.hom) (pullback.fst s T'.hom) (pullback.fst s T''.hom)
    (baseChangeMap s t) (baseChangeMap_fst s g) (baseChangeMap_fst s h)
    ((baseChangeMap_comp s h g).symm.trans (congrArg (baseChangeMap s) ht)) P
  rw [comparison_symm, comparison_symm, comparison_symm]
  exact hh

end AlgebraicGeometry
