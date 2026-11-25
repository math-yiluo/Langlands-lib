/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.FiniteDiscreteOrdinaryEncoding
import all WeilConjectures.AlgebraicGeometry.FiniteDiscreteCoefficientTerminal

/-! # Finite discrete coefficient comparison -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false

universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.FiniteDiscreteOrdinary

variable (A : Type u) [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]

private theorem constants_natural {C D : Type*} [Category C] [Category D]
    {a : D} {P : C ⥤ D} (q : (Functor.const C).obj a ⟶ P)
    {X Y : C} (f : X ⟶ Y) : q.app Y = q.app X ≫ P.map f := by
  simpa using q.naturality f

private theorem constants_transport {C D B : Type*}
    [Category C] [Category D] [Category B] (F : C ⥤ D)
    {a : B} {P : C ⥤ B} {Q : D ⥤ B}
    (q : (Functor.const C).obj a ⟶ P) (r : (Functor.const D).obj a ⟶ Q)
    (p : P ⟶ F ⋙ Q) {W V : C} (f : W ⟶ V)
    (h : q.app W ≫ p.app W = r.app (F.obj W)) :
    q.app V ≫ p.app V = r.app (F.obj V) := by
  have hq := constants_natural q f
  have hr := constants_natural r (F.map f)
  rw [hq, Category.assoc, p.naturality f, ← Category.assoc, h]
  exact hr.symm

private theorem terminal_map_exists (T : Scheme.{u}) (V : T.ProEt) :
    Nonempty (V ⟶ (MorphismProperty.Over.pullback @WeaklyEtale ⊤ (toSpecZ T)).obj
      (proEtTerminal specZ.{u})) :=
  ⟨(proEtIsTerminal _).from V⟩

/-- Canonical constant scalars commute with every scheme direct-image coefficient map.
Source: blueprint coefficient-identification proof, step 8; the unit comparison for
constantSchemeIso. (auxiliary; not a blueprint node).

Proof: at the base change of the terminal pro-etale object over Spec Z, the two maps
are the same constant-sheaf unit followed by the inverse-image adjunction unit. The
composition law for these units gives their equality. Naturality propagates this
identity along the unique arrow from any site object to that base-changed terminal
object. No finite, discrete, nonzero-ring or nonempty-scheme hypothesis is used. -/
theorem canonicalAbelianMap_naturality (T U : Scheme.{u}) (j : U ⟶ T) (V : T.ProEtᵒᵖ) :
    (toSheafify (Scheme.ProEt.topology T)
        ((Functor.const T.ProEtᵒᵖ).obj (AddCommGrpCat.of (ULift.{u + 1} A))) ≫
      (canonicalAbelianMap A T).hom).app V ≫
        (condensedPushforwardHom (coefficient A) j).hom.app V =
    (toSheafify (Scheme.ProEt.topology U)
        ((Functor.const U.ProEtᵒᵖ).obj (AddCommGrpCat.of (ULift.{u + 1} A))) ≫
      (canonicalAbelianMap A U).hom).app
        ((MorphismProperty.Over.pullback @WeaklyEtale ⊤ j).op.obj V) := by
  obtain ⟨f⟩ := terminal_map_exists T V.unop
  have h := CondensedRing.constantScheme_pushforward
    (AddCommGrpCat.of (ULift.{u + 1} A)) (coefficient A)
    (((sheafificationAdjunction (coherentTopology Profinite.{u}) Ab.{u + 1}).homEquiv
      _ (coefficient A)).symm (pointConstants A)) T U j
  have htransport := constants_transport (V := V)
    (MorphismProperty.Over.pullback @WeaklyEtale ⊤ j).op
    (toSheafify (Scheme.ProEt.topology T)
        ((Functor.const T.ProEtᵒᵖ).obj (AddCommGrpCat.of (ULift.{u + 1} A))) ≫
      (canonicalAbelianMap A T).hom)
    (toSheafify (Scheme.ProEt.topology U)
        ((Functor.const U.ProEtᵒᵖ).obj (AddCommGrpCat.of (ULift.{u + 1} A))) ≫
      (canonicalAbelianMap A U).hom)
    (condensedPushforwardHom (coefficient A) j).hom f.op h
  exact htransport

end AlgebraicGeometry.ProEtale.FiniteDiscreteOrdinary
