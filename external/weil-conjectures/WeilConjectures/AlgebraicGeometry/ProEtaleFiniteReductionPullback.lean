/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.ProEtaleIntegralCoefficientLimit
public import WeilConjectures.SixFunctors.ProEtale.GaloisEvaluation

/-!
# Base change for one normalized finite reduction

The finite constant-sheaf identifications and the adjunction-mate calculation for a
single continuous finite quotient. This calculation is independent of the integral
limit and of its ring-compatible comparison.

(auxiliary; not a blueprint node).
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u v

open CategoryTheory CategoryTheory.Limits Opposite WeilConjectures
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

/-- The canonical comparison between a constant commutative ring sheaf, regarded as
an abelian sheaf, and the constant abelian sheaf of its additive group.
Source: blueprint pullback clause 1, canonical finite constant-sheaf identifications
(blueprint: lemma-comparison-completed-coefficients--4). -/
def sfbConstantRingAbIso (X : Scheme.{u}) (A : CommRingCat.{u + 1}) :
    (sheafCompose (Scheme.ProEt.topology X) (forget₂ RingCat.{u + 1} Ab.{u + 1})).obj
        ((sheafCompose (Scheme.ProEt.topology X)
          (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
            ((constantSheaf (Scheme.ProEt.topology X) CommRingCat.{u + 1}).obj A)) ≅
      (constantSheaf (Scheme.ProEt.topology X) Ab.{u + 1}).obj (AddCommGrpCat.of A) :=
  letI : (Scheme.ProEt.topology X).PreservesSheafification
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1}) :=
    GrothendieckTopology.instPreservesSheafification _ _
  letI : (Scheme.ProEt.topology X).PreservesSheafification
      (forget₂ RingCat.{u + 1} Ab.{u + 1}) :=
    GrothendieckTopology.instPreservesSheafification _ _
  (sheafCompose (Scheme.ProEt.topology X) (forget₂ RingCat.{u + 1} Ab.{u + 1})).mapIso
    ((constantCommuteCompose (Scheme.ProEt.topology X)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).app A) ≪≫
    (constantCommuteCompose (Scheme.ProEt.topology X)
      (forget₂ RingCat.{u + 1} Ab.{u + 1})).app ((forget₂ CommRingCat RingCat).obj A)

attribute [local irreducible] upperStarLowerStarAdjunction constantSheafΓAdj
  globalSectionsLowerStarIso

private abbrev finitePoint : FintypeCat.{u} := FintypeCat.of PUnit.{u + 1}

private noncomputable def finitePointTerminal (X : Scheme.{u}) :
    IsTerminal ((profiniteToProEtOf X).obj (FintypeCat.toProfinite.obj finitePoint)) := by
  have : PreservesFiniteLimits (profiniteToProEtOf X) := by
    have : PreservesFiniteLimits profiniteToProEt.{u} := inferInstance
    have : PreservesFiniteLimits
        (MorphismProperty.Over.pullback @WeaklyEtale ⊤ (toSpecZ X)) := inferInstance
    exact comp_preservesFiniteLimits _ _
  exact Profinite.isTerminalPUnit.isTerminalObj (profiniteToProEtOf X) _

private theorem pointAdj_map_app (X : Scheme.{u})
    {F G : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}} (t : F ⟶ G)
    (S : Profinite.{u}) :
    ((sfbPullbackFromPointRightAdjoint X).map t).hom.app (op S) =
      t.hom.app (op ((profiniteToProEtOf X).obj S)) := rfl

attribute [local irreducible] pointUpperStarLowerStarAdjunction

set_option backward.isDefEq.respectTransparency false in
private theorem constantCommute_unit {C D B : Type*} [Category* C] [Category* D]
    [Category* B] (J : GrothendieckTopology C) (U : D ⥤ B)
    [HasWeakSheafify J D] [HasWeakSheafify J B]
    [J.HasSheafCompose U] [J.PreservesSheafification U] (A : D) :
    Functor.whiskerRight (toSheafify J ((Functor.const Cᵒᵖ).obj A)) U ≫
        ((constantCommuteCompose J U).hom.app A).hom =
      (Functor.constComp Cᵒᵖ A U).hom ≫
        toSheafify J ((Functor.const Cᵒᵖ).obj (U.obj A)) := by
  rw [constantCommuteCompose_hom_app_hom, ← Category.assoc,
    sheafComposeIso_inv_fac, ← toSheafify_naturality]

private noncomputable abbrev finiteAbSheaf (X : Scheme.{u}) (R : Type u) [CommRing R] :=
  (sheafCompose (Scheme.ProEt.topology X) (forget₂ RingCat.{u + 1} Ab.{u + 1})).obj
    ((sheafCompose (Scheme.ProEt.topology X)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
        ((constantSheaf (Scheme.ProEt.topology X) CommRingCat.{u + 1}).obj
          (CommRingCat.of (ULift.{u + 1} R))))

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem constantRingAb_unit (X : Scheme.{u}) (A : CommRingCat.{u + 1})
    (V : X.ProEtᵒᵖ) (x : A) :
    (sfbConstantRingAbIso X A).hom.hom.app V
        ((toSheafify (Scheme.ProEt.topology X)
          ((Functor.const X.ProEtᵒᵖ).obj A)).app V x) =
      (toSheafify (Scheme.ProEt.topology X)
        ((Functor.const X.ProEtᵒᵖ).obj (AddCommGrpCat.of A))).app V x := by
  let : (Scheme.ProEt.topology X).PreservesSheafification
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1}) :=
    GrothendieckTopology.instPreservesSheafification _ _
  let : (Scheme.ProEt.topology X).PreservesSheafification
      (forget₂ RingCat.{u + 1} Ab.{u + 1}) :=
    GrothendieckTopology.instPreservesSheafification _ _
  have h₁ := congrArg (fun t ↦ t.app V x)
    (constantCommute_unit (Scheme.ProEt.topology X)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1}) A)
  have h₂ := congrArg (fun t ↦ t.app V x)
    (constantCommute_unit (Scheme.ProEt.topology X)
      (forget₂ RingCat.{u + 1} Ab.{u + 1})
        ((forget₂ CommRingCat.{u + 1} RingCat.{u + 1}).obj A))
  exact (congrArg (fun z ↦ ((constantCommuteCompose (Scheme.ProEt.topology X)
    (forget₂ RingCat.{u + 1} Ab.{u + 1})).hom.app
      ((forget₂ CommRingCat.{u + 1} RingCat.{u + 1}).obj A)).hom.app V z) h₁).trans h₂

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private noncomputable def finiteRepresentation (X : Scheme.{u})
    (a : sfbFiniteConstantSets X ≅ sfbFiniteRepresentables X)
    (R : Type u) [CommRing R] [Finite R] :
    (finiteAbSheaf X R).obj ⋙ forget Ab.{u + 1} ≅
      uliftYoneda.{u + 1}.obj
        ((profiniteToProEtOf X).obj (FintypeCat.toProfinite.obj (FintypeCat.of R))) :=
  (sheafToPresheaf _ _).mapIso
    ((constantCommuteCompose (Scheme.ProEt.topology X) (forget CommRingCat.{u + 1})).app
      (CommRingCat.of (ULift.{u + 1} R))) ≪≫ a.app (FintypeCat.of R)

end AlgebraicGeometry.ProEtale
