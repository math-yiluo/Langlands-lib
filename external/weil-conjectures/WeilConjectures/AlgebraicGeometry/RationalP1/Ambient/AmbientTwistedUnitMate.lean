/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedAmbientExchange
public import WeilConjectures.AlgebraicGeometry.RationalP1.Scalar.RationalP1ScalarChernMaps
@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option allowUnsafeReducibility true in
attribute [local reducible] AlgebraicGeometry.ProEtale.CondensedRing.moduleObjectDerivedPullback
  AlgebraicGeometry.ProEtale.CondensedRing.moduleObjectDerivedPushforward
set_option allowUnsafeReducibility true in
attribute [local irreducible] CategoryTheory.mateEquiv CategoryTheory.Functor.leftDerivedFunctor
  CategoryTheory.Functor.rightDerivedFunctor CategoryTheory.Functor.mapDerivedCategory
  AlgebraicGeometry.ProEtale.CondensedRing.upperStar
  AlgebraicGeometry.ProEtale.CondensedRing.lowerStar
  AlgebraicGeometry.ProEtale.CondensedRing.derivedUpperStarLowerStarAdjunction
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped CategoryTheory.Obj CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.RationalP1
open DiagonalCoefficients CondensedRing
@[irreducible] private def ambientAdjunction
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X Y : Scheme.{u}} (f : X ⟶ Y) :
    moduleObjectDerivedPullback Λ f ⊣ moduleObjectDerivedPushforward Λ f := by
  unfold moduleObjectDerivedPullback moduleObjectDerivedPushforward
  exact CondensedRing.derivedUpperStarLowerStarAdjunction Λ f

private theorem scalarTwistedUnit_eq
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X Y : Scheme.{u}} (f : X ⟶ Y)
    (A : DerivedCategory (Modules Λ Y)) (B : DerivedCategory (Modules Λ X))
    (e : (moduleObjectDerivedPullback Λ f).obj A ≅ B) :
    scalarTwistedUnit Λ f A B e = (ambientAdjunction Λ f).unit.app A ≫
      (moduleObjectDerivedPushforward Λ f).map e.hom := by
  delta scalarTwistedUnit ambientAdjunction
  rfl

private theorem condensedAmbientExchange_eq
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    {X' X Y' Y : Scheme.{u}} {g' : X' ⟶ X} {f' : X' ⟶ Y'}
    {f : X ⟶ Y} {g : Y' ⟶ Y} (sq : ChosenCartesianSquare g' f' f g) :
    condensedAmbientExchange Λ sq =
      (mateEquiv (ambientAdjunction Λ f) (ambientAdjunction Λ f')
        (TwoSquare.mk (moduleObjectDerivedPullback Λ g) (moduleObjectDerivedPullback Λ f)
          (moduleObjectDerivedPullback Λ f') (moduleObjectDerivedPullback Λ g')
          (condensedAmbientPullbackComparison Λ sq).hom)) := by
  delta condensedAmbientExchange ambientAdjunction
  rfl

-- Perform the mate calculation before specializing to the derived module categories.
private theorem mate_unit_maps
    {C D C' D' : Type*} [Category C] [Category D] [Category C'] [Category D']
    {L : C ⥤ D} {R : D ⥤ C} {L' : C' ⥤ D'} {R' : D' ⥤ C'}
    {G : C ⥤ C'} {H : D ⥤ D'} (a : L ⊣ R) (b : L' ⊣ R')
    (θ : TwoSquare G L L' H) {A : C} {B : D} {B' : C'} {Q : D'}
    (e : L.obj A ⟶ B) (j : G.obj A ⟶ B') (d : H.obj B ⟶ Q)
    (e₂ : L'.obj B' ⟶ Q) (h : θ.app A ≫ H.map e ≫ d = L'.map j ≫ e₂) :
    G.map (a.unit.app A ≫ R.map e) ≫ (mateEquiv a b θ).app B ≫ R'.map d =
      j ≫ b.unit.app B' ≫ R'.map e₂ := by
  have hn := (mateEquiv a b θ).naturality e
  simp only [Functor.comp_map] at hn
  calc
    _ = G.map (a.unit.app A) ≫ (mateEquiv a b θ).app (L.obj A) ≫
        R'.map (H.map e) ≫ R'.map d := by
      simpa only [Functor.map_comp, Category.assoc] using
        congrArg (fun t ↦ G.map (a.unit.app A) ≫ t ≫ R'.map d) hn
    _ = b.unit.app (G.obj A) ≫ R'.map (θ.app A ≫ H.map e ≫ d) := by
      rw [← Category.assoc, ← Category.assoc, unit_mateEquiv]
      simp only [Functor.map_comp, Functor.id_obj, Category.assoc]
    _ = b.unit.app (G.obj A) ≫ R'.map (L'.map j ≫ e₂) := by rw [h]
    _ = j ≫ b.unit.app B' ≫ R'.map e₂ := by
      simpa only [Functor.map_comp, Functor.comp_map, Functor.id_map, Category.assoc] using
        congrArg (fun t ↦ t ≫ R'.map e₂) (b.unit.naturality j).symm

/-- Ambient twisted-unit mate assembly. Apply `unit_mateEquiv`, then use
naturality of the exchange and the two adjunction units. -/
theorem ambient_twisted_unit_mate
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    {X' X Y' Y : Scheme.{u}} {g' : X' ⟶ X} {f' : X' ⟶ Y'}
    {f : X ⟶ Y} {g : Y' ⟶ Y} (sq : ChosenCartesianSquare g' f' f g)
    {A : DerivedCategory (Modules Λ Y)} {B : DerivedCategory (Modules Λ X)}
    {B' : DerivedCategory (Modules Λ Y')} {Q : DerivedCategory (Modules Λ X')}
    (e : (moduleObjectDerivedPullback Λ f).obj A ≅ B)
    (j : (moduleObjectDerivedPullback Λ g).obj A ⟶ B')
    (d : (moduleObjectDerivedPullback Λ g').obj B ⟶ Q)
    (e₂ : (moduleObjectDerivedPullback Λ f').obj B' ≅ Q)
    (h : (condensedAmbientPullbackComparison Λ sq).hom.app A ≫
      (moduleObjectDerivedPullback Λ g').map e.hom ≫ d =
      (moduleObjectDerivedPullback Λ f').map j ≫ e₂.hom) :
    (moduleObjectDerivedPullback Λ g).map (scalarTwistedUnit Λ f A B e) ≫
      (condensedAmbientExchange Λ sq).app B ≫
      (moduleObjectDerivedPushforward Λ f').map d =
      j ≫ scalarTwistedUnit Λ f' B' Q e₂ := by
  rw [scalarTwistedUnit_eq, scalarTwistedUnit_eq, condensedAmbientExchange_eq]
  exact mate_unit_maps (ambientAdjunction Λ f) (ambientAdjunction Λ f')
    (TwoSquare.mk _ _ _ _ (condensedAmbientPullbackComparison Λ sq).hom)
    e.hom j d e₂.hom h
end AlgebraicGeometry.ProEtale.RationalP1
