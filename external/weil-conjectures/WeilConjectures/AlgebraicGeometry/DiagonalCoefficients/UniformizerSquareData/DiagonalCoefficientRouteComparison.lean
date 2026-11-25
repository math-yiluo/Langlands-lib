/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.UniformizerSquareData.DiagonalCoefficientRouteEndpoints

/-! # Explicit functors and endpoints for the two finite coefficient routes

Source: diagonal tower coefficient changes (1), derived adjunction transitivity.
(blueprint: def-diagonal-coefficient-route-comparison).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option Elab.async false
set_option genSizeOf false
set_option genInjectivity false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite
open scoped CategoryTheory.Obj CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.DiagonalCoefficients

-- Use the module-sheaf abelian structure of GeoCartierClass.
attribute [local instance 100000] sheafIsAbelian
attribute [local instance 200000] AlgebraicGeometry.ProEtale.diagonalAbSheafAbelian
attribute [local instance 300000] CommRing.toRing
attribute [local instance 400000] AlgebraicGeometry.ProEtale.diagonalModuleSheafAbelian
namespace UniformizerSquareData

attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits

/-- Construct the mate of a comparison of right adjoints, by their hom equivalences. -/
@[irreducible] def restrictionMate
    {C D K : Type*} [Category C] [Category D] [Category K]
    {L : C ⥤ D} {R : D ⥤ C} {L' : C ⥤ K} {R' : K ⥤ C}
    (a : L ⊣ R) (b : L' ⊣ R') (H : K ⥤ D) (s : R' ≅ H ⋙ R) :
    L ⟶ L' ⋙ H := by
  let gamma : 𝟭 C ⟶ (L' ⋙ H) ⋙ R :=
    b.unit ≫ Functor.whiskerLeft L' s.hom
  exact
    { app := fun M ↦ (a.homEquiv _ _).symm (gamma.app M)
      naturality := by
        intro M N f
        apply (a.homEquiv _ _).injective
        rw [Adjunction.homEquiv_naturality_left, Adjunction.homEquiv_naturality_right]
        simp only [Equiv.apply_symm_apply]
        exact gamma.naturality f }

variable {l : ℕ} [Fact l.Prime] {Y : Scheme.{u}}
  {E : PadicAlgCl.FiniteIntermediateField l} {π : PadicAlgCl.integers l E} {n : ℕ}
  {A : Type (u + 1)} [CommRing A] {hA : ((l ^ (n + 1) : ℕ) : A) = 0}
  (q : UniformizerSquareData l Y E π n A hA)

attribute [local irreducible] derivedScalars quotientLine quotientLineMap cyclicLine cyclicLineMap
  Functor.leftDerivedFunctor Mod.derivedExtendMapDerivedCategoryAdjunction
  HasDerivedCategory.standard DerivedCategory.singleFunctors
  HomotopyCategory.singleFunctors DerivedCategory.singleFunctorIsoCompQ

abbrev cyclicRight := q.cyclic.eW.F.asEquivalence.inverse ⋙
  Mod.comap (coefficientMap (cyclicMap l n) (diagonalSurface Y))

abbrev quotientRight := q.eW.F.asEquivalence.inverse ⋙
  ScalarCompatibility.compositeRestriction q.route.first q.route.second

/-- Underlying sheaves of the inverse finite realization, with its counit. -/
def inverseUnderlying
    {R : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
    [MonObj R] [IsCommMonObj R] {B : Type (u + 1)} [CommRing B]
    {X : Scheme.{u}} (e : FiniteRealization R B X)
    (M : Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} B)) :
    ((e.F.asEquivalence.inverse.obj M).X) ≅
      (sheafCompose (Scheme.ProEt.topology X)
        (forget₂ (ModuleCat.{u + 1} B) Ab.{u + 1})).obj M :=
  (e.underlying.app (e.F.asEquivalence.inverse.obj M)).symm ≪≫
    (sheafCompose (Scheme.ProEt.topology X)
      (forget₂ (ModuleCat.{u + 1} B) Ab.{u + 1})).mapIso
        (e.F.asEquivalence.counitIso.app M)

/-- The ordinary restriction comparison is fixed by its actual underlying sheaf map. -/
def RestrictionNormalized (s : q.quotientRight ≅ q.restriction ⋙ q.cyclicRight) : Prop :=
  ∀ M, (s.hom.app M).hom =
    (inverseUnderlying q.eW M).hom ≫
      (inverseUnderlying q.cyclic.eW (q.restriction.obj M)).inv

/-- The scalar adjunction with the same named left functor as the endpoints. -/
@[irreducible] def scalarAdjunction
    {R S : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
    [MonObj R] [IsCommMonObj R] [MonObj S] [IsCommMonObj S]
    (a : R ⟶ S) [IsMonHom a] (X : Scheme.{u}) :
    derivedScalars a X ⊣ (Mod.comap (coefficientMap a X)).mapDerivedCategory := by
  unfold derivedScalars
  exact @Mod.derivedExtendMapDerivedCategoryAdjunction
    (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) _ _ _ _ _ _ _ _
    (condensedRingObj R X) (condensedRingObj S X) _ _
    (isCommMonObj_condensedRingObj R X) (isCommMonObj_condensedRingObj S X)
    (coefficientMap a X) _

/-- Additivity of the chosen inverse equivalence of a finite realization. -/
theorem inverse_additive
    {R : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
    [MonObj R] [IsCommMonObj R] {B : Type (u + 1)} [CommRing B]
    {X : Scheme.{u}} (e : FiniteRealization R B X) :
    e.F.asEquivalence.inverse.Additive := by
  let : e.F.asEquivalence.functor.Additive := inferInstanceAs e.F.Additive
  exact Equivalence.inverse_additive e.F.asEquivalence

attribute [local instance] inverse_additive

/-- The exact derived adjunction of a finite realization and its inverse. -/
@[irreducible] def finiteAdjunction
    {R : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
    [MonObj R] [IsCommMonObj R] {B : Type (u + 1)} [CommRing B]
    {X : Scheme.{u}} (e : FiniteRealization R B X) :
    e.F.mapDerivedCategory ⊣ e.F.asEquivalence.inverse.mapDerivedCategory := by
  letI : e.F.asEquivalence.functor.Additive := inferInstanceAs e.F.Additive
  letI : e.F.asEquivalence.inverse.Additive :=
    Equivalence.inverse_additive e.F.asEquivalence
  exact e.F.asEquivalence.mapDerivedCategory.toAdjunction

attribute [local semireducible] UniformizerSquareData.cyclicEndpoints
  UniformizerSquareData.quotientEndpoints

/-- The cyclic composite adjunction with its exact right functor collected. -/
@[irreducible] def cyclicAdjunction : q.cyclicFunctor ⊣ q.cyclicRight.mapDerivedCategory :=
  ((scalarAdjunction (cyclicMap l n) (diagonalSurface Y)).comp
    (finiteAdjunction q.cyclic.eW)).ofNatIsoRight
      (Functor.mapDerivedCategoryCompIso q.cyclic.eW.F.asEquivalence.inverse
        (Mod.comap (coefficientMap (cyclicMap l n) (diagonalSurface Y))))

/-- The successive composite adjunction with its exact right functor collected. -/
@[irreducible] def quotientAdjunction :
    q.quotientFunctor ⊣ q.quotientRight.mapDerivedCategory :=
  ((ScalarCompatibility.compositeAdjunction q.route.first q.route.second).comp
    (finiteAdjunction q.eW)).ofNatIsoRight
      (Functor.mapDerivedCategoryCompIso q.eW.F.asEquivalence.inverse
        (ScalarCompatibility.compositeRestriction q.route.first q.route.second))

/-- The derived mate of the ordinary restriction comparison. This is a construction
from actual adjunctions, independent of the diagonal arrow and both endpoint tests. -/
@[irreducible] def comparison (s : q.quotientRight ≅ q.restriction ⋙ q.cyclicRight) :
    q.cyclicFunctor ⟶ q.quotientFunctor ⋙ q.restriction.mapDerivedCategory :=
  restrictionMate q.cyclicAdjunction q.quotientAdjunction q.restriction.mapDerivedCategory
    (Functor.mapDerivedCategoryNatIso s ≪≫
      (Functor.mapDerivedCategoryCompIso q.restriction q.cyclicRight).symm)

end UniformizerSquareData
end AlgebraicGeometry.ProEtale.DiagonalCoefficients
