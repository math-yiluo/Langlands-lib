/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.UniformizerSquareData.DiagonalCoefficientRouteComparison

/-! # Ordinary root insertions for the two coefficient routes

Source: diagonal tower coefficient changes (1), ordinary scalar adjunction units.
(blueprint: def-diagonal-root-route-insertions).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option genSizeOf false
set_option genInjectivity false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.Obj CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.DiagonalCoefficients

attribute [local instance 100000] sheafIsAbelian
attribute [local instance 200000] AlgebraicGeometry.ProEtale.diagonalAbSheafAbelian
attribute [local instance 300000] CommRing.toRing
attribute [local instance 400000] AlgebraicGeometry.ProEtale.diagonalModuleSheafAbelian
attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits
attribute [local irreducible] derivedScalars quotientLine cyclicLine
  Functor.mapDerivedCategory Functor.mapDerivedCategorySingleFunctor
  DerivedCategory.singleFunctors HomotopyCategory.singleFunctors
  HasDerivedCategory.standard

/-- Transpose an ordinary line isomorphism under the finite equivalence.
Source: coefficient changes (1) (blueprint: def-diagonal-root-route-insertions). -/
def FiniteRealization.rootInsertion
    {R : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
    [MonObj R] [IsCommMonObj R] {B : Type (u + 1)} [CommRing B]
    {X : Scheme.{u}} (e : FiniteRealization R B X) (M : Modules R X)
    {N : Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} B)} (i : e.F.obj M ≅ N) :
    M ⟶ e.F.asEquivalence.inverse.obj N :=
  e.F.asEquivalence.unitIso.hom.app M ≫ e.F.asEquivalence.inverse.map i.hom

/-- Forgetting the finite-equivalence transpose recovers the specified underlying map.
Source: equivalence triangle identity (blueprint: def-diagonal-root-route-insertions). -/
theorem FiniteRealization.rootInsertion_underlying
    {R : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
    [MonObj R] [IsCommMonObj R] {B : Type (u + 1)} [CommRing B]
    {X : Scheme.{u}} (e : FiniteRealization R B X) (M : Modules R X)
    {N : Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} B)} (i : e.F.obj M ≅ N) :
    (e.rootInsertion M i).hom ≫ (UniformizerSquareData.inverseUnderlying e N).hom =
      e.underlying.inv.app M ≫
        (sheafCompose (Scheme.ProEt.topology X)
          (forget₂ (ModuleCat.{u + 1} B) Ab.{u + 1})).map i.hom := by
  let U := sheafCompose (Scheme.ProEt.topology X)
    (forget₂ (ModuleCat.{u + 1} B) Ab.{u + 1})
  let f := e.rootInsertion M i
  have hn := e.underlying.inv.naturality f
  change f.hom ≫ e.underlying.inv.app (e.F.asEquivalence.inverse.obj N) =
    e.underlying.inv.app M ≫ U.map (e.F.map f) at hn
  unfold UniformizerSquareData.inverseUnderlying
  change f.hom ≫ e.underlying.inv.app (e.F.asEquivalence.inverse.obj N) ≫
    U.map (e.F.asEquivalence.counitIso.hom.app N) = _
  have hh := congrArg (fun z ↦ z ≫ U.map (e.F.asEquivalence.counitIso.hom.app N)) hn
  have he : e.F.map f ≫ e.F.asEquivalence.counitIso.hom.app N = i.hom := by
    have hi := e.F.asEquivalence.counitIso.hom.naturality i.hom
    change e.F.map (e.F.asEquivalence.inverse.map i.hom) ≫
      e.F.asEquivalence.counitIso.hom.app N =
      e.F.asEquivalence.counitIso.hom.app (e.F.obj M) ≫ i.hom at hi
    calc
      _ = e.F.map (e.F.asEquivalence.unitIso.hom.app M) ≫
          (e.F.map (e.F.asEquivalence.inverse.map i.hom) ≫
            e.F.asEquivalence.counitIso.hom.app N) := by
        dsimp only [f, FiniteRealization.rootInsertion]
        exact (e.F.map_comp _ _ ▸ Category.assoc _ _ _)
      _ = e.F.map (e.F.asEquivalence.unitIso.hom.app M) ≫
          (e.F.asEquivalence.counitIso.hom.app (e.F.obj M) ≫ i.hom) := congrArg _ hi
      _ = (e.F.map (e.F.asEquivalence.unitIso.hom.app M) ≫
          e.F.asEquivalence.counitIso.hom.app (e.F.obj M)) ≫ i.hom :=
        (Category.assoc _ _ _).symm
      _ = i.hom := (congrArg (· ≫ i.hom)
        (e.F.asEquivalence.functor_unitIso_comp M)).trans (Category.id_comp _)
  have hh' : f.hom ≫ e.underlying.inv.app (e.F.asEquivalence.inverse.obj N) ≫
      U.map (e.F.asEquivalence.counitIso.hom.app N) =
      e.underlying.inv.app M ≫ U.map
        (e.F.map f ≫ e.F.asEquivalence.counitIso.hom.app N) := by
    exact ((Category.assoc _ _ _).symm.trans hh).trans
      ((Category.assoc _ _ _).trans
        (congrArg (e.underlying.inv.app M ≫ ·) (U.map_comp _ _).symm))
  exact hh'.trans (congrArg (fun z ↦ e.underlying.inv.app M ≫ U.map z) he)

namespace UniformizerSquareData
variable {l : ℕ} [Fact l.Prime] {Y : Scheme.{u}}
  {E : PadicAlgCl.FiniteIntermediateField l} {π : PadicAlgCl.integers l E} {n : ℕ}
  {A : Type (u + 1)} [CommRing A] {hA : ((l ^ (n + 1) : ℕ) : A) = 0}
  (q : UniformizerSquareData l Y E π n A hA)

/-- The cyclic semilinear root map followed by the finite-equivalence transpose.
Source: coefficient changes (1) (blueprint: def-diagonal-root-route-insertions). -/
def cyclicRootInsertion :
    zlLine l (diagonalSurface Y) ⟶ q.cyclicRight.obj
      (geoCartierLine (diagonalResidue.{u} l n) (l ^ (n + 1))
        (cartierResidue_cast l (n + 1)) (diagonalSurface Y)) :=
  q.cyclic.line.semilinear.hom ≫
    (Mod.comap (coefficientMap (cyclicMap l n) (diagonalSurface Y))).map
      (q.cyclic.eW.rootInsertion _ q.cyclic.lineEndpoint.iso)

/-- The successive ordinary root map, transposed through the finite equivalence.
Source: coefficient changes (1) (blueprint: def-diagonal-root-route-insertions). -/
def quotientRootInsertion :
    zlLine l (diagonalSurface Y) ⟶ q.quotientRight.obj
      (geoCartierLine A (l ^ (n + 1)) hA (diagonalSurface Y)) :=
  q.route.first.lineW.semilinear.hom ≫
    (Mod.comap (coefficientMap (integralMap l E) (diagonalSurface Y))).map
      (q.route.second.lineW.semilinear.hom ≫
        (Mod.comap (coefficientMap (quotientMap l E π n) (diagonalSurface Y))).map
          (q.eW.rootInsertion _ q.lineW.endpoint.iso))

end UniformizerSquareData

/-- The shifted exact-single insertion into a derived right functor.
Source: coefficient changes (1) (blueprint: def-diagonal-root-route-insertions). -/
def shiftedRootInsertion
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D]
    (R : D ⥤ C) [R.Additive] [PreservesFiniteLimits R] [PreservesFiniteColimits R]
    {M : C} {N : D} (f : M ⟶ R.obj N) :
    ((DerivedCategory.singleFunctor C 0).obj M)⟦(2 : ℤ)⟧ ⟶
      R.mapDerivedCategory.obj (((DerivedCategory.singleFunctor D 0).obj N)⟦(2 : ℤ)⟧) :=
  ((DerivedCategory.singleFunctor C 0).map f ≫
    (R.mapDerivedCategorySingleFunctor 0).inv.app N)⟦(2 : ℤ)⟧' ≫
      (R.mapDerivedCategory.commShiftIso (2 : ℤ)).inv.app _

end AlgebraicGeometry.ProEtale.DiagonalCoefficients
