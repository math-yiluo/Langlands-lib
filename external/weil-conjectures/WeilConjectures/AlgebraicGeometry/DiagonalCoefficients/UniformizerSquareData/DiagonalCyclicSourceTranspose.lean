/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.UniformizerSquareData.DiagonalDerivedSourceMaps
import all WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.DiagonalSourceAdjunctionTransport

/-! # Transpose of the cyclic supported endpoint

Source: diagonal tower coefficient changes (1), exact scalar and finite-realization adjunctions.
(blueprint: lem-diagonal-source-cyclic-transpose).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option genSizeOf false
set_option genInjectivity false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.DiagonalCoefficients

-- Use the module-sheaf abelian structure of GeoCartierClass.
attribute [local instance 100000] sheafIsAbelian
attribute [local instance 200000] AlgebraicGeometry.ProEtale.diagonalAbSheafAbelian
attribute [local instance 300000] CommRing.toRing
attribute [local instance 400000] AlgebraicGeometry.ProEtale.diagonalModuleSheafAbelian

set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

attribute [local irreducible] derivedScalars quotientLine quotientLineMap cyclicLine cyclicLineMap
  Functor.leftDerivedFunctor Mod.derivedExtendMapDerivedCategoryAdjunction
  HasDerivedCategory.standard DerivedCategory.singleFunctors HomotopyCategory.singleFunctors
  DerivedCategory.singleFunctorIsoCompQ
  Functor.mapDerivedCategory Functor.mapDerivedCategorySingleFunctor
  CondensedRing.lowerStar Profinite.continuousMapRingSheaf
  HasDerivedCategory.ofHasKInjectiveResolutions HasDerivedCategory.ofIsGrothendieckAbelian

attribute [local semireducible] UniformizerSquareData.cyclicEndpoints
  UniformizerSquareData.quotientEndpoints

attribute [local instance] UniformizerSquareData.inverse_additive
  comp_preservesFiniteLimits comp_preservesFiniteColimits

attribute [local semireducible] UniformizerSquareData.finiteAdjunction

private theorem realized_endpoint_transpose
    {R S : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
    [MonObj R] [IsCommMonObj R] [MonObj S] [IsCommMonObj S]
    {a : R ⟶ S} [IsMonHom a] {X : Scheme.{u}}
    {M : Modules R X} {N : Modules S X} {m : M.X ⟶ N.X}
    (d : Endpoint a M N m) {A : Type (u + 1)} [CommRing A]
    (e : FiniteRealization S A X)
    (P : Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A)) (g : e.F.obj N ≅ P) :
    (((UniformizerSquareData.scalarAdjunction a X).comp
        (UniformizerSquareData.finiteAdjunction e)).ofNatIsoRight
          (Functor.mapDerivedCategoryCompIso e.F.asEquivalence.inverse
            (Mod.comap (coefficientMap a X)))).homEquiv _ _
        (finiteSourceIso e d.iso g).hom =
      (DerivedCategory.singleFunctor _ 0).map
          (d.semilinear.hom ≫ (Mod.comap (coefficientMap a X)).map
            (e.F.asEquivalence.toAdjunction.homEquiv _ _ g.hom)) ≫
        ((e.F.asEquivalence.inverse ⋙
          Mod.comap (coefficientMap a X)).mapDerivedCategorySingleFunctor 0).inv.app P := by
  let : e.F.asEquivalence.functor.Additive := inferInstanceAs e.F.Additive
  exact finite_homEquiv_single (Mod.comap (coefficientMap a X))
    (UniformizerSquareData.scalarAdjunction a X) e.F.asEquivalence M N P
    d.iso.hom g.hom d.semilinear.hom (endpoint_scalar_normalization d)

namespace UniformizerSquareData

variable {l : ℕ} [Fact l.Prime] {Y : Scheme.{u}}
  {E : PadicAlgCl.FiniteIntermediateField l} {π : PadicAlgCl.integers l E} {n : ℕ}
  {A : Type (u + 1)} [CommRing A] {hA : ((l ^ (n + 1) : ℕ) : A) = 0}
  (q : UniformizerSquareData l Y E π n A hA)

attribute [local semireducible] cyclicAdjunction

/-- The supported endpoint transpose in degree zero.
Source: coefficient changes (1). (blueprint: lem-diagonal-source-cyclic-transpose).
Proof: apply exact single-object adjunction transport to the supplied scalar endpoint
normalization and finite realization. For the successive route, first compose the two
scalar normalizations. -/
theorem cyclic_transpose : q.cyclicTranspose = q.cyclicSingleNormalized := by
  unfold cyclicTranspose cyclicSingleNormalized cyclicOrdinary
  exact realized_endpoint_transpose q.cyclic.supported q.cyclic.eW _
    q.cyclic.sourceComparison.iso

end UniformizerSquareData
end AlgebraicGeometry.ProEtale.DiagonalCoefficients
