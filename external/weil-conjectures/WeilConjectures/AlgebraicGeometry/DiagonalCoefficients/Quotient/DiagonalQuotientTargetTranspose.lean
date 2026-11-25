/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.FiniteRealization.DiagonalRootRouteInsertions
import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.UniformizerSquareData.DiagonalQuotientEndpointTranspose
import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.Scalar.DiagonalScalarEndpointsTranspose

/-! # The successive target endpoint under its actual adjunction

Source: diagonal tower coefficient changes (1), normalized scalar extension.
(blueprint: lem-diagonal-quotient-target-transpose).
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

attribute [local instance 100000] sheafIsAbelian
attribute [local instance 200000] AlgebraicGeometry.ProEtale.diagonalAbSheafAbelian
attribute [local instance 300000] CommRing.toRing
attribute [local instance 400000] AlgebraicGeometry.ProEtale.diagonalModuleSheafAbelian
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
attribute [local irreducible] derivedScalars quotientLine cyclicLine
  Functor.mapDerivedCategory Functor.mapDerivedCategorySingleFunctor
  DerivedCategory.singleFunctors HomotopyCategory.singleFunctors HasDerivedCategory.standard
  DerivedCategory HasDerivedCategory.ofHasKInjectiveResolutions
  HasDerivedCategory.ofIsGrothendieckAbelian DerivedCategory.singleFunctorIsoCompQ
  CondensedRing.lowerStar Profinite.continuousMapRingSheaf
attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits
  UniformizerSquareData.inverse_additive

private theorem homEquiv_shift
    {C D : Type*} [Category C] [Category D] [HasShift C ℤ] [HasShift D ℤ]
    {F : C ⥤ D} {R : D ⥤ C} [F.CommShift ℤ] [R.CommShift ℤ]
    (a : F ⊣ R) [a.CommShift ℤ] {M : C} {N : D} (f : F.obj M ⟶ N) (k : ℤ) :
    a.homEquiv _ _ ((F.commShiftIso k).hom.app M ≫ f⟦k⟧') =
      (a.homEquiv _ _ f)⟦k⟧' ≫ (R.commShiftIso k).inv.app N := by
  have h : (a.homEquiv _ _ f)⟦k⟧' =
      a.homEquiv _ _ ((F.commShiftIso k).hom.app M ≫ f⟦k⟧') ≫
        (R.commShiftIso k).hom.app N := by
    simp only [Adjunction.homEquiv_unit, Functor.map_comp, Category.assoc]
    rw [a.shift_unit_app]
    simp only [Category.assoc]
    rw [Functor.commShiftIso_hom_naturality]
  exact ((R.commShiftIso k).app N).eq_comp_inv.mpr h.symm

namespace UniformizerSquareData

/-- The degree-two endpoint is the shifted degree-zero endpoint.
Source: diagonal tower coefficient changes (1)
(blueprint: lem-diagonal-quotient-target-transpose).
Proof: Use exact shift naturality to collect the successive shifted endpoint maps. -/
private theorem quotientTarget_shift
    {l : ℕ} [Fact l.Prime] {Y : Scheme.{u}}
    {E : PadicAlgCl.FiniteIntermediateField l} {π : PadicAlgCl.integers l E} {n : ℕ}
    {A : Type (u + 1)} [CommRing A] {hA : ((l ^ (n + 1) : ℕ) : A) = 0}
    (q : UniformizerSquareData l Y E π n A hA) :
    finiteTargetMap q.eW
      (ScalarCompatibility.compositeTarget q.route.first q.route.second)
      q.lineW.endpoint.iso =
      (((ScalarCompatibility.compositeFunctor q.route.first q.route.second) ⋙
        q.eW.F.mapDerivedCategory).commShiftIso (2 : ℤ)).hom.app _ ≫
      (quotientEndpointZero q)⟦(2 : ℤ)⟧' := by
  unfold quotientEndpointZero
  exact scalarRealizedEndpoints_shift q.route.first q.route.second q.eW
    q.lineW.endpoint.iso

end UniformizerSquareData

attribute [local semireducible] UniformizerSquareData.quotientAdjunction
  UniformizerSquareData.quotientEndpoints

/-- The successive endpoint transposes to the shifted single of its ordinary root insertion.

Source: latest blueprint, diagonal tower coefficient changes (1), scalar units and
finite realization; the first transposition in lem-diagonal-cyclic-uniformizer-target.
(blueprint: lem-diagonal-quotient-target-transpose).

Proof: expand the finite target map as the realized shifted scalar endpoint followed
by the finite single/shift comparisons and line isomorphism. Transpose first through
the derived finite equivalence: its counit is the derived ordinary counit. Exact single
coherence and the ordinary equivalence triangle identify this transpose with the single
of rootInsertion, followed by the inverse single comparison of the inverse equivalence.
Transpose through the quotient and integral scalar adjunctions, using each
Endpoint.normalization. Exact single
composition coherence collects the three ordinary restrictions into quotientRight. The
scalar shift is induced by that adjunction, and exact realization commutes with shifts,
so shifting the degree-zero calculation gives the displayed formula. No cyclic reduction,
scalar comparison from the cyclic ring to A,
or root-limit comparison is used. -/
theorem diagonalQuotientTargetTranspose
    (l : ℕ) [Fact l.Prime] (Y : Scheme.{u})
    (E : PadicAlgCl.FiniteIntermediateField l) (π : PadicAlgCl.integers l E) (n : ℕ)
    (A : Type (u + 1)) [CommRing A] (hA : ((l ^ (n + 1) : ℕ) : A) = 0)
    (q : UniformizerSquareData l Y E π n A hA) :
    q.quotientAdjunction.homEquiv _ _ q.quotientTarget =
      shiftedRootInsertion q.quotientRight q.quotientRootInsertion := by
  change (UniformizerSquareData.quotientAdjunctionAux q).homEquiv _ _
    (finiteTargetMap q.eW
      (ScalarCompatibility.compositeTarget q.route.first q.route.second)
      q.lineW.endpoint.iso) = _
  let := UniformizerSquareData.quotientAdjunction_commShift q
  exact (congrArg ((UniformizerSquareData.quotientAdjunctionAux q).homEquiv _ _)
      (UniformizerSquareData.quotientTarget_shift q)).trans
    ((homEquiv_shift (UniformizerSquareData.quotientAdjunctionAux q)
      (UniformizerSquareData.quotientEndpointZero q) (2 : ℤ)).trans
        (congrArg (fun f ↦ f⟦(2 : ℤ)⟧' ≫
          (q.quotientRight.mapDerivedCategory.commShiftIso (2 : ℤ)).inv.app _)
            (UniformizerSquareData.quotientEndpointZero_transpose q)))

end AlgebraicGeometry.ProEtale.DiagonalCoefficients
