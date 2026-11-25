/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Algebra.Homology.OpenTensorNormalization.RestrictionSquare.LeftEq
public import WeilConjectures.Algebra.Homology.OpenTensorNormalization.RestrictionSquare.MixedFinite
public import WeilConjectures.Algebra.Homology.OpenTensorNormalization.RepresentativeSquareCancellation

/-! # The left half of the finite restriction representative square -/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.Scheme.ProjectionRestriction
namespace SheafOfModules.OpenTensorNormalization.RestrictionSquare

variable (A : Type (u + 1)) [CommRing A] [Finite A]
    {U' U X' X : Scheme.{u}} (gU : U' ⟶ U) (j' : U' ⟶ X')
    (j : U ⟶ X) (g : X' ⟶ X) (sq : OpenImmersionSquare gU j' j g)
    [IsOpenImmersion j] [IsOpenImmersion j']
    {t : SiteSquare (finiteInput A gU j' j g sq)}
    (o : Operations (finiteInput A gU j' j g sq) t)
    (e : FiniteComparisons A o)

set_option linter.unusedSectionVars false in
/-- The left half: the restricted tensor model, the open pin and the mixed representative
equation. (blueprint: lem-sf-finite-restriction-representative-square) -/
theorem leftEq (P Q : CochainComplex (FiniteModules A X) ℤ)
    (hp : resolving (finiteInput A gU j' j g sq).R
      ((finiteComplexRealization e.realizeX).obj P))
    (hq : resolving (finiteInput A gU j' j g sq).R
      ((finiteComplexRealization e.realizeX).obj Q)) :
    LeftEq A gU j' j g sq o e P Q hp hq := by
  constructor
  let : (restrict .ordinary j (finiteInput A gU j' j g sq).R).Additive :=
    (restriction_exact .ordinary j (finiteInput A gU j' j g sq).R).1
  exact representative_square_left
    (QX := DerivedCategory.Q) (QU := DerivedCategory.Q) (QR := DerivedCategory.Q)
    (QS := DerivedCategory.Q)
    (fc := (ProEtale.upperStar (ModuleCat.{u + 1} A) j).mapHomologicalComplex (.up ℤ))
    (xc := finiteComplexRealization e.realizeX) (uc := finiteComplexRealization e.realizeU)
    (lc := (restrict .ordinary j (finiteInput A gU j' j g sq).R).mapHomologicalComplex (.up ℤ))
    (totR := total (finiteInput A gU j' j g sq).R)
    (EXd := e.realizeX.derived) (EUd := e.realizeU.derived)
    (Fd := (ProEtale.upperStar (ModuleCat.{u + 1} A) j).mapDerivedCategory)
    (FL := (ProEtale.upperStar (ModuleCat.{u + 1} A) j).leftDerivedFunctor)
    (J := o.opens.jStar) (TX := finiteTensor A X) (TU := finiteTensor A U)
    (TR := o.tensorX.functor)
    (x := e.realizeX.equivalence.functor.mapDerivedCategoryFactors)
    (y := e.realizeU.equivalence.functor.mapDerivedCategoryFactors)
    (a := (ProEtale.upperStar (ModuleCat.{u + 1} A) j).mapDerivedCategoryFactors)
    (b := (restrict .ordinary j (finiteInput A gU j' j g sq).R).mapDerivedCategoryFactors)
    (LIso := (ProEtale.upperStar (ModuleCat.{u + 1} A) j).leftDerivedFunctorIsoMapDerivedCategory)
    (oP := e.openPull) (tXd := e.tensorX)
    (v := NatTrans.mapHomologicalComplex e.open_pin.star.hom (.up ℤ))
    (P := P) (Q := Q) (TPQ := finiteTotal A X P Q)
    (TUc := _)
    (muX := Functor.LaxMonoidal.μ DerivedCategory.Q P Q)
    (muU := Functor.LaxMonoidal.μ (DerivedCategory.Q (C := FiniteModules A U))
      (((ProEtale.upperStar (ModuleCat.{u + 1} A) j).mapHomologicalComplex (.up ℤ)).obj P)
      (((ProEtale.upperStar (ModuleCat.{u + 1} A) j).mapHomologicalComplex (.up ℤ)).obj Q))
    (c := ((Functor.OplaxMonoidal.mapHomologicalComplexδNatTrans (.up ℤ)
      (ProEtale.upperStar (ModuleCat.{u + 1} A) j)).app P).app Q)
    (delta := ((ProEtale.mapDerivedCategoryUpperStarDerivedTensorIso
      (ModuleCat.{u + 1} A) j).hom.app (DerivedCategory.Q.obj P)).app (DerivedCategory.Q.obj Q))
    (tiX := e.tensorX_pin.totalIso P Q)
    (txI := o.tensorX.representative.app (⟨_, hp⟩, ⟨_, hq⟩))
    (k := suffix A gU j' j g sq o e P Q hp hq)
    (n := (ProEtale.upperStar (ModuleCat.{u + 1} A) j).mapDerivedCategoryFactors.hom.app P ⊗ₘ
      ((ProEtale.upperStar (ModuleCat.{u + 1} A) j).leftDerivedFunctorIsoMapDerivedCategory.hom.app
        (DerivedCategory.Q.obj Q) ≫
        (ProEtale.upperStar (ModuleCat.{u + 1} A) j).mapDerivedCategoryFactors.hom.app Q))
    (tr := restrictionTransport%) (hk := rfl) (htr := rfl)
    (hx := e.tensorX_pin.model P Q hp hq) (hr := e.open_pin.models.2)
    (hm := mixed_representation_finite A j P Q)

end SheafOfModules.OpenTensorNormalization.RestrictionSquare
