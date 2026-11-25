/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Algebra.Homology.OpenTensorNormalization.RestrictionSquare.RightEq
public import WeilConjectures.Algebra.Homology.OpenTensorNormalization.RestrictionSquare.Resolving
public import WeilConjectures.Algebra.Homology.OpenTensorNormalization.RepresentativeSquareCancellation

/-! # The right half of the finite restriction representative square -/

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
/-- The right half: the tensor model on `U`, the ringed tensor comparison and the open pin.
(blueprint: lem-sf-finite-restriction-representative-square) -/
theorem rightEq (P Q : CochainComplex (FiniteModules A X) ℤ)
    (hp : resolving (finiteInput A gU j' j g sq).R
      ((finiteComplexRealization e.realizeX).obj P))
    (hq : resolving (finiteInput A gU j' j g sq).R
      ((finiteComplexRealization e.realizeX).obj Q)) :
    RightEq A gU j' j g sq o e P Q hp hq := by
  constructor
  let : (restrict .ordinary j (finiteInput A gU j' j g sq).R).Additive :=
    (restriction_exact .ordinary j (finiteInput A gU j' j g sq).R).1
  have hpL := o.tensorComparison.preserves ((finiteComplexRealization e.realizeX).obj P) hp
  have hqL := o.tensorComparison.preserves ((finiteComplexRealization e.realizeX).obj Q) hq
  have hpU : resolving (restrictRing .ordinary j (finiteInput A gU j' j g sq).R)
      ((finiteComplexRealization e.realizeU).obj
        (((ProEtale.upperStar (ModuleCat.{u + 1} A) j).mapHomologicalComplex (.up ℤ)).obj P)) :=
    resolving_of_iso (restrictRing .ordinary j (finiteInput A gU j' j g sq).R)
    ((NatIso.mapHomologicalComplex e.open_pin.star (.up ℤ)).app P) hpL
  have hqU : resolving (restrictRing .ordinary j (finiteInput A gU j' j g sq).R)
      ((finiteComplexRealization e.realizeU).obj
        (((ProEtale.upperStar (ModuleCat.{u + 1} A) j).mapHomologicalComplex (.up ℤ)).obj Q)) :=
    resolving_of_iso (restrictRing .ordinary j (finiteInput A gU j' j g sq).R)
    ((NatIso.mapHomologicalComplex e.open_pin.star (.up ℤ)).app Q) hqL
  have hv := o.tensorU.representative.hom.naturality
    (Prod.mkHom
      (show (⟨_, hpU⟩ : (resolving
          (restrictRing .ordinary j (finiteInput A gU j' j g sq).R)).FullSubcategory) ⟶
        ⟨_, hpL⟩ from ObjectProperty.homMk
          ((NatTrans.mapHomologicalComplex e.open_pin.star.hom (.up ℤ)).app P))
      (show (⟨_, hqU⟩ : (resolving
          (restrictRing .ordinary j (finiteInput A gU j' j g sq).R)).FullSubcategory) ⟶
        ⟨_, hqL⟩ from ObjectProperty.homMk
          ((NatTrans.mapHomologicalComplex e.open_pin.star.hom (.up ℤ)).app Q)))
  exact representative_square_right
    (QX := DerivedCategory.Q) (QU := DerivedCategory.Q) (QR := DerivedCategory.Q)
    (QS := DerivedCategory.Q)
    (fc := (ProEtale.upperStar (ModuleCat.{u + 1} A) j).mapHomologicalComplex (.up ℤ))
    (xc := finiteComplexRealization e.realizeX) (uc := finiteComplexRealization e.realizeU)
    (lc := (restrict .ordinary j (finiteInput A gU j' j g sq).R).mapHomologicalComplex (.up ℤ))
    (totR := total (finiteInput A gU j' j g sq).R)
    (totS := total (restrictRing .ordinary j (finiteInput A gU j' j g sq).R))
    (EXd := e.realizeX.derived) (EUd := e.realizeU.derived)
    (Fd := (ProEtale.upperStar (ModuleCat.{u + 1} A) j).mapDerivedCategory)
    (FL := (ProEtale.upperStar (ModuleCat.{u + 1} A) j).leftDerivedFunctor)
    (J := o.opens.jStar) (TU := finiteTensor A U)
    (TR := o.tensorX.functor) (TS := o.tensorU.functor)
    (x := e.realizeX.equivalence.functor.mapDerivedCategoryFactors)
    (y := e.realizeU.equivalence.functor.mapDerivedCategoryFactors)
    (a := (ProEtale.upperStar (ModuleCat.{u + 1} A) j).mapDerivedCategoryFactors)
    (b := (restrict .ordinary j (finiteInput A gU j' j g sq).R).mapDerivedCategoryFactors)
    (LIso := (ProEtale.upperStar (ModuleCat.{u + 1} A) j).leftDerivedFunctorIsoMapDerivedCategory)
    (oP := e.openPull) (tUd := e.tensorU) (cmp := o.tensorComparison.comparison)
    (v := NatTrans.mapHomologicalComplex e.open_pin.star.hom (.up ℤ))
    (P := P) (Q := Q) (TUc := _)
    (muU := Functor.LaxMonoidal.μ (DerivedCategory.Q (C := FiniteModules A U))
      (((ProEtale.upperStar (ModuleCat.{u + 1} A) j).mapHomologicalComplex (.up ℤ)).obj P)
      (((ProEtale.upperStar (ModuleCat.{u + 1} A) j).mapHomologicalComplex (.up ℤ)).obj Q))
    (tiU := e.tensorU_pin.totalIso _ _)
    (txI := o.tensorX.representative.app (⟨_, hp⟩, ⟨_, hq⟩))
    (tuI := o.tensorU.representative.app (⟨_, hpU⟩, ⟨_, hqU⟩))
    (tlI := o.tensorU.representative.app (⟨_, hpL⟩, ⟨_, hqL⟩))
    (w := totalMap o.tensorX o.tensorU _ o.restrictionTensor o.tensorComparison.comm
      ((finiteComplexRealization e.realizeX).obj P) ((finiteComplexRealization e.realizeX).obj Q))
    (k := suffix A gU j' j g sq o e P Q hp hq)
    (n := (ProEtale.upperStar (ModuleCat.{u + 1} A) j).mapDerivedCategoryFactors.hom.app P ⊗ₘ
      ((ProEtale.upperStar (ModuleCat.{u + 1} A) j).leftDerivedFunctorIsoMapDerivedCategory.hom.app
        (DerivedCategory.Q.obj Q) ≫
        (ProEtale.upperStar (ModuleCat.{u + 1} A) j).mapDerivedCategoryFactors.hom.app Q))
    (tr := restrictionTransport%) (hk := rfl) (htr := rfl) (hn := rfl)
    (hu := e.tensorU_pin.model _ _ hpU hqU) (hr := e.open_pin.models.2)
    (hrep := o.tensorComparison.representative _ _ hp hq) (hv := hv)

end SheafOfModules.OpenTensorNormalization.RestrictionSquare
