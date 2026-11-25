/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Algebra.Homology.OpenTensorNormalization.RestrictionSquare.LeftEq
public import WeilConjectures.Algebra.Homology.OpenTensorNormalization.RestrictionSquare.RightEq
public import WeilConjectures.Algebra.Homology.OpenTensorNormalization.RestrictionSquare.SquareEq

/-! # Assembly of the finite restriction representative square -/

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

/-- The representative square from its two halves and the chain-level equation.
(blueprint: lem-sf-finite-restriction-representative-square) -/
theorem squareEq_of_halves (P Q : CochainComplex (FiniteModules A X) ℤ)
    (hp : resolving (finiteInput A gU j' j g sq).R
      ((finiteComplexRealization e.realizeX).obj P))
    (hq : resolving (finiteInput A gU j' j g sq).R
      ((finiteComplexRealization e.realizeX).obj Q))
    (hL : LeftEq A gU j' j g sq o e P Q hp hq) (hR : RightEq A gU j' j g sq o e P Q hp hq)
    (h_total :
    let R := (finiteInput A gU j' j g sq).R
    letI : (restrict .ordinary j R).Additive := (restriction_exact .ordinary j R).1
    let fc := (ProEtale.upperStar (ModuleCat.{u + 1} A) j).mapHomologicalComplex (.up ℤ)
    let h := (restrict .ordinary j R).mapHomologicalComplex (.up ℤ)
    let v := NatTrans.mapHomologicalComplex e.open_pin.star.hom (.up ℤ)
    ∀ P Q : CochainComplex (FiniteModules A X) ℤ,
      (finiteComplexRealization e.realizeU).map
          (inv (((Functor.OplaxMonoidal.mapHomologicalComplexδNatTrans (.up ℤ)
            (ProEtale.upperStar (ModuleCat.{u + 1} A) j)).app P).app Q)) ≫
        v.app (finiteTotal A X P Q) ≫
        h.map (e.tensorX_pin.totalIso P Q).hom =
      (e.tensorU_pin.totalIso (fc.obj P) (fc.obj Q)).hom ≫
        (total (restrictRing .ordinary j R)).map
          (Prod.mkHom (v.app P) (v.app Q)) ≫
        totalMap o.tensorX o.tensorU (restrict .ordinary j R) o.restrictionTensor
          o.tensorComparison.comm ((finiteComplexRealization e.realizeX).obj P)
            ((finiteComplexRealization e.realizeX).obj Q)) :
    SquareEq A gU j' j g sq o e P Q := by
  have := suffix_isIso A gU j' j g sq o e P Q hp hq
  exact ⟨(cancel_mono (suffix A gU j' j g sq o e P Q hp hq)).1 (hL.eq.trans
    ((congrArg (fun z ↦ restrictionTransport% ≫ DerivedCategory.Q.map z) (h_total P Q)).trans
      hR.eq.symm))⟩

end SheafOfModules.OpenTensorNormalization.RestrictionSquare
