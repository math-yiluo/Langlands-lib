/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Algebra.Homology.OpenTensorNormalization.MixedRepresentationNormalized
public import WeilConjectures.Algebra.Homology.OpenTensorNormalization.OpenTensorNormalizationData
public import WeilConjectures.Algebra.Homology.OpenTensorNormalization.RepresentativeSquareCancellation

/-!
# Named terms of the finite restriction representative square

The two sides of the chain-level equation `h_total` and of the representative square in
`finite_restriction_representative_square`, the transport prefix and the cancellable
suffix, as definitions. Stating the intermediate lemmas with these names keeps their
statements syntactically equal across files, so the final assembly is kernel-cheap.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.Scheme.ProjectionRestriction
namespace SheafOfModules.OpenTensorNormalization.RestrictionSquare

/-- The source of a morphism. -/
abbrev homSource {C : Type*} [Category C] {X Y : C} (_f : X ⟶ Y) : C := X

variable (A : Type (u + 1)) [CommRing A] [Finite A]
    {U' U X' X : Scheme.{u}} (gU : U' ⟶ U) (j' : U' ⟶ X')
    (j : U ⟶ X) (g : X' ⟶ X) (sq : OpenImmersionSquare gU j' j g)
    [IsOpenImmersion j] [IsOpenImmersion j']
    {t : SiteSquare (finiteInput A gU j' j g sq)}
    (o : Operations (finiteInput A gU j' j g sq) t)
    (e : FiniteComparisons A o)

set_option hygiene false in
/-- The transport prefix: the derived tensorator on `U` followed by the realization
factorization at the target of the lax tensorator. It is a notation rather than a definition,
so that its elaborated proof terms are syntactically those of the surrounding statement.
It refers to the variables `A`, `U`, `j`, `e`, `P`, `Q` of the use site. -/
scoped macro "restrictionTransport%" : term =>
  `(e.realizeU.derived.map
      (((ProEtale.upperStar (ModuleCat.{u + 1} A) j).mapDerivedCategoryFactors.hom.app P ⊗ₘ
        ((ProEtale.upperStar (ModuleCat.{u + 1} A)
          j).leftDerivedFunctorIsoMapDerivedCategory.hom.app
          (DerivedCategory.Q.obj Q) ≫
          (ProEtale.upperStar (ModuleCat.{u + 1} A) j).mapDerivedCategoryFactors.hom.app Q)) ≫
        Functor.LaxMonoidal.μ (DerivedCategory.Q (C := FiniteModules A U))
          (((ProEtale.upperStar (ModuleCat.{u + 1} A) j).mapHomologicalComplex (.up ℤ)).obj
            P)
          (((ProEtale.upperStar (ModuleCat.{u + 1} A) j).mapHomologicalComplex (.up ℤ)).obj
            Q)) ≫
    e.realizeU.equivalence.functor.mapDerivedCategoryFactors.hom.app _)

/-- The cancellable suffix: restriction of the inverse ringed tensor representative
followed by the restriction factorization. -/
def suffix (P Q : CochainComplex (FiniteModules A X) ℤ)
    (hp : resolving (finiteInput A gU j' j g sq).R
      ((finiteComplexRealization e.realizeX).obj P))
    (hq : resolving (finiteInput A gU j' j g sq).R
      ((finiteComplexRealization e.realizeX).obj Q)) :=
  o.opens.jStar.map
      (o.tensorX.functor.map
          (Prod.mkHom (e.realizeX.equivalence.functor.mapDerivedCategoryFactors.hom.app P)
            (e.realizeX.equivalence.functor.mapDerivedCategoryFactors.hom.app Q)) ≫
        (o.tensorX.representative.app (⟨_, hp⟩, ⟨_, hq⟩)).inv) ≫
    (restrict .ordinary j (finiteInput A gU j' j g sq).R).mapDerivedCategoryFactors.hom.app
      ((total (finiteInput A gU j' j g sq).R).obj
        ((finiteComplexRealization e.realizeX).obj P, (finiteComplexRealization e.realizeX).obj Q))

set_option linter.unusedSectionVars false in
/-- The cancellable suffix is invertible. -/
theorem suffix_isIso (P Q : CochainComplex (FiniteModules A X) ℤ)
    (hp : resolving (finiteInput A gU j' j g sq).R
      ((finiteComplexRealization e.realizeX).obj P))
    (hq : resolving (finiteInput A gU j' j g sq).R
      ((finiteComplexRealization e.realizeX).obj Q)) :
    IsIso (suffix A gU j' j g sq o e P Q hp hq) :=
  representative_suffix_isIso (QX := DerivedCategory.Q) (QR := DerivedCategory.Q)
    (QS := DerivedCategory.Q) (EXd := e.realizeX.derived) (J := o.opens.jStar)
    (TR := o.tensorX.functor) (totR := total (finiteInput A gU j' j g sq).R)
    (x := e.realizeX.equivalence.functor.mapDerivedCategoryFactors)
    (b := (restrict .ordinary j (finiteInput A gU j' j g sq).R).mapDerivedCategoryFactors) P Q
    (o.tensorX.representative.app (⟨_, hp⟩, ⟨_, hq⟩)) _ rfl

end SheafOfModules.OpenTensorNormalization.RestrictionSquare
