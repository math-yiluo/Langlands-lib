/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import Mathlib.Algebra.Homology.Localization
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
public import WeilConjectures.AlgebraicGeometry.IntegralDerivedReduction
public import WeilConjectures.AlgebraicGeometry.IntegralReductionTowerWellDefinedUnrestricted
public import WeilConjectures.AlgebraicGeometry.NormalizedDVRTower
import all WeilConjectures.AlgebraicGeometry.IntegralReductionTowerUnrestricted

/-! # Quotient transitions on K-flat representatives -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe d t u
open CategoryTheory CategoryTheory.Limits Opposite
namespace WeilConjectures
attribute [local irreducible] completedIntegralCoefficientSheafUnrestricted
  scalarReductionDerivedExistence normalizedDVRResCompletedComp
  scalarReductionDerivedExtension scalarReductionCounit

section AdjunctionHelpers
universe a b c v w z
variable {A : Type a} {B : Type b} {C : Type c}
  [Category.{v} A] [Category.{w} B] [Category.{z} C]
  {F : A ⥤ B} {R : B ⥤ A} {G : A ⥤ C} {S : C ⥤ A}
  (H : C ⥤ B) (i : H ⋙ R ≅ S) (adj : F ⊣ R) (adjn : G ⊣ S)

end AdjunctionHelpers

section TensorHelpers
universe a b r
variable {C : Type a} [Category.{b} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{r}] [HasWeakSheafify J AddCommGrpCat.{r}]
  {R S T : Sheaf J CommRingCat.{r}}
  (f : R ⟶ S) (g : R ⟶ T) (q : S ⟶ T) (hq : f ≫ q = g)
open SheafOfModules.UnrestrictedTowerProof

private noncomputable def tensorRestrictionComp : res q ⋙ res f ≅ res g :=
  normalizedDVRRestrictionCompIso
    ((sheafCompose J (forget₂ CommRingCat RingCat)).map f)
    ((sheafCompose J (forget₂ CommRingCat RingCat)).map q) ≪≫
  eqToIso (congrArg (fun k ↦ SheafOfModules.restrictScalars.{r} k)
    (by simpa only [Functor.map_comp] using
      congrArg ((sheafCompose J (forget₂ CommRingCat RingCat)).map) hq))

variable
  (F : SheafOfModules.{r} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R) ⥤
    SheafOfModules.{r} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj S))
  (G : SheafOfModules.{r} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R) ⥤
    SheafOfModules.{r} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj T))
  (hf : ∀ N, F.obj N = SheafOfModules.changeOfRings f N)
  (hg : ∀ N, G.obj N = SheafOfModules.changeOfRings g N)

private noncomputable def finiteMap
    (M : SheafOfModules.{r} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) :
    F.obj M ⟶ (res q).obj (G.obj M) :=
  eqToHom (hf M) ≫ sheafMap f g q hq M ≫ (res q).map (eqToHom (hg M).symm)

attribute [local irreducible] finiteMap tensorRestrictionComp

end TensorHelpers

attribute [local irreducible] SheafOfModules.changeOfRings
  SheafOfModules.changeOfRingsHom

attribute [local irreducible] SheafOfModules.UnrestrictedTowerProof.identifiedMap
  SheafOfModules.UnrestrictedTowerProof.sheafMap
  SheafOfModules.UnrestrictedTowerProof.restrictedMap
  SheafOfModules.UnrestrictedTowerProof.tensorSection

section ExactHelpers
universe a b c v w z
variable {A : Type a} {B : Type b} {C : Type c}
  [Category.{v} A] [Category.{w} B] [Category.{z} C]
  [Abelian A] [Abelian B] [Abelian C]
  [HasDerivedCategory A] [HasDerivedCategory B] [HasDerivedCategory C]
  (H : A ⥤ B) (R : B ⥤ C) (S : A ⥤ C)
  [H.Additive] [R.Additive] [S.Additive]
  [PreservesFiniteLimits H] [PreservesFiniteColimits H]
  [PreservesFiniteLimits R] [PreservesFiniteColimits R]
  [PreservesFiniteLimits S] [PreservesFiniteColimits S]
  (i : H ⋙ R ≅ S)

end ExactHelpers

attribute [local irreducible] Functor.mapDerivedCategory

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (X : AlgebraicGeometry.Scheme.{t})
  (D : FiniteFieldDatum.{d}) (hl : l ≠ D.p)
/-- Canonical abelian sheafification, registered only in this file. -/
abbrev normalizedDVRKFlatTransitionLocal1 :
    HasSheafify (AlgebraicGeometry.Scheme.ProEt.topology X)
    AddCommGrpCat.{max u (t + 1)} := integralCoefficientAbSheafify.{t, u} X
attribute [local instance] normalizedDVRKFlatTransitionLocal1
/-- The canonical locally bijective sheafification criterion, registered locally. -/
abbrev normalizedDVRKFlatTransitionLocal2 :
    (AlgebraicGeometry.Scheme.ProEt.topology X).WEqualsLocallyBijective
    AddCommGrpCat.{max u (t + 1)} := integralCoefficientAbLocallyBijective.{t, u} X
attribute [local instance] normalizedDVRKFlatTransitionLocal2

/-- The universal derived tensor counit followed by the exact restriction comparison.
Source: Stacks Tag 06YY; blueprint final proof step of DVR effectivity.
This is an actual morphism built from the fixed derived functors. -/
noncomputable def normalizedDVRKFlatComparison (n : ℕ)
    (P : CochainComplex (scalarReductionSource l E X) ℤ) :
    (scalarReductionDerivedRestriction l E X n).obj
        ((scalarReductionDerivedExtension l E X n).obj (DerivedCategory.Q.obj P)) ⟶
      DerivedCategory.Q.obj (unrestrictedTowerComplex l E X n P) :=
  (scalarReductionDerivedRestriction l E X n).map
      ((scalarReductionDerivedExtension l E X n).map
          ((DerivedCategory.quotientCompQhIso _).inv.app P) ≫
        (scalarReductionCounit l E X n).app
          ((HomotopyCategory.quotient _ (.up ℤ)).obj P) ≫
        DerivedCategory.Qh.map
          (((scalarReductionExtension l E X n).mapHomotopyCategoryFactors (.up ℤ)).hom.app
            P) ≫
        (DerivedCategory.quotientCompQhIso _).hom.app
          (unrestrictedTowerFiniteComplex l E X n P)) ≫
    (scalarReductionRestriction l E X n).mapDerivedCategoryFactors.hom.app
      (unrestrictedTowerFiniteComplex l E X n P)

attribute [local irreducible] normalizedDVRKFlatComparison

attribute [local instance] scalarReductionExtensionAdditive
  scalarReductionRestrictionLimits scalarReductionRestrictionColimits

attribute [local irreducible] normalizedDVRQuotient integralCoefficientSheafTransition

attribute [local irreducible] scalarReductionExistence unrestrictedIntegralReductionExistence
  scalarReductionExtension unrestrictedIntegralReductionFunctor

section TensorIdentification
attribute [local semireducible] scalarReductionExistence unrestrictedIntegralReductionExistence
  scalarReductionExtension unrestrictedIntegralReductionFunctor

end TensorIdentification

end WeilConjectures
