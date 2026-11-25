/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.Strict.Etale.StrictEtaleIsomorphicStageProjectionInterfaces
import WeilConjectures.AlgebraicGeometry.Strict.Etale.StrictEtaleOrdinaryInverseTransport
import WeilConjectures.AlgebraicGeometry.Strict.Etale.StrictEtaleFiniteOrdinaryInverseTransport
import WeilConjectures.AlgebraicGeometry.Strict.Etale.StrictEtaleDerivedInverseTransportFaces
import WeilConjectures.CategoryTheory.ProperBaseChange.ExchangeMateCube
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import all WeilConjectures.CategoryTheory.ToposFiniteFreeCompact.ToposFiniteFreeCompactConstituents
import WeilConjectures.AlgebraicGeometry.Strict.Etale.StrictEtaleFiniteFreeScalarExact
import WeilConjectures.AlgebraicGeometry.Strict.Etale.StrictEtaleFiniteFreeProperMateColumns
/-! Finite-free proper projection face for strict étale systems. -/

-- After pruning, this module only keeps private declarations.
set_option linter.privateModule false
@[expose] public noncomputable section
set_option autoImplicit false
set_option genInjectivity false
set_option genSizeOfSpec false
set_option genSizeOf false
set_option genCtorIdx false
set_option synthInstance.maxSize 2048
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor SheafOfModules
namespace AlgebraicGeometry
attribute [local instance 5000] strictEtaleSystemDerived strictEtaleLevelDerived
/- Mate and localization arguments adapted from StrictEtaleProperProjectionFaces (E5). -/
private theorem mate_of_counit
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    {L : A ⥤ B} {R : B ⥤ A} {L' : C ⥤ D} {R' : D ⥤ C}
    (adj : L ⊣ R) (adj' : L' ⊣ R')
    (E : A ⥤ C) (F : B ⥤ D)
    (α : L ⋙ F ≅ E ⋙ L') (β : R ⋙ E ≅ F ⋙ R')
    (h : ∀ K, α.hom.app (R.obj K) ≫ L'.map (β.hom.app K) ≫
      adj'.counit.app (F.obj K) = F.map (adj.counit.app K)) :
    (mateEquiv adj adj' (.mk _ _ _ _ α.inv)) = β.hom := by
  ext K
  apply (adj'.homEquiv _ _).symm.injective
  rw [Adjunction.homEquiv_counit]
  rw [mateEquiv_counit]
  apply (cancel_epi (α.hom.app (R.obj K))).1
  simpa only [Adjunction.homEquiv_counit, Category.assoc,
    Iso.hom_inv_id_app_assoc] using (h K).symm

section DerivedSquare
universe a b c d av bv cv dv w
variable {A : Type a} [Category.{av} A] [Abelian A] [HasDerivedCategory.{w} A]
  {B : Type b} [Category.{bv} B] [Abelian B] [HasDerivedCategory.{w} B]
  {C : Type c} [Category.{cv} C] [Abelian C] [HasDerivedCategory.{w} C]
  {D : Type d} [Category.{dv} D] [Abelian D] [HasDerivedCategory.{w} D]
  (F : A ⥤ B) (eA : A ⥤ C) (eB : B ⥤ D) (L : C ⥤ D)
  [F.Additive] [eA.Additive] [eB.Additive] [L.Additive]
  (FD : DerivedCategory A ⥤ DerivedCategory B)
  (EA : DerivedCategory A ⥤ DerivedCategory C)
  (EB : DerivedCategory B ⥤ DerivedCategory D)
  (LD : DerivedCategory C ⥤ DerivedCategory D)
  (φF : DerivedCategory.Q ⋙ FD ≅ F.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
  (φA : DerivedCategory.Q ⋙ EA ≅ eA.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
  (φB : DerivedCategory.Q ⋙ EB ≅ eB.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
  (φL : DerivedCategory.Q ⋙ LD ≅ L.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
  (α : F ⋙ eB ≅ eA ⋙ L)

end DerivedSquare

end AlgebraicGeometry
