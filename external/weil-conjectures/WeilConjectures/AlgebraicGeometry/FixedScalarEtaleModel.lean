/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.AdicStratifiedPerfectData
public import WeilConjectures.AlgebraicGeometry.FixedScalarComplexModel
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor

/-! # Explicit exact equivalences for fixed scalar site models

Source: Stacks Tags 03CY and 09A5 (auxiliary; not a blueprint node).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme

/-- Precomposition by the site equivalence followed by the inverse constant scalar
restriction equivalence. All data is constructed from the specified equivalences.
Source: Stacks Tags 03CY and 09A5 (auxiliary; not a blueprint node). -/
def fixedScalarEtaleSheafEquivalence (X : Scheme.{u}) (k : Type (u + 1)) [CommRing k] :
    Sheaf (X.smallEtaleTopology) (ModuleCat.{u + 1} k) ≌
      ConstantCompletion.Mod
        (ConstantCompletion.constant (smallModelComparisonEtaleTopology.{u, u} X) k) := by
  let e := AsSmall.equiv.{u, u + 1, u + 1} (C := X.Etale)
  let : (AsSmall.down : smallModelComparisonEtaleSite.{u, u} X ⥤ X.Etale).IsEquivalence :=
    e.isEquivalence_inverse
  let : e.inverse.IsDenseSubsite (smallModelComparisonEtaleTopology.{u, u} X)
      (X.smallEtaleTopology) := inferInstanceAs
    ((AsSmall.down : smallModelComparisonEtaleSite.{u, u} X ⥤ X.Etale).IsDenseSubsite
      ((AsSmall.down : smallModelComparisonEtaleSite.{u, u} X ⥤ X.Etale).inducedTopology
        (X.smallEtaleTopology)) (X.smallEtaleTopology))
  exact (e.sheafCongr (X.smallEtaleTopology) (smallModelComparisonEtaleTopology.{u, u} X)
    (ModuleCat.{u + 1} k)).trans
      (ConstantScalarRestriction.restriction
        (smallModelComparisonEtaleTopology.{u, u} X) k).asEquivalence.symm

instance fixedScalarEtaleSheafEquivalence_additive (X : Scheme.{u})
    (k : Type (u + 1)) [CommRing k] :
    (fixedScalarEtaleSheafEquivalence X k).functor.Additive :=
  Functor.additive_of_preserves_binary_products _

/-- Precomposition by the site equivalence followed by the inverse constant scalar
restriction equivalence. All data is constructed from the specified equivalences.
Source: Stacks Tags 03CY and 09A5 (auxiliary; not a blueprint node). -/
def fixedScalarProEtaleSheafEquivalence (X : Scheme.{u}) (k : Type (u + 1)) [CommRing k] :
    Sheaf (ProEt.topology X) (ModuleCat.{u + 1} k) ≌
      ConstantCompletion.Mod
        (ConstantCompletion.constant (coefficientProEtaleModelTopology.{u, u} X) k) := by
  let e := AsSmall.equiv.{u, u + 1, u + 1} (C := X.ProEt)
  let : (AsSmall.down : coefficientProEtaleSiteModel.{u, u} X ⥤ X.ProEt).IsEquivalence :=
    e.isEquivalence_inverse
  let : e.inverse.IsDenseSubsite (coefficientProEtaleModelTopology.{u, u} X)
      (ProEt.topology X) := inferInstanceAs
    ((AsSmall.down : coefficientProEtaleSiteModel.{u, u} X ⥤ X.ProEt).IsDenseSubsite
      ((AsSmall.down : coefficientProEtaleSiteModel.{u, u} X ⥤ X.ProEt).inducedTopology
        (ProEt.topology X)) (ProEt.topology X))
  exact (e.sheafCongr (ProEt.topology X) (coefficientProEtaleModelTopology.{u, u} X)
    (ModuleCat.{u + 1} k)).trans
      (ConstantScalarRestriction.restriction
        (coefficientProEtaleModelTopology.{u, u} X) k).asEquivalence.symm

instance fixedScalarProEtaleSheafEquivalence_additive (X : Scheme.{u})
    (k : Type (u + 1)) [CommRing k] :
    (fixedScalarProEtaleSheafEquivalence X k).functor.Additive :=
  Functor.additive_of_preserves_binary_products _

/-- The termwise etale presentation, with no chosen representative.
Source: Stacks Tag 03CY (auxiliary; not a blueprint node). -/
def fixedScalarEtaleComplexToModel (X : Scheme.{u}) (k : Type (u + 1)) [CommRing k] :=
  (fixedScalarEtaleSheafEquivalence X k).functor.mapHomologicalComplex (.up ℤ)

/-- The pro-etale equivalence is precisely the already prescribed termwise functor.
Source: Stacks Tags 03CY and 09A5 (auxiliary; not a blueprint node). -/
theorem fixedScalarComplexToModel_eq (X : Scheme.{u}) (k : Type (u + 1)) [CommRing k] :
    fixedScalarComplexToModel X k =
      (fixedScalarProEtaleSheafEquivalence X k).functor.mapHomologicalComplex (.up ℤ) := by
  unfold fixedScalarComplexToModel fixedScalarProEtaleSheafEquivalence
  rfl

instance fixedScalarEtaleSheafEquivalence_inverse_additive (X : Scheme.{u})
    (k : Type (u + 1)) [CommRing k] :
    (fixedScalarEtaleSheafEquivalence X k).inverse.Additive :=
  Functor.additive_of_preserves_binary_products _

instance fixedScalarEtaleComplexToModel_isEquivalence (X : Scheme.{u})
    (k : Type (u + 1)) [CommRing k] :
    (fixedScalarEtaleComplexToModel X k).IsEquivalence :=
  ((fixedScalarEtaleSheafEquivalence X k).mapHomologicalComplex (.up ℤ)).isEquivalence_functor

/-- The prescribed pro-etale functor descends to the standard derived localizations.
Source: Stacks Tags 03CY and 05RT (auxiliary; not a blueprint node). -/
def fixedScalarProEtaleDerivedFunctor (X : Scheme.{u}) (k : Type (u + 1)) [CommRing k] :
    DerivedCategory (Sheaf (ProEt.topology X) (ModuleCat.{u + 1} k)) ⥤
      ConstantCompletion.D
        (ConstantCompletion.constant (coefficientProEtaleModelTopology.{u, u} X) k) :=
  letI := HasDerivedCategory.standard (ConstantCompletion.Mod
    (ConstantCompletion.constant (coefficientProEtaleModelTopology.{u, u} X) k))
  (fixedScalarProEtaleSheafEquivalence X k).functor.mapDerivedCategory

instance fixedScalarProEtaleDerivedFunctor_isEquivalence (X : Scheme.{u})
    (k : Type (u + 1)) [CommRing k] :
    (fixedScalarProEtaleDerivedFunctor X k).IsEquivalence := by
  unfold fixedScalarProEtaleDerivedFunctor
  infer_instance

/-- Localization of the explicit termwise equivalence agrees with the derived functor.
Source: Stacks Tags 03CY and 05RT (auxiliary; not a blueprint node). -/
def fixedScalarProEtaleDerivedFactors (X : Scheme.{u}) (k : Type (u + 1)) [CommRing k]
    (T : CochainComplex (Sheaf (ProEt.topology X) (ModuleCat.{u + 1} k)) ℤ) :
    (fixedScalarProEtaleDerivedFunctor X k).obj (DerivedCategory.Q.obj T) ≅
      fixedScalarDerivedModel X k T := by
  unfold fixedScalarDerivedModel
  rw [fixedScalarComplexToModel_eq]
  letI := HasDerivedCategory.standard (ConstantCompletion.Mod
    (ConstantCompletion.constant (coefficientProEtaleModelTopology.{u, u} X) k))
  exact ((fixedScalarProEtaleSheafEquivalence X k).functor.mapDerivedCategoryFactors).app T

end AlgebraicGeometry.Scheme
