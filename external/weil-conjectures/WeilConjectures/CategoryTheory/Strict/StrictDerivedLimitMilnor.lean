/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import WeilConjectures.CategoryTheory.Triangulated.DerivedLimit
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
public import Mathlib.CategoryTheory.Functor.Derived.RightDerived
public import Mathlib.Algebra.Homology.Functor
public import Mathlib.CategoryTheory.Limits.Shapes.Countable
import all WeilConjectures.CategoryTheory.RingedStrictTowerHomotopyLimit
import all WeilConjectures.CategoryTheory.RingedSiteModules
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import all WeilConjectures.CategoryTheory.RingedSiteGrothendieckAbelian
import all WeilConjectures.CategoryTheory.Triangulated.DerivedLimit
import all Mathlib.Algebra.Homology.DerivedCategory.Basic
import all Mathlib.CategoryTheory.Triangulated.Functor
import all Mathlib.Algebra.Homology.Functor
import all Mathlib.Algebra.Homology.HomotopyCategory.KInjective
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
import all Mathlib.CategoryTheory.Functor.Derived.RightDerived
import all Mathlib.CategoryTheory.Whiskering
import all Mathlib.CategoryTheory.Functor.OfSequence
import all Mathlib.CategoryTheory.Limits.Shapes.Countable
import all Mathlib.Algebra.Homology.DerivedCategory.ShortExact
import all WeilConjectures.Algebra.Homology.KInjectiveProductsTermwise
import all Mathlib.Algebra.Homology.HomologicalComplexLimits
import all Mathlib.Algebra.Homology.DerivedCategory.KInjective
import all WeilConjectures.Algebra.Homology.HomotopyCategory.Products
import all WeilConjectures.Mathlib.CategoryTheory.Limits.Shapes.Products
import all WeilConjectures.Algebra.Homology.TowerEvaluationKInjective
import all WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolutionInjective
import all WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import all Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.FunctorCategory
import all Mathlib.CategoryTheory.Adjunction.Evaluation
import all WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
import all Mathlib.CategoryTheory.Localization.DerivabilityStructure.Derives
import all Mathlib.Algebra.BigOperators.Ring.Finset

/-! # The Milnor triangle for any total derived inverse limit

Source: Stacks Project, sites-cohomology.tex, Tags 0940 and 0941.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe a v w g
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated Opposite

namespace CategoryTheory

/-- Any total right derived inverse limit has a Milnor triangle whose terms are the
localized evaluations of the strict tower. The coefficient category is any Grothendieck
abelian category, and the complexes are unbounded. Exact products are not required.

Source: Stacks Project, sites-cohomology.tex, Tags 0940 and 0941,
the strict-tower construction and lemma-derived-limit-is-ok
(blueprint: lem-sfb-strict-derived-limit-milnor).

Proof: the tower category is Grothendieck. Resolve its complexes by functorial K-injective
complexes with injective terms. An injective tower has split epimorphic transitions;
recursively solve y_n - q_n y_(n+1) = x_n to show that one minus shift on its product is
split epimorphic. Its kernel is the inverse limit. The short exact sequence of complexes
gives the Milnor triangle. Evaluation preserves K-injectives because its finite-coproduct
left adjoint is exact. Products of K-injectives represent products in the derived category,
so the middle terms of this triangle are the derived products of the evaluations. The
existing natural Roos construction descends these triangles along localization. Finally,
uniqueness of total right derived functors identifies its inverse limit with the specified
one; conjugate the first and last arrows by this isomorphism. All steps also apply to zero
towers, identity transitions, and zero transitions. -/
theorem strictDerivedLimit_milnor
    {A : Type a} [Category.{v} A] [Abelian A] [IsGrothendieckAbelian.{g} A]
    [HasDerivedCategory.{w} A] [HasDerivedCategory.{w} (ℕᵒᵖ ⥤ A)]
    [HasLimitsOfShape ℕᵒᵖ A] [HasCountableProducts A]
    [HasCountableProducts (DerivedCategory.{w} A)]
    (R : DerivedCategory.{w} (ℕᵒᵖ ⥤ A) ⥤ DerivedCategory.{w} A)
    (η : (lim : (ℕᵒᵖ ⥤ A) ⥤ A).mapHomologicalComplex (.up ℤ) ⋙
      DerivedCategory.Q ⟶ DerivedCategory.Q ⋙ R)
    (hR : R.IsRightDerivedFunctor η
      (HomologicalComplex.quasiIso (ℕᵒᵖ ⥤ A) (.up ℤ))) :
    ∃ (E : DerivedCategory.{w} (ℕᵒᵖ ⥤ A) ⥤ (ℕᵒᵖ ⥤ DerivedCategory.{w} A))
      (_ε : DerivedCategory.Q ⋙ E ≅
        HomologicalComplex.complexOfFunctorsToFunctorToComplex ⋙
          (Functor.whiskeringRight ℕᵒᵖ (CochainComplex A ℤ)
            (DerivedCategory.{w} A)).obj DerivedCategory.Q)
      (p : ∀ Z, R.obj Z ⟶ ∏ᶜ (fun n : ℕ ↦ (E.obj Z).obj (op n)))
      (δ : ∀ Z, (∏ᶜ (fun n : ℕ ↦ (E.obj Z).obj (op n))) ⟶ (R.obj Z)⟦(1 : ℤ)⟧),
      ∀ Z, IsDerivedLimitTriangle
        (fun n : ℕ ↦ (E.obj Z).map (homOfLE (Nat.le_succ n)).op)
        (R.obj Z) (p Z) (δ Z) := by
  let : IsGrothendieckAbelian.{g} (ℕᵒᵖ ⥤ A) :=
    RingedStrictTowerProof.tower_grothendieck A
  have : (lim : (ℕᵒᵖ ⥤ A) ⥤ A).Additive :=
    Functor.additive_of_preserves_binary_products _
  obtain ⟨RF, ηF, hRF, hηF, -, -⟩ :=
    RingedStrictTowerProof.totalDerivedData (lim : (ℕᵒᵖ ⥤ A) ⥤ A)
  have := hRF
  have := hR
  let c := Functor.rightDerivedUnique RF R ηF η
    (HomologicalComplex.quasiIso (ℕᵒᵖ ⥤ A) (.up ℤ))
  obtain ⟨E, ⟨ε⟩⟩ := RingedStrictTowerProof.evaluationData (A := A)
  obtain ⟨p, δ, hT, -, -⟩ :=
    RingedStrictTowerProof.CoreWork.natural_roos RF ηF hηF E ε
  refine ⟨E, ε, (fun Z ↦ (c.app Z).inv ≫ p Z),
    (fun Z ↦ δ Z ≫ (c.app Z).hom⟦(1 : ℤ)⟧'), ?_⟩
  intro Z
  exact isomorphic_distinguished _ (hT Z) _
    (Triangle.isoMk _ _ (c.app Z).symm (Iso.refl _) (Iso.refl _)
      (by simp) (by simp) (by
        change (δ Z ≫ (shiftFunctor _ (1 : ℤ)).map (c.hom.app Z)) ≫
          (shiftFunctor _ (1 : ℤ)).map (c.inv.app Z) = 𝟙 _ ≫ δ Z
        simp only [Category.id_comp, Category.assoc, ← Functor.map_comp,
          Iso.hom_inv_id_app, Functor.map_id, Category.comp_id]))

end CategoryTheory
