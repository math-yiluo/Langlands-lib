/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.DerivedCategory
import WeilConjectures.Algebra.Homology.OpenExtensionRestrictionIso
import Mathlib.CategoryTheory.Adjunction.Triple
import Mathlib.CategoryTheory.Adjunction.Additive
import Mathlib.CategoryTheory.Localization.Adjunction
import WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor

@[expose] public section

set_option autoImplicit false
universe u w
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry

/-- Restricting the unit of any right adjunction of open restriction is invertible.
There are no compactness, quasi-coherence, closed support, or triangle hypotheses.
Source: Stacks Project, Cohomology, Tags 08BS and 08FE (open restriction of direct image).
(blueprint: lem-pc-derived-open-unit-restriction-iso).

Proof: Let G be the concrete extension-by-zero functor (extension-by-zero presheaf
followed by module sheafification), and F the over-site restriction. The theorem
open_restriction_adjunction_exact supplies their exactness and an adjunction G to F.
Localize the termwise complex adjunction at quasi-isomorphisms to obtain an adjunction
between G.mapDerivedCategory and F.mapDerivedCategory. The existing theorem
nonempty_openExtensionRestrictionIso gives G followed by F naturally isomorphic to
the identity. Derive this isomorphism and use the derived composition and identity
comparisons to identify G.mapDerivedCategory followed by F.mapDerivedCategory with
the identity. Consequently the derived G is fully faithful. In the adjoint triple
G.mapDerivedCategory to F.mapDerivedCategory to R, full faithfulness of the leftmost
functor implies full faithfulness of R (Adjunction.Triple.fullyFaithfulEquiv).
The supplied adjunction therefore has invertible counit, and its triangle identity
makes F.mapDerivedCategory applied to its unit the inverse of that counit.
This includes empty and entire opens and all unbounded complexes. No arbitrary
existential witness is installed in a definition; adjunctions and isomorphisms are
eliminated only inside this proof. -/
theorem derived_open_unit_restriction_isIso
    (X : Scheme.{u}) (U : X.Opens)
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [HasDerivedCategory.{w}
      (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))]
    (R : DerivedCategory
      (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U)) ⥤
      schemeDerivedCategory X)
    (adj : (SheafOfModules.overFunctor.{u} (moduleRings X.toRingedSpace) U).mapDerivedCategory ⊣ R)
    (K : schemeDerivedCategory X) :
    IsIso ((SheafOfModules.overFunctor.{u} (moduleRings X.toRingedSpace) U).mapDerivedCategory.map
      (adj.unit.app K)) := by
  classical
  let A := SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U)
  let B := SheafOfModules.{u} (moduleRings X.toRingedSpace)
  let F := SheafOfModules.overFunctor.{u} (moduleRings X.toRingedSpace) U
  let G := SheafOfModules.extensionByZeroPresheaf.{u} (moduleRings X.toRingedSpace) U ⋙
    PresheafOfModules.sheafification.{u} (𝟙 (moduleRings X.toRingedSpace).obj)
  obtain ⟨_, _, hlim, hcolim, ⟨adjG⟩⟩ := open_restriction_adjunction_exact X.toRingedSpace U
  let : PreservesFiniteLimits G := hlim
  let : PreservesFiniteColimits G := hcolim
  let : G.Additive := adjG.left_adjoint_additive
  let : CatCommSq (G.mapHomologicalComplex (ComplexShape.up ℤ))
      DerivedCategory.Q DerivedCategory.Q G.mapDerivedCategory :=
    ⟨G.mapDerivedCategoryFactors.symm⟩
  let : CatCommSq (F.mapHomologicalComplex (ComplexShape.up ℤ))
      DerivedCategory.Q DerivedCategory.Q F.mapDerivedCategory :=
    ⟨F.mapDerivedCategoryFactors.symm⟩
  let adjD : G.mapDerivedCategory ⊣ F.mapDerivedCategory :=
    (adjG.mapHomologicalComplex (ComplexShape.up ℤ)).localization
      DerivedCategory.Q (HomologicalComplex.quasiIso A (ComplexShape.up ℤ))
      DerivedCategory.Q (HomologicalComplex.quasiIso B (ComplexShape.up ℤ))
      G.mapDerivedCategory F.mapDerivedCategory
  obtain ⟨e⟩ := nonempty_openExtensionRestrictionIso X.toRingedSpace U
  let : PreservesFiniteLimits (G ⋙ F) := comp_preservesFiniteLimits G F
  let : PreservesFiniteColimits (G ⋙ F) := comp_preservesFiniteColimits G F
  let eD : G.mapDerivedCategory ⋙ F.mapDerivedCategory ≅ 𝟭 (DerivedCategory A) :=
    (Functor.mapDerivedCategoryCompIso G F) ≪≫
      Functor.mapDerivedCategoryNatIso e ≪≫ Functor.mapDerivedCategoryIdIso A
  let ff := adjD.fullyFaithfulLOfCompIsoId eD
  let ffR := (Adjunction.Triple.fullyFaithfulEquiv ⟨adjD, adj⟩) ff
  let : R.Full := ffR.full
  let : R.Faithful := ffR.faithful
  exact inferInstance

end AlgebraicGeometry
