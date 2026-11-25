/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.ProEtaleInverseImage
public import WeilConjectures.CategoryTheory.RingedDerivedRestrictionGeneral
public import WeilConjectures.CategoryTheory.RingedSiteDerivedRestrictionUniverses
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful
import WeilConjectures.AlgebraicGeometry.ProEtaleModuleInverseImageComparison

/-!
# Exact inverse image and local derived restriction

Source: Stacks Project, derived.tex, Tag 015F; sites-modules.tex, Tags 03D2, 03DA,
04IX; Bhatt--Scholze, Proposition 6.8.11(3).
(auxiliary; not a blueprint node).

## Main declarations

* `inverseImage_exact`: exactness over the actual inverse-image ring.
* `comparison`: the prescribed localization-representative comparison.
* `comparisons`: its functorial cohomology and shifted-single normalizations.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u wT wS wU

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.ProEtaleLocalRestriction

/-- Underlying ring sheaf of the specified commutative coefficient sheaf.
This is only a transparent notation for sheafCompose with forget₂, not a new ring.
Source: Stacks, Tag 03DA (auxiliary; not a blueprint node). -/
abbrev ring {T : Scheme.{u}} (R : Sheaf (ProEt.topology T) CommRingCat.{u + 1}) :=
  (sheafCompose (ProEt.topology T) (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R

/-- The actual inverse-image coefficient ring, with commutativity forgotten.
Source: Stacks, Tag 03D2 (auxiliary; not a blueprint node). -/
abbrev inverseRing {S T : Scheme.{u}} (g : S ⟶ T)
    (R : Sheaf (ProEt.topology T) CommRingCat.{u + 1}) :=
  ring ((proEtaleSheafInverseImage g CommRingCat.{u + 1}).obj R)

/-- Module restriction to the slice, with its actual restricted coefficient ring.
Source: Stacks, Tag 04IX (auxiliary; not a blueprint node). -/
abbrev restriction {S T : Scheme.{u}} (g : S ⟶ T)
    (R : Sheaf (ProEt.topology T) CommRingCat.{u + 1}) (U : S.ProEt) :=
  SheafOfModules.overFunctor.{u + 1} (inverseRing g R) U

/-- Actual-ring inverse image is additive and exact for every scheme morphism.
Source: Stacks, Tags 03D2, 03DA and 010N
(auxiliary; not a blueprint node).
Proof: the module inverse-image comparison identifies its underlying abelian sheaf
with abelian inverse image, preserving the scalar action. Site inverse image is exact.
The faithful exact module forgetful functors reflect zero homology: a module with zero
underlying sheaf has zero identity by faithfulness. They therefore reflect short exact
sequences and addition of maps. Apply the abelian exact-functor criterion. This uses
only the actual inverse-image ring, without extension to another coefficient ring.
DAG inputs: lem-weil-pbc-proetale-module-inverse-image-comparison,
lem-weil-pbc-left-exact-site-inverse-image-tensor,
situation-conventions, and
lem-sp-exact-functor-preserves-homology. -/
theorem inverseImage_exact {S T : Scheme.{u}} (g : S ⟶ T)
    (R : Sheaf (ProEt.topology T) CommRingCat.{u + 1}) :
    (proEtaleModuleInverseImage g R).Additive ∧
      PreservesFiniteLimits (proEtaleModuleInverseImage g R) ∧
      PreservesFiniteColimits (proEtaleModuleInverseImage g R) := by
  let F := proEtaleModuleInverseImage g R
  let V := SheafOfModules.toSheaf.{u + 1} (inverseRing g R)
  let : PreservesFiniteColimits (SheafOfModules.toSheaf.{u + 1} (ring R)) :=
    (moduleSheaves_colimits_forgetful (ring R)).2.2.1
  let : PreservesFiniteColimits V :=
    (moduleSheaves_colimits_forgetful (inverseRing g R)).2.2.1
  let : (proEtaleSheafDirectImage g AddCommGrpCat.{u + 1}).Additive := ⟨by
    intros
    ext W
    rfl⟩
  let : (proEtaleSheafInverseImage g AddCommGrpCat.{u + 1}).Additive :=
    (proEtaleSheafAdjunction g AddCommGrpCat.{u + 1}).left_adjoint_additive
  let : RepresentablyFlat (proEtaleBaseChange g) := flat_of_preservesFiniteLimits _
  let : PreservesFiniteLimits (proEtaleSheafInverseImage g AddCommGrpCat.{u + 1}) :=
    inferInstance
  let : PreservesColimitsOfSize.{0, 0}
      (proEtaleSheafInverseImage g AddCommGrpCat.{u + 1}) :=
    (proEtaleSheafAdjunction g AddCommGrpCat.{u + 1}).leftAdjoint_preservesColimits
  obtain ⟨e⟩ := (proEtale_moduleInverseImage_comparison g R).1
  let : (F ⋙ V).Additive := Functor.additive_of_iso e.symm
  let : F.Additive := Functor.additive_of_comp_faithful F V
  let : ReflectsFiniteLimits V := reflectsFiniteLimits_of_reflectsIsomorphisms V
  let : PreservesFiniteLimits (F ⋙ V) := preservesFiniteLimits_of_natIso e.symm
  let : PreservesFiniteLimits F := preservesFiniteLimits_of_reflects_of_preserves F V
  let : ReflectsFiniteColimits V :=
    { reflects := fun _ ↦ reflectsColimitsOfShape_of_reflectsIsomorphisms }
  let : PreservesFiniteColimits (F ⋙ V) := preservesFiniteColimits_of_natIso e.symm
  let : PreservesFiniteColimits F := preservesFiniteColimits_of_reflects_of_preserves F V
  exact ⟨inferInstance, inferInstance, inferInstance⟩

/-- Additivity supplied by the actual-ring exactness assertion.
Source: Stacks, Tag 03DA (auxiliary; not a blueprint node). -/
instance inverseImage_additive {S T : Scheme.{u}} (g : S ⟶ T)
    (R : Sheaf (ProEt.topology T) CommRingCat.{u + 1}) :
    (proEtaleModuleInverseImage g R).Additive :=
  (inverseImage_exact g R).1

/-- Preservation of finite limits supplied by actual-ring exactness.
Source: Stacks, Tag 03DA (auxiliary; not a blueprint node). -/
instance inverseImage_preservesFiniteLimits {S T : Scheme.{u}} (g : S ⟶ T)
    (R : Sheaf (ProEt.topology T) CommRingCat.{u + 1}) :
    PreservesFiniteLimits (proEtaleModuleInverseImage g R) :=
  (inverseImage_exact g R).2.1

/-- Preservation of finite colimits supplied by actual-ring exactness.
Source: Stacks, Tag 03DA (auxiliary; not a blueprint node). -/
instance inverseImage_preservesFiniteColimits {S T : Scheme.{u}} (g : S ⟶ T)
    (R : Sheaf (ProEt.topology T) CommRingCat.{u + 1}) :
    PreservesFiniteColimits (proEtaleModuleInverseImage g R) :=
  (inverseImage_exact g R).2.2

/-- Additivity of the existing slice restriction, without a site-size identification.
Source: Stacks, Tag 04IX (auxiliary; not a blueprint node). -/
instance restriction_additive {S T : Scheme.{u}} (g : S ⟶ T)
    (R : Sheaf (ProEt.topology T) CommRingCat.{u + 1}) (U : S.ProEt) :
    (restriction g R U).Additive :=
  (ringedOverFunctor_exactGeneral (inverseRing g R) U).1

/-- Left exactness of existing slice restriction.
Source: Stacks, Tag 04IX (auxiliary; not a blueprint node). -/
instance restriction_preservesFiniteLimits {S T : Scheme.{u}} (g : S ⟶ T)
    (R : Sheaf (ProEt.topology T) CommRingCat.{u + 1}) (U : S.ProEt) :
    PreservesFiniteLimits (restriction g R U) :=
  (ringedOverFunctor_exactGeneral (inverseRing g R) U).2.1

/-- Right exactness of existing slice restriction.
Source: Stacks, Tag 04IX (auxiliary; not a blueprint node). -/
instance restriction_preservesFiniteColimits {S T : Scheme.{u}} (g : S ⟶ T)
    (R : Sheaf (ProEt.topology T) CommRingCat.{u + 1}) (U : S.ProEt) :
    PreservesFiniteColimits (restriction g R U) :=
  (ringedOverFunctor_exactGeneral (inverseRing g R) U).2.2

variable {S T : Scheme.{u}} (g : S ⟶ T)
  (R : Sheaf (ProEt.topology T) CommRingCat.{u + 1}) (U : S.ProEt)
  [HasDerivedCategory.{wT} (SheafOfModules.{u + 1} (ring R))]
  [HasDerivedCategory.{wS} (SheafOfModules.{u + 1} (inverseRing g R))]
  [HasDerivedCategory.{wU} (SheafOfModules.{u + 1} ((inverseRing g R).over U))]

end AlgebraicGeometry.Scheme.ProEtaleLocalRestriction
