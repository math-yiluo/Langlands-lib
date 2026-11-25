/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProperBaseChange.CompletionMap
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import all WeilConjectures.SmoothPurity.Derived.DerivedScalarExtensionRestrictionAdjunctionSupplement
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived
import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Homology.BifunctorShift
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.CategoryTheory.Sites.Equivalence
import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import Mathlib.CategoryTheory.Limits.EssentiallySmall
import WeilConjectures.Algebra.Homology.ProperBaseChange.KFlatResolutionGeneral

/-! # The canonical derived reduction Hom equivalence

Source: blueprint proper base change, order 1260, proof step 6.
(blueprint: lem-weil-pbc-adic-reduction-adjunction-hom-equiv).
-/

@[expose] public section
set_option autoImplicit false

universe t
open CategoryTheory CategoryTheory.Limits
open scoped ChangeOfRings TensorProduct
namespace AlgebraicGeometry.Scheme

-- The imported adjunction specializes its site-size instance to another coefficient universe.
-- Keep that instance out of this proof; the site here already has size t + 1.
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Restriction of scalars is exact, also when the small site's object and morphism
universes differ. Source: order 1260, proof step 6; Stacks Tag 03D3.
Proof: restriction leaves the underlying abelian sheaf unchanged. Kernels and cokernels
are computed on those sheaves, with the restricted action, so it preserves both.
(blueprint: lemma-weil-pbc-adic-completion-reduction) -/
theorem adicRestrictScalars_exact (X : Scheme.{t}) {A B : Type t}
    [CommRing A] [CommRing B] (φ : A →+* B) :
    PreservesFiniteLimits (SheafOfModules.restrictScalars.{t + 1} (adicModuleMap X φ)) ∧
      PreservesFiniteColimits (SheafOfModules.restrictScalars.{t + 1} (adicModuleMap X φ)) := by
  let F := SheafOfModules.restrictScalars.{t + 1} (adicModuleMap X φ)
  let UA := SheafOfModules.toSheaf.{t + 1, t, t + 1, t + 1} (adicModuleRing X A)
  let UB := SheafOfModules.toSheaf.{t + 1, t, t + 1, t + 1} (adicModuleRing X B)
  have hs : HasSheafify (ProEt.topology X) AddCommGrpCat.{t + 1} :=
    SheafOfModules.hasSheafify_coefficientUniverse.{t + 1, t, t + 1}
      (C := X.ProEt) (J := ProEt.topology X)
  have hw : GrothendieckTopology.WEqualsLocallyBijective.{t + 1, t + 1, t,
      t + 2, t + 1, t + 1} (ProEt.topology X) AddCommGrpCat.{t + 1} :=
    SheafOfModules.wEqualsLocallyBijective_coefficientUniverse.{t + 1, t, t + 1}
      (C := X.ProEt) (J := ProEt.topology X)
  have : PreservesFiniteColimits UA :=
    @SheafOfModules.preservesFiniteColimits_toSheaf.{t + 1, t, t + 1, t + 1}
      X.ProEt inferInstance (ProEt.topology X) _ hs hw
  have : PreservesFiniteColimits UB :=
    @SheafOfModules.preservesFiniteColimits_toSheaf.{t + 1, t, t + 1, t + 1}
      X.ProEt inferInstance (ProEt.topology X) _ hs hw
  have : PreservesFiniteLimits (F ⋙ UA) :=
    inferInstanceAs (PreservesFiniteLimits UB)
  have : PreservesFiniteColimits (F ⋙ UA) :=
    inferInstanceAs (PreservesFiniteColimits UB)
  have : ReflectsFiniteColimits UA :=
    { reflects := fun _ ↦ reflectsColimitsOfShape_of_reflectsIsomorphisms }
  exact ⟨preservesFiniteLimits_of_reflects_of_preserves F UA,
    preservesFiniteColimits_of_reflects_of_preserves F UA⟩

/-- Exact derived restriction along the constant coefficient map.
Source: order 1260, proof step 6 (blueprint: lemma-weil-pbc-adic-completion-reduction). -/
noncomputable def adicDerivedRestrict (X : Scheme.{t}) {A B : Type t}
    [CommRing A] [CommRing B] (φ : A →+* B) :
    proEtaleDerivedCategory X B ⥤ proEtaleDerivedCategory X A :=
  letI := HasDerivedCategory.standard (SheafOfModules.{t + 1} (adicModuleRing X A))
  letI := HasDerivedCategory.standard (SheafOfModules.{t + 1} (adicModuleRing X B))
  letI := (adicRestrictScalars_exact X φ).1
  letI := (adicRestrictScalars_exact X φ).2
  (SheafOfModules.restrictScalars.{t + 1} (adicModuleMap X φ)).mapDerivedCategory

end AlgebraicGeometry.Scheme
