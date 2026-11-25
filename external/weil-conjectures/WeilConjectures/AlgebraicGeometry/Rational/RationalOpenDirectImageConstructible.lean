/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Condensed.CondensedConstantConstructibilitySupplement
public import WeilConjectures.AlgebraicGeometry.ContinuousCoefficientCommRing
public import WeilConjectures.AlgebraicGeometry.ContinuousCoefficientUniverse
public import Mathlib.Topology.Category.Profinite.EffectiveEpi
public import WeilConjectures.CategoryTheory.RingObjects.ContinuousMap
public import Mathlib.Condensed.TopComparison
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.FiniteSubextension
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructibleIhom
public import WeilConjectures.AlgebraicGeometry.Bounded.BoundedConstructibleDevissageSupplement
public import WeilConjectures.AlgebraicGeometry.FiniteTypeDirectImageSingleBound
public import WeilConjectures.AlgebraicGeometry.FiniteTypeDirectImageSingleConstructible
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusCompatibility
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperLowerStar
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType

import WeilConjectures.AlgebraicGeometry.Finite.Coefficient.FiniteCoefficientDescentTwoColimit
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructibleLowerStar

/-!
# Rational open direct images with finite constant local models

The two conjuncts are the finite-subextension and algebraic-closure coefficient cases.
Both use the finite-constant-model predicate, rather than general local finite presentation.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

/-- Rational derived direct image along a quasi-compact open immersion preserves bounded
constructibility with finite constant scalar models, for both rational coefficient rings.
-/
theorem constantModelBoundedConstructible_rational_open_direct_image
    (ℓ : ℕ) [Fact ℓ.Prime] (k : Type u) [Field k]
    [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
    (E : PadicAlgCl.FiniteIntermediateField ℓ)
    {U X : Scheme.{u}} [U.Over (Spec (.of k))] [X.Over (Spec (.of k))]
    [LocallyOfFiniteType (U ↘ Spec (.of k))] [QuasiCompact (U ↘ Spec (.of k))]
    [IsSeparated (U ↘ Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))]
    (j : U ⟶ X) [j.IsOver (Spec (.of k))] [IsOpenImmersion j] [QuasiCompact j] :
    (∀ K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology U) Ab.{u + 1})
        (condensedRingObj (Profinite.continuousMapRingObj E) U)),
      constantModelBoundedConstructible (Profinite.continuousMapRingObj E) U K →
      constantModelBoundedConstructible (Profinite.continuousMapRingObj E) X
        (((CondensedRing.lowerStar (Profinite.continuousMapRingObj E) j).rightDerivedFunctor).obj
          K)) ∧
    (∀ K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology U) Ab.{u + 1})
        (condensedRingObj (Profinite.padicAlgClRingObj ℓ) U)),
      constantModelBoundedConstructible (Profinite.padicAlgClRingObj ℓ) U K →
      constantModelBoundedConstructible (Profinite.padicAlgClRingObj ℓ) X
        (((CondensedRing.lowerStar (Profinite.padicAlgClRingObj ℓ) j).rightDerivedFunctor).obj
          K)) := by
  let f := j.asOver (Spec (.of k))
  let : LocallyOfFiniteType (U.asOver (Spec (.of k))).hom :=
    inferInstanceAs (LocallyOfFiniteType (U ↘ Spec (.of k)))
  let : QuasiCompact (U.asOver (Spec (.of k))).hom :=
    inferInstanceAs (QuasiCompact (U ↘ Spec (.of k)))
  let : IsSeparated (U.asOver (Spec (.of k))).hom :=
    inferInstanceAs (IsSeparated (U ↘ Spec (.of k)))
  let : LocallyOfFiniteType (X.asOver (Spec (.of k))).hom :=
    inferInstanceAs (LocallyOfFiniteType (X ↘ Spec (.of k)))
  let : QuasiCompact (X.asOver (Spec (.of k))).hom :=
    inferInstanceAs (QuasiCompact (X ↘ Spec (.of k)))
  let : IsSeparated (X.asOver (Spec (.of k))).hom :=
    inferInstanceAs (IsSeparated (X ↘ Spec (.of k)))
  constructor
  · intro K hK
    rw [constantModelBoundedConstructible_eq_boundedConstructible_subfield_of_finiteType k ℓ E U]
      at hK
    rw [constantModelBoundedConstructible_eq_boundedConstructible_subfield_of_finiteType k ℓ E X]
    exact CondensedRing.ContinuousMapRingObj.boundedConstructible_rightDerivedLowerStar_obj
      ℓ (k := k) E f ⟨K, hK⟩
  · intro K hK
    rw [constantModelBoundedConstructible_eq_boundedConstructible_padicAlgCl_of_finiteType k ℓ U]
      at hK
    rw [constantModelBoundedConstructible_eq_boundedConstructible_padicAlgCl_of_finiteType k ℓ X]
    exact CondensedRing.boundedConstructible_rightDerivedLowerStar_obj ℓ (k := k) f ⟨K, hK⟩

end AlgebraicGeometry.ProEtale
