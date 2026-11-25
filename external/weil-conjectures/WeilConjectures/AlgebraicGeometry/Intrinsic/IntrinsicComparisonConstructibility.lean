/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.Intrinsic.IntrinsicFiniteTorsionConstructibility
public import WeilConjectures.AlgebraicGeometry.ProEtale.Finite.ProEtaleFiniteModuleIntrinsicComparison
public import WeilConjectures.SixFunctors.Etale.Derived.Coefficients
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
public import Mathlib.RingTheory.Ideal.Quotient.Index
import WeilConjectures.AlgebraicGeometry.Intrinsic.IntrinsicRealizationOriginComparison
import WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantModuleConstructibility
import WeilConjectures.AlgebraicGeometry.ConstructibleEtaleModuleSheafComparison
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
/-! The bounded constructibility component of finite-coefficient comparison.

## Implementation details

Use exactness of intrinsic comparison to identify homology with the
comparison pullback of each étale homology sheaf; transport constructibility across
the constant-scalar restriction equivalence and the finite constructible comparison
lemma. Finiteness of the set of nonzero homology degrees follows from the bounded
constructibility hypothesis and its integer interval. -/
@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory AlgebraicGeometry
namespace AlgebraicGeometry
/-- Exact comparison preserves bounded constructibility. -/
theorem intrinsicComparison_boundedConstructible
    (D : WeilConjectures.FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (_hlp : l ≠ D.p)
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (n : ℕ) (hn : 1 ≤ n) (T : Scheme.{u})
    [∀ x : T, Invertible (l : T.residueField x)]
    (K' : Etale.DerivedCategoryModule
      (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E n)) T)
    (_hK' : @Etale.DerivedCategory.isBoundedConstructible.{u}
      (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E n)) inferInstance
      ((Equiv.ulift : ULift.{u + 1, u} (Padic.coefficientExtensionRing l E n) ≃
        Padic.coefficientExtensionRing l E n).finite_iff.mpr
          (Padic.finite_coefficientExtensionRing l E n hn)) T K')
    :
    Scheme.intrinsicFiniteTorsionConstructible l E n hn T
      ((@ProEtale.finiteCoefficientIntrinsicDerivedComparison.{u} T
        (Padic.coefficientExtensionRing l E n) inferInstance
        (Padic.finite_coefficientExtensionRing l E n hn)).obj K') := by
  let B := Padic.coefficientExtensionRing l E n
  have : Finite B := Padic.finite_coefficientExtensionRing l E n hn
  have : Finite (ULift.{u + 1, u} B) := Finite.of_equiv B Equiv.ulift.symm
  let F := ProEtale.finiteCoefficientIntrinsicComparison T B
  let H := DerivedCategory.homologyFunctor
    (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1, u} B)))
  let H' := DerivedCategory.homologyFunctor
    (Scheme.proEtaleRingModules T (Scheme.proEtaleConstantRing T B))
  have eH (i : ℤ) : F.obj ((H i).obj K') ≅
      (H' i).obj ((ProEtale.finiteCoefficientIntrinsicDerivedComparison T B).obj K') :=
    (F.mapDerivedCategoryHomologyFunctorIso i).app K'
  change Set.Finite {i : ℤ | ¬ CategoryTheory.Limits.IsZero
      ((H' i).obj ((ProEtale.finiteCoefficientIntrinsicDerivedComparison T B).obj K'))} ∧ _
  constructor
  · obtain ⟨c, d, hcd, hvan⟩ := _hK'.2
    apply (Set.finite_Icc c d).subset
    intro i hi
    change c ≤ i ∧ i ≤ d
    constructor
    · by_contra h
      exact hi ((F.map_isZero (hvan i (Or.inl (lt_of_not_ge h)))).of_iso (eH i).symm)
    · by_contra h
      exact hi ((F.map_isZero (hvan i (Or.inr (lt_of_not_ge h)))).of_iso (eH i).symm)
  · intro i
    apply (Scheme.proEtaleModuleRestriction_constructible_iff T B _).mpr
    have hci := (Scheme.isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf
      ((H i).obj K')).mp (_hK'.1 i)
    obtain ⟨eR⟩ := ProEtale.intrinsicRealization_restriction T B
    have hfixed := ProEtale.isConstructible_comparisonUpperStar_obj ((H i).obj K')
    exact ProEtale.isConstructible_of_iso
      ((eR.app ((ProEtale.comparisonUpperStar
        (ModuleCat.{u + 1} (ULift.{u + 1, u} B)) T).obj ((H i).obj K'))).symm ≪≫
        (Scheme.proEtaleModuleRestriction T B).mapIso (eH i)) hfixed
end AlgebraicGeometry
