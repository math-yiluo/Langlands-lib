/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import WeilConjectures.AlgebraicGeometry.QuasiFiniteMorphism
public import WeilConjectures.AlgebraicGeometry.IsConstructibleEtaleModuleSheaf
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriek
import WeilConjectures.SixFunctors.Finite.Exact
import WeilConjectures.AlgebraicGeometry.Finite.FiniteFinitePresentationPushforwardConstructible
import WeilConjectures.AlgebraicGeometry.QuasiFinite.QuasiFiniteFpFiniteFactorization
import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekCoherence
import WeilConjectures.ConstructibleSheaf.OpenClosed
import WeilConjectures.AlgebraicGeometry.ConstructibleEtaleModuleSheafComparison
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusExact

/-!
# Constructible cohomology under quasi-finite lower shriek

## References

* Stacks Project, More on Etale Cohomology, Tags 0GK3 and 0GKM, finite-ring bounded-below
  specialization
* Stacks Project, Tags 035C, 01TD, 0GK3 and 0GKM
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Etale

/-- Quasi-finite finitely presented lower shriek preserves constructible cohomology. -/
theorem constructibleCohomology_lowerShriek_of_quasiFinite
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    {T B : Scheme.{u}} [CompactSpace T] [QuasiSeparatedSpace T]
    [CompactSpace B] [QuasiSeparatedSpace B] (h : T ⟶ B)
    [IsSeparated h] [LocallyOfFiniteType h] [QuasiCompact h]
    [QuasiSeparated h] [LocallyOfFinitePresentation h] (hqf : h.IsQuasiFinite)
    (K : _root_.DerivedCategory.Plus (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (hK : ∀ q : ℤ, Scheme.IsConstructibleEtaleModuleSheaf
      ((_root_.DerivedCategory.Plus.homologyFunctor _ q).obj K))
    (c : Compactification h) [QuasiCompact c.i] :
    ∀ q : ℤ, Scheme.IsConstructibleEtaleModuleSheaf
      ((_root_.DerivedCategory.Plus.homologyFunctor _ q).obj
        ((rightDerivedLowerShriekOfCompactificationPlus (ModuleCat.{u + 1} Λ) c).obj K)) := by
  obtain ⟨T₁, a, g, ha, hac, hg, hgfp, hgqc, hgqs, hag, hT₁, hT₁qs⟩ :=
    h.exists_qcqs_finitePresentation_factorization hqf
  have := ha
  have := hac
  have := hg
  have := hgfp
  have := hgqc
  have := hgqs
  have := hT₁
  have := hT₁qs
  let d : Compactification h :=
    { Z := T₁, i := a, g := g, comm := hag.symm,
      isProper := inferInstance, isOpenImmersion := ha }
  have : QuasiCompact d.i := hac
  intro q
  let F := (_root_.DerivedCategory.Plus.homologyFunctor _ q).obj K
  have : Scheme.IsConstructibleSheaf F :=
    (Scheme.isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf F).mp (hK q)
  have hzero : Scheme.IsConstructibleEtaleModuleSheaf
      ((openImmersionLowerShriek (ModuleCat.{u + 1} Λ) a).obj F) :=
    (Scheme.isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf _).mpr
      (Scheme.IsConstructibleSheaf.openImmersionLowerShriek
        a a.closedComplement a.range_closedComplement F)
  have hfinite :=
    Scheme.isConstructibleEtaleModuleSheaf_lowerStar_of_finite_finitePresentation g _ hzero
  have : Scheme.IsConstructibleSheaf
      ((lowerStar (ModuleCat.{u + 1} Λ) g).obj
        ((openImmersionLowerShriek (ModuleCat.{u + 1} Λ) a).obj F)) :=
    (Scheme.isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf _).mp hfinite
  let J := (openImmersionLowerShriek (ModuleCat.{u + 1} Λ) a).mapDerivedCategoryPlus.obj K
  let e₁ := (_root_.DerivedCategory.Plus.homologyFunctor _ q).mapIso
      ((lowerStar (ModuleCat.{u + 1} Λ) g).rightDerivedFunctorPlusIsoMapDerivedCategoryPlus.app J)
    ≪≫ ((lowerStar (ModuleCat.{u + 1} Λ) g).mapDerivedCategoryPlusHomologyFunctorIso q).symm.app J
  let e₂ := (lowerStar (ModuleCat.{u + 1} Λ) g).mapIso
    ((Functor.mapDerivedCategoryPlusHomologyFunctorIso
      (openImmersionLowerShriek (ModuleCat.{u + 1} Λ) a) q).symm.app K)
  let e₃ := (_root_.DerivedCategory.Plus.homologyFunctor _ q).mapIso
    ((rightDerivedLowerShriekOfCompactificationPlusIso Λ c d).app K)
  exact (Scheme.isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf _).mpr
    (Scheme.IsConstructibleSheaf.of_iso
      (F := (lowerStar (ModuleCat.{u + 1} Λ) g).obj
        ((openImmersionLowerShriek (ModuleCat.{u + 1} Λ) a).obj F))
      (e₃ ≪≫ e₁ ≪≫ e₂).symm)

/-- The closed-immersion consequence of quasi-finite constructibility. -/
theorem constructibleCohomology_lowerShriek_of_isClosedImmersion
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    {T B : Scheme.{u}} [CompactSpace T] [QuasiSeparatedSpace T]
    [CompactSpace B] [QuasiSeparatedSpace B] (h : T ⟶ B)
    [IsClosedImmersion h] [LocallyOfFinitePresentation h]
    (K : _root_.DerivedCategory.Plus (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (hK : ∀ q : ℤ, Scheme.IsConstructibleEtaleModuleSheaf
      ((_root_.DerivedCategory.Plus.homologyFunctor _ q).obj K))
    (c : Compactification h) [QuasiCompact c.i] :
    ∀ q : ℤ, Scheme.IsConstructibleEtaleModuleSheaf
      ((_root_.DerivedCategory.Plus.homologyFunctor _ q).obj
        ((rightDerivedLowerShriekOfCompactificationPlus (ModuleCat.{u + 1} Λ) c).obj K)) := by
  apply constructibleCohomology_lowerShriek_of_quasiFinite Λ h _ K hK c
  refine ⟨inferInstance, inferInstance, fun x ↦ ?_⟩
  exact Scheme.Hom.quasiFiniteAt_iff_isOpen_singleton_asFiber.mp (h.quasiFiniteAt x)

end AlgebraicGeometry.Etale
