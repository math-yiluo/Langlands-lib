/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Homology.HomologicalComplex
public import Mathlib.CategoryTheory.Functor.OfSequence
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import WeilConjectures.CategoryTheory.Triangulated.DerivedLimit
public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleSurjectiveTowerDerivedLimitSupplement

import WeilConjectures.AlgebraicGeometry.ProEtaleProductsExact
import Mathlib.AlgebraicGeometry.Sites.Proetale
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic
import WeilConjectures.AlgebraicGeometry.ProEtaleSectionsLimitsColimits
import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Proetale
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.CategoryTheory.Sites.Sheaf
import WeilConjectures.CategoryTheory.Sites.WeaklyContractible
import WeilConjectures.CategoryTheory.RingedSiteModules
import Mathlib.CategoryTheory.Limits.HasLimits
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Colimits
import Mathlib.CategoryTheory.Sites.PreservesSheafification
import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleWeaklyContractibleEvaluationColimitsSupplement
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import WeilConjectures.CategoryTheory.RingedSiteModulesGrothendieckOfUniverses
import WeilConjectures.CategoryTheory.SiteCoveringAxioms
import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
import WeilConjectures.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses
import Mathlib.Algebra.Category.Grp.AB
import Mathlib.Algebra.Category.Ring.Limits
import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
import Mathlib.CategoryTheory.Yoneda
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import Mathlib.CategoryTheory.Generator.Basic
import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolutionInjective
import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.KInjective
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
import WeilConjectures.Algebra.Homology.HomotopyCategory.Products
import WeilConjectures.CategoryTheory.Triangulated.DerivedLimit
import Mathlib.CategoryTheory.Sites.Equivalence
import Mathlib.CategoryTheory.Sites.LocallyBijective
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import WeilConjectures.CategoryTheory.Sites.RGammaDerivedLimit
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Coseparator
import WeilConjectures.AlgebraicGeometry.ProEtale.SectionsConservative
import WeilConjectures.AlgebraicGeometry.ProEtale.WeaklyContractible
import WeilConjectures.AlgebraicGeometry.WContractibleAffineCover
import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
import Mathlib.CategoryTheory.Sites.ConstantSheaf
import WeilConjectures.RingTheory.ProEtale.WContractible
import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
import Mathlib.RingTheory.RingHom.FaithfullyFlat
import WeilConjectures.RingTheory.ProperBaseChange.IndPrincipalZariski
import WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful
import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import Mathlib.Algebra.Category.ModuleCat.AB
import Mathlib.CategoryTheory.Limits.Preserves.Limits
import WeilConjectures.CategoryTheory.Triangulated.DerivedLimitProducts
import WeilConjectures.AlgebraicGeometry.ProEtaleMilnorEpimorphic
import WeilConjectures.AlgebraicGeometry.ProEtaleMilnorSequence
import WeilConjectures.SmoothPurity.Integral.IntegralOperationsWellDefinedSupplement
import WeilConjectures.AlgebraicGeometry.MilnorTower
import WeilConjectures.AlgebraicGeometry.RoosCohomologySequence
import WeilConjectures.AlgebraicGeometry.RoosCohomologyMaps
import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
import WeilConjectures.CategoryTheory.DerivedCategory.DegreewiseLimits
import WeilConjectures.Algebra.Homology.DerivedCategory.TowerLimit
import WeilConjectures.AlgebraicGeometry.RoosCohomologyNaturality
import Mathlib.Algebra.Homology.SingleHomology
import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleSurjectiveTowerDerivedLimitSupplement
import Mathlib.Algebra.Category.ModuleCat.Products
import WeilConjectures.Algebra.Homology.KernelShiftedMappingCone

/-!
# Bounds for derived limits with epimorphic top cohomology

The index `n: ℕ` denotes the positive level `n + 1` of the source tower.
The coefficient sheaf is written as a sheaf of rings with sectionwise commutativity;
this retains exactly the given ring and module structures. A derived limit is any
object satisfying the existing Roos-triangle property, without a chosen cone model.

## References

* Stacks Project, Tag 0947, (5)-(7) and its proof, specialized to the small pro-etale site
* Stacks Project, Tag 0947, (5)-(7) and its proof
-/

@[expose] public section

set_option autoImplicit false

universe t u w

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.ProEt

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall in
/-- A strict tower with cohomology in `[a,b]` and epimorphic top-cohomology
transitions has every derived limit cohomologically in the same interval. -/
theorem bounded_epimorphic_top_derivedLimit
    (X : Scheme.{t})
    (R : Sheaf (topology X) RingCat.{max u (t + 1)})
    (_hcomm : ∀ U : X.ProEtᵒᵖ, ∀ r s : R.obj.obj U, r * s = s * r)
    [HasDerivedCategory.{w} (ringedSiteModules.{max u (t + 1)} R)]
    (P : ℕ → CochainComplex (ringedSiteModules.{max u (t + 1)} R) ℤ)
    (τ : ∀ n : ℕ, P (n + 1) ⟶ P n)
    [HasProduct (fun n : ℕ ↦ DerivedCategory.Q.{w}.obj (P n))]
    (L : DerivedCategory (ringedSiteModules.{max u (t + 1)} R))
    (_hL : IsDerivedLimit (K := fun n : ℕ ↦ DerivedCategory.Q.{w}.obj (P n))
      (fun n : ℕ ↦ DerivedCategory.Q.{w}.map (τ n)) L)
    (a b : ℤ) (_hab : a ≤ b)
    (_hP : ∀ (n : ℕ) (j : ℤ), j < a ∨ b < j → IsZero ((P n).homology j))
    (_htop : ∀ n : ℕ, Epi (HomologicalComplex.homologyMap (τ n) b)) :
    ∀ j : ℤ, j < a ∨ b < j →
      IsZero ((DerivedCategory.homologyFunctor
        (ringedSiteModules.{max u (t + 1)} R) j).obj L) := by
  let A := ringedSiteModules.{max u (t + 1)} R
  let Q := DerivedCategory.Q.{w} (C := A)
  let K := fun n : ℕ ↦ Q.obj (P n)
  let f := fun n : ℕ ↦ Q.map (τ n)
  have : CountableAB4Star A := ⟨fun I _ ↦ products_exact X R I⟩
  have hH (j : ℤ) : PreservesLimitsOfShape (Discrete ℕ)
      (DerivedCategory.homologyFunctor A j) :=
    (derivedCategory_countableProducts_core A).choose_spec.2 ℕ j
  let H := DerivedCategory.homologyFunctor A
  have hzero (j : ℤ) (hj : j < a ∨ b < j) : IsZero ((H j).obj (∏ᶜ K)) := by
    have := hH j
    let hc := isLimitOfHasProductOfPreservesLimit (H j) K
    apply hc.isZero_pt
    apply (Functor.isZero_iff _).mpr
    intro ⟨n⟩
    exact (_hP n j hj).of_iso ((DerivedCategory.homologyFunctorFactors A j).app (P n))
  have htop (n : ℕ) : Epi ((H b).map (f n)) := by
    have := _htop n
    have he : Epi ((H b).map (f n) ≫
        (DerivedCategory.homologyFunctorFactors A b).hom.app (P n)) := by
      rw [DerivedCategory.homologyFunctorFactors_hom_naturality]
      infer_instance
    exact (epi_comp_iff_of_isIso _ _).mp he
  have htrans : Epi ((H b).map (towerTransitionEndomorphism (K := K) f)) := by
    have := hH b
    let M := Functor.ofOpSequence (X := fun n ↦ (H b).obj (K n))
      (fun n ↦ (H b).map (f n))
    have ht (n : ℕ) : Epi (M.map (homOfLE (Nat.le_succ n)).op) := by
      simpa [M] using htop n
    have he : Epi (towerTransitionEndomorphism (K := fun n ↦ (H b).obj (K n))
        (fun n ↦ (H b).map (f n))) := by
      simpa [M] using (AlgebraicGeometry.ProEtale.milnor_epimorphic X R M ht).1
    have hm : (H b).map (towerTransitionEndomorphism (K := K) f) ≫ piComparison (H b) K =
        piComparison (H b) K ≫
          towerTransitionEndomorphism (K := fun n ↦ (H b).obj (K n))
            (fun n ↦ (H b).map (f n)) := by
      apply Pi.hom_ext
      intro n
      rw [Category.assoc, piComparison_comp_π, ← Functor.map_comp]
      simp only [towerTransitionEndomorphism, towerProductShift, Preadditive.sub_comp,
        Category.id_comp, Pi.lift_comp_π,
        Preadditive.comp_sub, Category.assoc, piComparison_comp_π,
        piComparison_comp_π_assoc]
      rw [Functor.map_sub, Functor.map_comp]
    have : Epi ((H b).map (towerTransitionEndomorphism (K := K) f) ≫ piComparison (H b) K) := by
      rw [hm]
      exact inferInstance
    exact (epi_comp_iff_of_isIso _ (piComparison (H b) K)).mp inferInstance
  obtain ⟨p, δ, hT⟩ := _hL
  let T := Pretriangulated.Triangle.mk p (towerTransitionEndomorphism (K := K) f) δ
  have hT' : T ∈ distTriang _ := hT
  intro j hj
  by_cases h : j = b + 1
  · subst j
    have hδ := DerivedCategory.HomologySequence.comp_δ T hT' b (b + 1) rfl
    have : Epi ((H b).map T.mor₂) := htrans
    apply (DerivedCategory.HomologySequence.exact₁ T hT' b (b + 1) rfl).isZero_of_both_zeros
    · exact (cancel_epi ((H b).map T.mor₂)).mp (by simpa using hδ)
    · exact (hzero (b + 1) hj).eq_zero_of_tgt _
  · exact (DerivedCategory.HomologySequence.exact₁ T hT' (j - 1) j
      (by omega)).isZero_of_both_isZero (hzero (j - 1) (by omega)) (hzero j hj)

end AlgebraicGeometry.Scheme.ProEt
