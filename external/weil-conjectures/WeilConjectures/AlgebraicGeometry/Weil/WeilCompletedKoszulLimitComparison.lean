/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Weil.WeilCompletedKoszulRepresentativeComparison
import WeilConjectures.CategoryTheory.StrictRoosDerivation
import WeilConjectures.CategoryTheory.StrictRoosModel
import Mathlib.CategoryTheory.Functor.Derived.RightDerived
import Mathlib.CategoryTheory.Whiskering
import Mathlib.Algebra.Homology.Functor
import Mathlib.CategoryTheory.Limits.Shapes.Countable
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Mathlib.Algebra.Homology.HomotopyCategory.MappingCocone
import Mathlib.Algebra.Homology.HomologicalComplexLimits
import Mathlib.CategoryTheory.Abelian.FunctorCategory
import WeilConjectures.CategoryTheory.Limits.TowerTransitionEndomorphism
import WeilConjectures.CategoryTheory.RingedSiteModules
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic
import WeilConjectures.Algebra.Homology.RoosComplex
import WeilConjectures.Algebra.Homology.DerivedCategory.TowerLimit
import WeilConjectures.CategoryTheory.RingedSiteModulesGrothendieckOfUniverses
import WeilConjectures.CategoryTheory.SiteCoveringAxioms
import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
import WeilConjectures.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses
import Mathlib.Algebra.Category.Grp.AB
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.Algebra.Category.Ring.Limits
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
import Mathlib.CategoryTheory.Yoneda
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import Mathlib.CategoryTheory.Generator.Basic
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolutionInjective
import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.KInjective
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
import WeilConjectures.Algebra.Homology.HomotopyCategory.Products
import WeilConjectures.CategoryTheory.Triangulated.DerivedLimit
import Mathlib.CategoryTheory.Sites.Equivalence
import Mathlib.CategoryTheory.Sites.LocallyBijective
import WeilConjectures.CategoryTheory.Sites.RGammaDerivedLimit
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.CategoryTheory.Adjunction.Evaluation
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.FunctorCategory
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
import WeilConjectures.AlgebraicGeometry.ProEtaleProductsExact
import Mathlib.AlgebraicGeometry.Sites.Proetale
import Mathlib.Algebra.Category.Grp.FilteredColimits
import WeilConjectures.AlgebraicGeometry.ProEtaleSectionsLimitsColimits
import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Proetale
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.CategoryTheory.Sites.Sheaf
import WeilConjectures.CategoryTheory.Sites.WeaklyContractible
import Mathlib.CategoryTheory.Limits.HasLimits
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Colimits
import Mathlib.CategoryTheory.Sites.PreservesSheafification
import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleWeaklyContractibleEvaluationColimitsSupplement
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

/-!
# Comparing the published Koszul fiber with the strict derived limit

Source: Stacks Project, algebraization.tex, Tag 0A0E,
lemma-derived-completion-koszul, and sites-cohomology.tex, Tags 0941 and 0A0A.
(blueprint: lem-weil-pbc-completed-fiber-strict-limit-comparison).

This is a comparison of constructions, including the specified units. It makes no
assertion about Cech complexes, completeness, or the mapping property of completion.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048

universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme

variable (X : Scheme.{u}) {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A)

set_option backward.isDefEq.respectTransparency false in
/-- The published signed Koszul fiber computes the prescribed strict derived limit,
including the canonical degree-zero unit, after the explicit ringed-site equivalence.

Source: Stacks Project, Tag 0A0E, proof of lemma-derived-completion-koszul;
Tags 0A0A and 0941; Bhatt--Scholze, Proposition 3.1.9.
(blueprint: lem-weil-pbc-completed-fiber-strict-limit-comparison).

Proof: use the explicit small site, completed ring and module equivalence above.
The coefficient restriction equivalence and the site equivalence preserve products
and tensor, and their induced derived equivalences commute with localization.
At power m+1, identify the exterior Koszul complex with the dual of the ordered tensor
of the positive two-term factors. On the basis of sorted k-element subsets in degree
-k, multiply the identification by (-1)^(k*(k-1)/2). The ratio in consecutive degrees
is (-1)^(k+1), the dual-differential sign, so contraction agrees with the differential.
The degree-zero identification is the identity. Both transitions multiply a subset
by the product of its generators. Tensoring with C therefore gives an isomorphism
of strict towers with their degree-zero units.

Exact countable products on the pro-etale site imply that the ordinary product of
complexes preserves quasi-isomorphisms. Resolve the strict tower by a K-injective
tower and apply its levelwise quasi-isomorphisms to products. The induced map on
the mapping fibers of 1-shift is a quasi-isomorphism. The strict-tower Roos theorem
computes the derived inverse limit on this resolution. Its right-derived universal
property identifies this computation with D.inverseLimit, normalized by D.comparison;
D.tensorFactors identifies its input with the actual strict tower. The compatible
degree-zero units have zero composite with 1-shift. Their zero-homotopy lift is
exactly the published (u,0) map, and all the displayed comparisons preserve that map.
The representative normalization in D.unit supplies the final equation.

For r=0 the tower is the constant identity tower and its fiber comparison carries
the diagonal unit to the identity. Zero or invertible generators, the zero ring and
the empty site satisfy the same formulas. No generation hypothesis is required. -/
theorem completed_fiber_strict_limit_comparison
    (X : Scheme.{u}) {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A)
    (r : ℕ) (a : Fin r → A)
    (C : CochainComplex (pbcModules X (pbcAdicCompletion X d)) ℤ) :
    let O := completedCechRing X d
    let F := completedCechDerivedEquiv X d
    let b := fun i ↦ completedCechScalar X d (a i)
    ∀ D : RingedKoszulLimitPresentation O r b,
      ∃ e : F.functor.obj (DerivedCategory.Q.obj (intrinsicCompletionComplex X d r a C)) ≅
          D.completion.obj (F.functor.obj (DerivedCategory.Q.obj C)),
        F.functor.map (DerivedCategory.Q.map (intrinsicCompletionComplexUnit X d r a C)) ≫
            e.hom = D.unit (F.functor.obj (DerivedCategory.Q.obj C)) := by
  classical
  dsimp only
  intro D
  let O := completedCechRing X d
  let F := completedCechDerivedEquiv X d
  let b := fun i ↦ completedCechScalar X d (a i)
  let B := ringedSiteModules.{u + 1, u + 1, u + 1, u + 1}
    ((sheafCompose (completedCechTopology X) (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj O)
  let P := DerivedCategory.Q.objPreimage (F.functor.obj (DerivedCategory.Q.obj C))
  let real := DerivedCategory.Q.objObjPreimageIso (F.functor.obj (DerivedCategory.Q.obj C))
  let T := ringedKoszulTensorTowerComplex O r b P
  obtain ⟨e, he⟩ := completed_fiber_roos_comparison X d r a C P real
  have : HasExactLimitsOfShape (Discrete ℕ) (pbcModules X (pbcAdicCompletion X d)) :=
    ProEt.products_exact.{u, u + 1} X
      ((sheafCompose (ProEt.topology X) (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
        (pbcAdicCompletion X d)) ℕ
  have : HasExactLimitsOfShape (Discrete ℕ) B :=
    HasExactLimitsOfShape.of_codomain_equivalence (Discrete ℕ) (completedCechModulesEquiv X d)
  obtain ⟨RF, κ, hRF, _⟩ := strictRoosDerivation.{u + 1, u + 1, u + 1, u + 2}
    (completedCechTopology X)
    ((sheafCompose (completedCechTopology X) (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj O)
    (fun U x y ↦ @mul_comm (O.obj.obj U) inferInstance x y)
  let W := HomologicalComplex.quasiIso (ℕᵒᵖ ⥤ B) (.up ℤ)
  let l := Functor.isoWhiskerRight
    (completedKoszulTermwiseLimitIso (B := B)) DerivedCategory.Q
  let eta := l.hom ≫ D.comparison
  have heta : D.inverseLimit.IsRightDerivedFunctor eta W := by
    rw [Functor.isRightDerivedFunctor_iff_isLeftKanExtension]
    have := D.isRightDerived
    have h' := Functor.IsRightDerivedFunctor.isLeftKanExtension
      D.inverseLimit D.comparison W
    exact (Functor.isLeftKanExtension_iff_of_iso₂ eta D.comparison l
      (Iso.refl _) (by simp [eta])).mpr h'
  let rho := RF.rightDerivedUnique D.inverseLimit (roosDerivedUnit κ) eta W
  have hunit : DerivedCategory.Q.map (roosι T) ≫ κ.hom.app T ≫
      rho.hom.app (DerivedCategory.Q.obj T) = eta.app T := by
    have h := RF.rightDerivedNatTrans_app D.inverseLimit (roosDerivedUnit κ)
      eta W (𝟙 _) T
    simpa [rho, Functor.rightDerivedUnique, Functor.rightDerivedNatIso,
      roosDerivedUnit, roosInclusion, roosLimitFunctor,
      Functor.rightDerivedNatTrans, Category.assoc] using h
  let k : DerivedCategory.Q.obj (roosF.obj T) ≅
      D.completion.obj (F.functor.obj (DerivedCategory.Q.obj C)) :=
    κ.app T ≪≫ rho.app (DerivedCategory.Q.obj T) ≪≫
      D.inverseLimit.mapIso (D.tensorFactors.app P).symm ≪≫ D.completion.mapIso real
  refine ⟨e ≪≫ k, ?_⟩
  dsimp only [Iso.trans_hom]
  rw [← Category.assoc, he]
  dsimp only [k, Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom]
  simp only [Functor.map_comp, Category.assoc]
  erw [reassoc_of% hunit]
  dsimp only [eta, NatTrans.comp_app, l, Functor.isoWhiskerRight_hom,
    Functor.whiskerRight_app]
  have hc : DerivedCategory.Q.map
      ((completedKoszulTermwiseLimitIso (B := B)).app T).inv ≫
      DerivedCategory.Q.map ((completedKoszulTermwiseLimitIso (B := B)).app T).hom =
        𝟙 _ := by
    rw [← Functor.map_comp, Iso.inv_hom_id]
    exact DerivedCategory.Q.map_id _
  change real.inv ≫ DerivedCategory.Q.map (ringedKoszulLimitUnit O r b P) ≫
    DerivedCategory.Q.map ((completedKoszulTermwiseLimitIso (B := B)).app T).inv ≫
    (DerivedCategory.Q.map ((completedKoszulTermwiseLimitIso (B := B)).app T).hom ≫
      D.comparison.app T) ≫
    D.inverseLimit.map (D.tensorFactors.app P).inv ≫ D.completion.map real.hom = _
  have hc' : DerivedCategory.Q.map
      ((completedKoszulTermwiseLimitIso (B := B)).app T).inv ≫
      (DerivedCategory.Q.map ((completedKoszulTermwiseLimitIso (B := B)).app T).hom ≫
        D.comparison.app T) = D.comparison.app T := by
    rw [← Category.assoc, hc, Category.id_comp]
  change _ = real.inv ≫
    (DerivedCategory.Q.map (ringedKoszulLimitUnit O r b P) ≫
      D.comparison.app T ≫ D.inverseLimit.map (D.tensorFactors.app P).inv) ≫
        D.completion.map real.hom
  simpa only [Category.assoc] using congrArg
    (fun h ↦ real.inv ≫ DerivedCategory.Q.map (ringedKoszulLimitUnit O r b P) ≫
      h ≫ D.inverseLimit.map (D.tensorFactors.app P).inv ≫ D.completion.map real.hom) hc'

end AlgebraicGeometry.Scheme
