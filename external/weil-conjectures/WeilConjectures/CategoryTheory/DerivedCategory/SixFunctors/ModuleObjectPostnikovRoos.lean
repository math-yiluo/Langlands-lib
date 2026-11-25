/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CondensedModuleDerivedPushpull
public import WeilConjectures.CategoryTheory.SixFunctors.ModuleObjects
public import Mathlib.CategoryTheory.Functor.OfSequence
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import WeilConjectures.CategoryTheory.Triangulated.HomotopyLimit
import WeilConjectures.CategoryTheory.DerivedCategory.SixFunctors.RoosEventuallyConstant
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.TStructure
import WeilConjectures.CategoryTheory.InternalAbelianSheafModuleEquivalence
import Mathlib.Algebra.Category.ModuleCat.Sheaf
import Mathlib.Algebra.Category.Ring.Limits
import Mathlib.CategoryTheory.Monoidal.Internal.FunctorCategory
import WeilConjectures.CategoryTheory.RingObjects.Ab
import WeilConjectures.CategoryTheory.Sites.MonObj
import WeilConjectures.CategoryTheory.ModuleObjects.MapMod
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

/-! The canonical Postnikov Roos cone for condensed module objects. -/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated Opposite
open AlgebraicGeometry.ProEtale
open scoped CategoryTheory.Obj

namespace DerivedCategory

/-- The inverse tower of canonical lower truncations, with the canonical transition maps.
Source: blueprint main-20261015, lemma-proper-direct-image-unbounded-complexes--1, limit
presentation (blueprint: lem-module-object-postnikov-roos). -/
def lowerPostnikovTower {C : Type*} [Category C] [Abelian C] [HasDerivedCategory C]
    (K : DerivedCategory C) : ℕᵒᵖ ⥤ DerivedCategory C :=
  Functor.ofOpSequence (X := fun n : ℕ ↦ (TStructure.t.truncGE (-(n : ℤ))).obj K)
    (fun n ↦ (TStructure.t.natTransTruncGEOfLE (-((n + 1 : ℕ) : ℤ)) (-(n : ℤ))
      (by omega)).app K)

/-- The canonical quotient cone over the lower Postnikov tower.
Source: blueprint main-20261015, lemma-proper-direct-image-unbounded-complexes--1, limit
presentation (blueprint: lem-module-object-postnikov-roos). -/
def lowerPostnikovCone {C : Type*} [Category C] [Abelian C] [HasDerivedCategory C]
    (K : DerivedCategory C) : Cone (lowerPostnikovTower K) :=
  Cone.mk K (NatTrans.ofOpSequence
    (fun n ↦ (TStructure.t.truncGEπ (-(n : ℤ))).app K) (fun n ↦ by
      simp [lowerPostnikovTower]))

end DerivedCategory

private theorem lower_postnikov_isHomotopyLimit
    {C : Type*} [Category C] [Abelian C] [HasDerivedCategory C]
    [HasCountableProducts (DerivedCategory C)]
    (hprod : ∀ j : ℤ, PreservesLimitsOfShape (Discrete ℕ)
      (DerivedCategory.homologyFunctor C j)) (K : DerivedCategory C) :
    IsHomotopyLimit (DerivedCategory.lowerPostnikovCone K) := by
  let F := DerivedCategory.lowerPostnikovTower K
  let c := DerivedCategory.lowerPostnikovCone K
  let P : Fan (fun n : ℕ ↦ F.obj (op n)) := Fan.mk _ (Pi.π _)
  let hP : IsLimit P := productIsProduct _
  let ℓ : K ⟶ P.pt := Fan.IsLimit.lift hP (fun n ↦ c.π.app (op n))
  obtain ⟨L, a, δ, hT⟩ := distinguished_cocone_triangle₁ (𝟙 P.pt - towerShift hP)
  let T := Triangle.mk a (𝟙 P.pt - towerShift hP) δ
  have hz : ℓ ≫ (𝟙 P.pt - towerShift hP) = 0 := by
    rw [Preadditive.comp_sub, Category.comp_id, lift_comp_towerShift hP c]
    exact sub_self _
  obtain ⟨v, hv⟩ := T.coyoneda_exact₂ hT ℓ hz
  change K ⟶ L at v
  change ℓ = v ≫ a at hv
  have ha : a ≫ towerShift hP = a := by
    have hh := comp_distTriang_mor_zero₁₂ T hT
    change a ≫ (𝟙 P.pt - towerShift hP) = 0 at hh
    exact (sub_eq_zero.mp (by
      simpa only [Preadditive.comp_sub, Category.comp_id] using hh)).symm
  let cL : Cone F := Cone.mk L (NatTrans.ofOpSequence
    (fun n ↦ a ≫ P.proj n) (fun n ↦ by
      change 𝟙 L ≫ a ≫ P.proj n =
        (a ≫ P.proj (n + 1)) ≫ F.map (homOfLE n.le_succ).op
      rw [Category.id_comp]
      symm
      rw [Category.assoc, ← towerShift_proj, ← Category.assoc, ha]))
  have hfac : ∀ n : ℕ, v ≫ cL.π.app (op n) = c.π.app (op n) := by
    intro n
    dsimp [cL]
    rw [← Category.assoc, ← hv]
    exact Fan.IsLimit.fac hP _ n
  have hcL : IsHomotopyLimit cL := by
    refine ⟨P, hP, δ, ?_⟩
    have hh : Fan.IsLimit.lift hP (fun n ↦ cL.π.app (op n)) = a := by
      apply Fan.IsLimit.hom_ext hP
      intro n
      exact Fan.IsLimit.fac hP _ n
    simpa only [hh] using hT
  have hvIso : IsIso v := by
    apply DerivedCategory.isIso_iff C v |>.2
    intro q
    let N : ℕ := (1 - q).toNat
    have hπ (n : ℕ) (hn : N ≤ n) (r : ℤ) (hr : q - 1 ≤ r) :
        IsIso ((DerivedCategory.homologyFunctor C r).map (c.π.app (op n))) := by
      exact DerivedCategory.isIso_homologyFunctor_map_truncGEπ_app K (-(n : ℤ)) r
        (by dsimp [N] at hn; omega)
    have ht (n : ℕ) (hn : N ≤ n) (r : ℤ) (hr : q - 1 ≤ r) :
        IsIso ((DerivedCategory.homologyFunctor C r).map
          (F.map (homOfLE n.le_succ).op)) := by
      have := hπ n hn r hr
      have := hπ (n + 1) (by omega) r hr
      have hh := congrArg (DerivedCategory.homologyFunctor C r).map
        (c.w (homOfLE n.le_succ).op)
      simp only [Functor.map_comp] at hh
      have hcomp : IsIso (((DerivedCategory.homologyFunctor C r).map
          (c.π.app (op (n + 1)))) ≫
          (DerivedCategory.homologyFunctor C r).map
            (F.map (homOfLE n.le_succ).op)) := by
        rw [hh]
        infer_instance
      exact IsIso.of_isIso_comp_left
        ((DerivedCategory.homologyFunctor C r).map (c.π.app (op (n + 1))))
        ((DerivedCategory.homologyFunctor C r).map (F.map (homOfLE n.le_succ).op))
    have hi := DerivedCategory.isIso_homology_map_cone_leg_of_eventually_isIso
      F cL hcL hprod q N (fun n hn ↦ ⟨ht n hn q (by omega), ht n hn (q - 1) le_rfl⟩)
      N le_rfl
    have := hπ N le_rfl q (by omega)
    have hh := congrArg (DerivedCategory.homologyFunctor C q).map (hfac N)
    rw [Functor.map_comp] at hh
    have hcomp : IsIso (((DerivedCategory.homologyFunctor C q).map v) ≫
        (DerivedCategory.homologyFunctor C q).map (cL.π.app (op N))) := by
      rw [hh]
      infer_instance
    exact IsIso.of_isIso_comp_right
      ((DerivedCategory.homologyFunctor C q).map v)
      ((DerivedCategory.homologyFunctor C q).map (cL.π.app (op N)))
  apply hcL.of_iso (Iso.refl F) c (asIso v).symm
  intro n
  simp only [Iso.refl_hom, NatTrans.id_app, Category.comp_id, Iso.symm_hom, asIso_inv]
  rw [← hfac n, IsIso.inv_hom_id_assoc]

private theorem exact_products (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (X : AlgebraicGeometry.Scheme.{u}) :
    HasExactLimitsOfShape (Discrete ℕ) (pulledBackModuleObjects Λ X) := by
  let J := AlgebraicGeometry.Scheme.ProEt.topology X
  let R := condensedRingObj Λ X
  let e := InternalAbelianSheafModule.sectionModuleEquivalence.{u + 1, u + 1, u} J R
  let S : Sheaf J RingCat.{u + 1} :=
    (sheafCompose J (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
      (InternalAbelianSheafModule.sectionRingSheaf.{u + 1, u + 1, u} J R)
  have := AlgebraicGeometry.Scheme.ProEt.products_exact.{u, 0, 0} X S ℕ
  exact HasExactLimitsOfShape.of_codomain_equivalence _ e.symm

namespace AlgebraicGeometry.ProEtale.CondensedRing

/-- The derived direct image of the canonical Postnikov cone is a homotopy limit cone,
and cohomology on the target preserves countable products.
Source: blueprint main-20261015, det-proper-unbounded-window-arbitrary.proof.md,
Limit presentation, and proposition-exact-products--2
(blueprint: lem-module-object-postnikov-roos).

Proof: Transfer exact countable products across the internal/sectionwise module
 equivalence. The general derived-product theorem then makes cohomology preserve them.
Complete 1-T on the product of the lower truncations to a distinguished triangle,
with first object L. The canonical projection cone factors through L by exactness.
In each cohomological degree the truncation projections and transitions are eventually
isomorphisms. The eventual-tower Milnor lemma therefore shows that the factor K -> L
is an isomorphism on every cohomology object, hence an isomorphism. Transport the
homotopy-limit cone along its inverse, keeping all canonical projections. Finally the
derived direct image is triangulated and a right adjoint, so preserves the product
and the entire homotopy-limit cone. No properness or boundedness is used.
-/
theorem moduleObjectDerivedPushforward_postnikov_roos
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X Y : Scheme.{u}} (p : X ⟶ Y)
    (K : DerivedCategory (pulledBackModuleObjects Λ X)) :
    IsHomotopyLimit ((moduleObjectDerivedPushforward Λ p).mapCone
      (DerivedCategory.lowerPostnikovCone K)) ∧
    (∀ j : ℤ, PreservesLimitsOfShape (Discrete ℕ)
      (DerivedCategory.homologyFunctor (pulledBackModuleObjects Λ Y) j)) := by
  have hprod (Z : AlgebraicGeometry.Scheme.{u}) (j : ℤ) :
      PreservesLimitsOfShape (Discrete ℕ)
        (DerivedCategory.homologyFunctor (pulledBackModuleObjects Λ Z) j) := by
    let := exact_products Λ Z
    infer_instance
  let : HasCountableProducts (DerivedCategory (pulledBackModuleObjects Λ X)) :=
    ⟨fun J ↦ DerivedCategory.hasLimitsOfShape_discrete _ J⟩
  let F := CondensedRing.moduleObjectDerivedPushforward Λ p
  let : F.CommShift ℤ := by
    dsimp only [F, CondensedRing.moduleObjectDerivedPushforward]
    infer_instance
  let : F.IsTriangulated := by
    dsimp only [F, CondensedRing.moduleObjectDerivedPushforward]
    infer_instance
  let : F.IsRightAdjoint := by
    dsimp only [F, CondensedRing.moduleObjectDerivedPushforward]
    infer_instance
  exact ⟨(lower_postnikov_isHomotopyLimit (hprod X) K).map F, hprod Y⟩

end AlgebraicGeometry.ProEtale.CondensedRing
