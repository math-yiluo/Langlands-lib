/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.SiteCoveringAxioms
public import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import WeilConjectures.Algebra.Homology.Site.SiteTensorFunctorialitySupplement
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Homology.HomologicalComplexAbelian
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.ConstantFieldFlat
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import Mathlib.CategoryTheory.Limits.ExactFunctor
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import WeilConjectures.CategoryTheory.RingedSiteModules
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.CategoryTheory.Sites.ConstantSheaf
import Mathlib.Algebra.Field.Defs
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatEquationalCriterionOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatLocalRelationsOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
import WeilConjectures.CategoryTheory.Sites.WeakSheafifyAddCommGrpLeftExact
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Submodule
import Mathlib.LinearAlgebra.TensorProduct.Vanishing
import Mathlib.RingTheory.TensorProduct.DirectLimitFG
import Mathlib.LinearAlgebra.TensorProduct.Finiteness
import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.ConstantFieldLocalSections
import Mathlib.CategoryTheory.Sites.LocallyBijective
import Mathlib.Algebra.Category.Ring.Basic
import Mathlib.Algebra.Category.Ring.Adjunctions
import Mathlib.CategoryTheory.Adjunction.Limits
import Mathlib.Algebra.Category.Ring.Limits
import Mathlib.RingTheory.Flat.EquationalCriterion
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology

/-!
# Cohomology and tensor product over a constant field sheaf

Source: the blueprint, `lem-exc-residue-tor-test.proof.md`, second paragraph;
Stacks Project, Tags 03CY, 03ET, 0GMW, 00WJ and 010N
(blueprint: lem-exc-constant-field-sheaf-tensor-cohomology).
-/

@[expose] public section

universe uC vC r m

open CategoryTheory CategoryTheory.Limits

namespace SheafOfModules

set_option backward.isDefEq.respectTransparency false

private theorem tensorMap_tmul
    {C : Type uC} [Category.{vC} C] {J : GrothendieckTopology C}
    [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
    [J.WEqualsLocallyBijective AddCommGrpCat.{m}] [HasSheafify J AddCommGrpCat.{m}]
    {A : Sheaf J CommRingCat.{r}}
    {M M' : SheafOfModules.{m} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj A)}
    (N : SheafOfModules.{m} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj A))
    (f : M ⟶ M') (U : Cᵒᵖ) (x : M.val.obj U) (y : N.val.obj U) :
    (((siteSheafTensorRight N).map f).val.app U) (siteSheafTensorTmul M N U x y) =
      siteSheafTensorTmul M' N U ((f.val.app U) x) y := by
  have h := (PresheafOfModules.sheafificationAdjunction
    (R := (sheafCompose J (forget₂ CommRingCat RingCat)).obj A) (𝟙 _)).unit.naturality
      (siteTensorHom f.val N.val)
  have hU := congrArg (fun a ↦ (a.app U) (x ⊗ₜ[A.obj.obj U] y)) h
  exact hU.symm

/-- Tensoring with any module sheaf over the constant field sheaf commutes with cohomology,
naturally in both variables, and sends `[z] ⊗ y` to `[z ⊗ y]` on local sections.
Source: blueprint `lem-exc-residue-tor-test.proof.md`, second paragraph, expanded by Stacks
Tags 03CY, 03ET, 0GMW, 00WJ and 010N
(blueprint: lem-exc-constant-field-sheaf-tensor-cohomology).

Proof:
1. Restrict a module sheaf N along the map from the constant presheaf field to its
sheafification. Its sections are vector spaces over the field; its associated module
sheaf is N, by the module-sheafification interface [lem-pc-sites-module-sheafification-interface].
This does not identify sections of the constant sheaf with the field itself.
2. Vector spaces are free, hence projective [lem-weil-pbc-vector-space-projective] and flat
[lem-weil-pbc-projective-module-flat]. Tensoring sections preserves kernels by
[lem-weil-pbc-flat-tensor-exact], and preserves finite products by the usual two-factor
sum of pure tensors. Equalizers are kernels of differences, so the presheaf tensor functor
preserves finite limits, which are computed objectwise.
3. By [lem-pc-sites-modules-sheafification-flat], sheafification gives flatness of N.
Thus the sheaf tensor functor is exact [def-pc-flat-sheaf-modules] in the abelian module
sheaf category [situation-conventions].
4. Apply [lem-sp-exact-functor-preserves-homology] to the three terms in degrees i-1,i,i+1.
Its kernel and image comparisons, compatible with the cycle and quotient maps, give
the displayed isomorphisms and naturality in chain maps. No boundedness is required.
5. The tensor of a cycle section with y is a cycle; changing the cycle by a boundary
changes this tensor by a boundary. The quotient compatibility therefore sends `[z] ⊗ y`
to `[z ⊗ y]`. Both composites for a morphism N → N' send this to `[z ⊗ g(y)]`.
Pure tensors and cycle classes locally generate the sheafified tensor and quotient,
so these equalities give naturality in N and the required local formula. -/
theorem exists_constantFieldTensorCohomology
    {C : Type uC} [Category.{vC} C] (J : GrothendieckTopology C)
    [EssentiallySmall.{m} C] [HasWeakSheafify J CommRingCat.{r}]
    [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
    [J.WEqualsLocallyBijective AddCommGrpCat.{m}] [HasSheafify J AddCommGrpCat.{m}]
    (κ : Type r) [Field κ] (i : ℤ) :
    ∃ e : ∀
      (N : ringedSiteModules.{m} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj
        ((constantSheaf J CommRingCat.{r}).obj (CommRingCat.of κ))))
      (K : CochainComplex
        (ringedSiteModules.{m} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj
          ((constantSheaf J CommRingCat.{r}).obj (CommRingCat.of κ)))) ℤ),
      (siteSheafTensorRight N).obj (K.homology i) ≅
        (((siteSheafTensorRight N).mapHomologicalComplex (ComplexShape.up ℤ)).obj K).homology i,
      (∀ N K L (f : K ⟶ L),
        (e N K).hom ≫ HomologicalComplex.homologyMap
            (((siteSheafTensorRight N).mapHomologicalComplex (ComplexShape.up ℤ)).map f) i =
          (siteSheafTensorRight N).map (HomologicalComplex.homologyMap f i) ≫ (e N L).hom) ∧
      (∀ N N' (g : N ⟶ N') K,
        (e N K).hom ≫ HomologicalComplex.homologyMap
            (((siteSheafTensorRightMap g).mapHomologicalComplex (ComplexShape.up ℤ)).app K) i =
          (siteSheafTensorRightMap g).app (K.homology i) ≫ (e N' K).hom) ∧
      (∀ N (K : CochainComplex
          (ringedSiteModules.{m} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj
            ((constantSheaf J CommRingCat.{r}).obj (CommRingCat.of κ)))) ℤ)
          (U : Cᵒᵖ) (z : (K.cycles i).val.obj U) (y : N.val.obj U),
        ∃ w : ((((siteSheafTensorRight N).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj K).cycles i).val.obj U,
          (((((siteSheafTensorRight N).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj K).iCycles i).val.app U) w =
              siteSheafTensorTmul (K.X i) N U (((K.iCycles i).val.app U) z) y ∧
          (((e N K).hom.val.app U)
            (siteSheafTensorTmul (K.homology i) N U (((K.homologyπ i).val.app U) z) y)) =
              (((((siteSheafTensorRight N).mapHomologicalComplex
                (ComplexShape.up ℤ)).obj K).homologyπ i).val.app U) w) := by
  classical
  have hflat : ∀ N : ringedSiteModules.{m} ((sheafCompose J
      (forget₂ CommRingCat RingCat)).obj
        ((constantSheaf J CommRingCat.{r}).obj (CommRingCat.of κ))), IsFlatOnSite N :=
    fun N ↦ isFlat_constantFieldModule J κ N
  let hpres (N : ringedSiteModules.{m} ((sheafCompose J
      (forget₂ CommRingCat RingCat)).obj
        ((constantSheaf J CommRingCat.{r}).obj (CommRingCat.of κ)))) :
      (siteSheafTensorRight N).PreservesHomology := by
    have hl : PreservesFiniteLimits (siteSheafTensorRight N) := (hflat N).1
    have hr : PreservesFiniteColimits (siteSheafTensorRight N) := (hflat N).2
    infer_instance
  let e (N : ringedSiteModules.{m} ((sheafCompose J
      (forget₂ CommRingCat RingCat)).obj
        ((constantSheaf J CommRingCat.{r}).obj (CommRingCat.of κ))))
      (K : CochainComplex (ringedSiteModules.{m} ((sheafCompose J
        (forget₂ CommRingCat RingCat)).obj
          ((constantSheaf J CommRingCat.{r}).obj (CommRingCat.of κ)))) ℤ) :
      (siteSheafTensorRight N).obj (K.homology i) ≅
        (((siteSheafTensorRight N).mapHomologicalComplex (ComplexShape.up ℤ)).obj K).homology i :=
    ((K.sc i).mapHomologyIso (siteSheafTensorRight N)).symm
  refine ⟨e, ?_, ?_, ?_⟩
  · intro N K L f
    exact (ShortComplex.mapHomologyIso_inv_naturality
      ((HomologicalComplex.shortComplexFunctor _ _ i).map f) (siteSheafTensorRight N)).symm
  · intro N N' g K
    change ((K.sc i).mapHomologyIso (siteSheafTensorRight N)).inv ≫
      ShortComplex.homologyMap ((K.sc i).mapNatTrans (siteSheafTensorRightMap g)) = _
    rw [ShortComplex.homologyMap_mapNatTrans]
    simp only [Iso.inv_hom_id_assoc]
    rfl
  · intro N K U z y
    let F := siteSheafTensorRight N
    let S := K.sc i
    let c := S.mapCyclesIso F
    let t := siteSheafTensorTmul (K.cycles i) N U z y
    let w := (c.inv.val.app U) t
    refine ⟨w, ?_, ?_⟩
    · have hc : c.inv ≫ (S.map F).iCycles = F.map S.iCycles := by
        rw [← ShortComplex.mapCyclesIso_hom_iCycles S F, Iso.inv_hom_id_assoc]
      have h := congrArg (fun a ↦ (a.val.app U) t) hc
      exact h.trans (tensorMap_tmul N (K.iCycles i) U z y)
    · have hπ : F.map S.homologyπ ≫ (S.mapHomologyIso F).inv =
          c.inv ≫ (S.map F).homologyπ := by
        dsimp only [c]
        rw [S.homologyData.left.mapHomologyIso_eq F,
          S.homologyData.left.mapCyclesIso_eq F]
        change F.map S.homologyπ ≫
            (F.map S.homologyData.left.homologyIso.hom ≫
              (S.homologyData.left.map F).homologyIso.inv) =
          (F.map S.homologyData.left.cyclesIso.hom ≫
            (S.homologyData.left.map F).cyclesIso.inv) ≫ (S.map F).homologyπ
        rw [← Category.assoc, ← F.map_comp,
          ShortComplex.LeftHomologyData.homologyπ_comp_homologyIso_hom,
          F.map_comp, Category.assoc, Category.assoc]
        congr 1
        exact (S.homologyData.left.map F).π_comp_homologyIso_inv
      have h := congrArg (fun a ↦ (a.val.app U) t) hπ
      rw [← tensorMap_tmul N (K.homologyπ i) U z y]
      exact h

end SheafOfModules
