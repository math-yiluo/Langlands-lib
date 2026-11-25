/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.RingedForgetTensorTransposition.RingedForgetTensorTranspositionData

/-! # Representative constraints for exact ringed tensor comparison

Source: Stacks Project, Tags 0FPT, 06YU and 0G7D
(blueprint: lem-sf-ringed-forget-tensor-chain-symmetry).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option Elab.async false

universe b vb a va c v r d vd s wb wa
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite WeilConjectures
-- Keep the chosen internal-Hom and localization constructions behind their APIs.
attribute [local irreducible] homComplexFunctor homComplexπ derivedInternalHomOfUniverses
  coefficientHomResolutionIso Functor.mapDerivedCategory Functor.mapDerivedCategoryFactors
  DerivedCategory instCategoryDerivedCategory DerivedCategory.Q
  SheafOfModules.IsFlatOnSite
  CochainComplex.IsKFlatIndependentCoefficients

namespace CategoryTheory.RingedForgetTensorTransposition

variable {C : Type c} [Category.{v} C] (J : GrothendieckTopology C)
  [HasSheafify J AddCommGrpCat.{max c v r}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max c v r}]
  (R : Sheaf J CommRingCat.{max c v r})

variable {D : Type d} [Category.{vd} D] (J' : GrothendieckTopology D)
  [HasSheafify J' AddCommGrpCat.{max d vd s}]
  [J'.WEqualsLocallyBijective AddCommGrpCat.{max d vd s}]
  (R' : Sheaf J' CommRingCat.{max d vd s})
  (U : RingedTensorModules.{c, v, r} J R ⥤ RingedTensorModules.{d, vd, s} J' R')
  [U.Additive] [PreservesFiniteLimits U] [PreservesFiniteColimits U]

variable (u : Underived.{c, v, r, d, vd, s} J R J' R' U)

omit [PreservesFiniteLimits U] [PreservesFiniteColimits U]
-- Component checking traverses the totalization and sheaf tensor instances.
/-- The total-tensor comparison commutes with the signed chain swaps.
Source: Stacks 0FPT and 06YU; the chain calculation in the symmetry part of
lem-sf-ringed-forget-tensor-coherence
(blueprint: lem-sf-ringed-forget-tensor-chain-symmetry).

Proof: precompose with the inverse comparison, then test every target coproduct
summand. The summand law expresses its inverse as the inverse underived tensor
comparison followed by the image of the source inclusion. Rewrite the source
signed swap, preserve its integer scalar by additivity, and apply the underived
symmetry square. Cancel the inverse tensor comparison. The target signed swap
has precisely the resulting summand restriction. This proves equality of the
component maps and hence of chain maps, without assuming coproduct preservation. -/
theorem ringed_forget_tensor_chain_symmetry
    (chain : coefficientTotalTensor.{r, c, v} J R ⋙ U.mapHomologicalComplex (.up ℤ) ≅
      ((U.mapHomologicalComplex (.up ℤ)).prod (U.mapHomologicalComplex (.up ℤ))) ⋙
        coefficientTotalTensor.{s, d, vd} J' R')
    (summand : ∀ (P Q : CochainComplex (RingedTensorModules.{c, v, r} J R) ℤ)
      (p q n : ℤ) (hpq : p + q = n),
      U.map (tensorSummand.{c, v, r} J R P Q p q n hpq) ≫
        (chain.hom.app (P, Q)).f n = u.tensor.hom.app (P.X p, Q.X q) ≫
          tensorSummand.{d, vd, s} J' R' ((U.mapHomologicalComplex (.up ℤ)).obj P)
            ((U.mapHomologicalComplex (.up ℤ)).obj Q) p q n hpq)
    (P Q : CochainComplex (RingedTensorModules.{c, v, r} J R) ℤ)
    (sB : (coefficientTotalTensor.{r, c, v} J R).obj (P, Q) ≅
      (coefficientTotalTensor.{r, c, v} J R).obj (Q, P))
    (sA : (coefficientTotalTensor.{s, d, vd} J' R').obj
        ((U.mapHomologicalComplex (.up ℤ)).obj P, (U.mapHomologicalComplex (.up ℤ)).obj Q) ≅
      (coefficientTotalTensor.{s, d, vd} J' R').obj
        ((U.mapHomologicalComplex (.up ℤ)).obj Q, (U.mapHomologicalComplex (.up ℤ)).obj P))
    (hsB : ∀ (p q n : ℤ) (h : p + q = n) (h' : q + p = n),
      tensorSummand.{c, v, r} J R P Q p q n h ≫ sB.hom.f n =
        ((p * q).negOnePow : ℤ) •
          ((SheafOfModules.symmetricCategory R).toBraidedCategory.braiding
            (P.X p) (Q.X q)).hom ≫ tensorSummand.{c, v, r} J R Q P q p n h')
    (hsA : ∀ (p q n : ℤ) (h : p + q = n) (h' : q + p = n),
      tensorSummand.{d, vd, s} J' R' ((U.mapHomologicalComplex (.up ℤ)).obj P)
          ((U.mapHomologicalComplex (.up ℤ)).obj Q) p q n h ≫ sA.hom.f n =
        ((p * q).negOnePow : ℤ) •
          ((SheafOfModules.symmetricCategory R').toBraidedCategory.braiding
            (U.obj (P.X p)) (U.obj (Q.X q))).hom ≫
            tensorSummand.{d, vd, s} J' R' ((U.mapHomologicalComplex (.up ℤ)).obj Q)
              ((U.mapHomologicalComplex (.up ℤ)).obj P) q p n h') :
    (U.mapHomologicalComplex (.up ℤ)).map sB.hom ≫ chain.hom.app (Q, P) =
      chain.hom.app (P, Q) ≫ sA.hom := by
  let := SheafOfModules.isMonoidal_W_independentCoefficients R'
  let := SheafOfModules.monoidalCategory R'
  let := SheafOfModules.preservesZeroMorphisms_curriedTensor_independentCoefficients R'
  let := SheafOfModules.preservesZeroMorphisms_curriedTensor_obj_independentCoefficients R'
  apply HomologicalComplex.hom_ext
  intro n
  change U.map (sB.hom.f n) ≫ (chain.hom.app (Q, P)).f n =
    (chain.hom.app (P, Q)).f n ≫ sA.hom.f n
  apply (cancel_epi ((chain.inv.app (P, Q)).f n)).mp
  apply HomologicalComplex.mapBifunctor.hom_ext
    (K₁ := (U.mapHomologicalComplex (.up ℤ)).obj P)
    (K₂ := (U.mapHomologicalComplex (.up ℤ)).obj Q)
    (F := curriedTensor (RingedTensorModules.{d, vd, s} J' R')) (c := .up ℤ)
  intro p q h
  change p + q = n at h
  have h' : q + p = n := by omega
  have hi : tensorSummand.{d, vd, s} J' R'
        ((U.mapHomologicalComplex (.up ℤ)).obj P)
        ((U.mapHomologicalComplex (.up ℤ)).obj Q) p q n h ≫
        (chain.inv.app (P, Q)).f n =
      u.tensor.inv.app (P.X p, Q.X q) ≫
        U.map (tensorSummand.{c, v, r} J R P Q p q n h) := by
    apply (cancel_mono ((chain.hom.app (P, Q)).f n)).mp
    have hh : (chain.inv.app (P, Q)).f n ≫ (chain.hom.app (P, Q)).f n = 𝟙 _ :=
      congrArg (fun f ↦ f.f n) (chain.app (P, Q)).inv_hom_id
    simp only [Category.assoc, hh, summand,
      Iso.inv_hom_id_app_assoc]
    exact Category.comp_id _
  change (tensorSummand.{d, vd, s} J' R'
      ((U.mapHomologicalComplex (.up ℤ)).obj P)
      ((U.mapHomologicalComplex (.up ℤ)).obj Q) p q n h ≫
        (chain.inv.app (P, Q)).f n) ≫ U.map (sB.hom.f n) ≫
          (chain.hom.app (Q, P)).f n =
    (tensorSummand.{d, vd, s} J' R'
      ((U.mapHomologicalComplex (.up ℤ)).obj P)
      ((U.mapHomologicalComplex (.up ℤ)).obj Q) p q n h ≫
        (chain.inv.app (P, Q)).f n) ≫ (chain.hom.app (P, Q)).f n ≫ sA.hom.f n
  rw [hi]
  simp only [Category.assoc]
  rw [← U.map_comp_assoc, hsB p q n h h', Functor.map_zsmul, Functor.map_comp]
  simp only [Category.assoc, summand, Preadditive.zsmul_comp, Preadditive.comp_zsmul]
  rw [reassoc_of% (u.coherence.symmetry (P.X p) (Q.X q))]
  erw [reassoc_of% (summand P Q p q n h)]
  simpa only [Iso.inv_hom_id_app_assoc] using (hsA p q n h h').symm

end CategoryTheory.RingedForgetTensorTransposition
