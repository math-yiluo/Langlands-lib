/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.Ringed.RingedDerivedClosedSymmetricMonoidal
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
public import WeilConjectures.Algebra.Homology.Site.SiteTensorFunctorialitySupplement
public import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
public import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import Mathlib.CategoryTheory.Limits.EssentiallySmall
public import WeilConjectures.Mathlib.Algebra.Homology.Monoidal
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import WeilConjectures.CategoryTheory.RingedForgetTensorTransposition.RingedTensorAssociatorDetection

/-! # The canonical chain associator models the ringed derived associator

Source: Stacks 0FPQ, 0FPT; detection on local pure triples.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option Elab.async false
set_option linter.style.haveILetI false
universe c w
open CategoryTheory CategoryTheory.MonoidalCategory WeilConjectures
namespace CategoryTheory.RingedForgetTensorTransposition

attribute [local irreducible] SheafOfModules.monoidalCategory
  DerivedCategory instCategoryDerivedCategory DerivedCategory.Q

variable {C : Type c} [SmallCategory C] (J : GrothendieckTopology C)
  [HasSheafify J AddCommGrpCat.{c}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{c}]
  (R : Sheaf J CommRingCat.{c})
  [HasDerivedCategory.{w} (RingedTensorModules.{c, c, c} J R)]
  (S : CoefficientClosedStructure (derivedInternalHomOfUniverses.{c, c, c, w} J R))
  (T : CoefficientTensorModels.{c, c, c, w} J R S)
  (β : @SymmetricCategory _ _ S.monoidal)
  (coh : RingedDerivedTensorCoherence.{c, c, c, w} J R S T β)

-- Comparing the two concrete tensor presentations requires additional elaboration steps.
/-- The concrete cochain associator gives the derived associator on K-flat models.
Source: Stacks 0FPQ, 0FPT
(blueprint: lem-sf-ringed-derived-associator-model-native).

Proof: apply the supplied derived associator model and identify its chain
isomorphism with the canonical associator by its local pure-triple formula.
Use tensorIso_both to change the two inner one-K-flat choices. -/
theorem coefficientAssociator_model_native
    (P Q N : CochainComplex (RingedTensorModules.{c, c, c} J R) ℤ)
    (hP : P.IsKFlatIndependentCoefficients) (hQ : Q.IsKFlatIndependentCoefficients)
    (hN : N.IsKFlatIndependentCoefficients) :
    letI := SheafOfModules.isMonoidal_W_independentCoefficients R
    letI := SheafOfModules.monoidalCategory R
    letI := S.monoidal
    let q := DerivedCategory.Q (C := RingedTensorModules.{c, c, c} J R)
    let B := coefficientTotalTensor.{c, c, c} J R
    (coh.tensorIso (B.obj (P, Q)) N (Or.inr hN) ≪≫
      whiskerRightIso (coh.tensorIso P Q (Or.inr hQ)) (q.obj N)).hom ≫
        (α_ (q.obj P) (q.obj Q) (q.obj N)).hom =
      q.map (α_ P Q N).hom ≫
        (coh.tensorIso P (B.obj (Q, N)) (Or.inl hP) ≪≫
          whiskerLeftIso (q.obj P) (coh.tensorIso Q N (Or.inr hN))).hom := by
  letI := SheafOfModules.isMonoidal_W_independentCoefficients R
  letI := SheafOfModules.monoidalCategory R
  letI := S.monoidal
  obtain ⟨a, ha, hm⟩ := coh.associator_model P Q N hP hQ hN
  have he := coefficientAssociator_eq_native J R P Q N a ha
  rw [he] at hm
  have hPQ := coh.tensorIso_both P Q hP hQ
  have hQN := coh.tensorIso_both Q N hQ hN
  simpa only [Iso.trans_hom, whiskerRightIso_hom, whiskerLeftIso_hom,
    ← tensorHom_id, ← id_tensorHom, hPQ, hQN, CoefficientClosedStructure.tensor,
    tensor_map, Category.assoc] using hm

end CategoryTheory.RingedForgetTensorTransposition
