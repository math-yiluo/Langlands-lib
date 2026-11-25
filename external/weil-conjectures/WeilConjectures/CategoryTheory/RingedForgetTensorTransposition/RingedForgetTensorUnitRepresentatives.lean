/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.RingedForgetTensorTransposition.RingedForgetTensorTranspositionData
import WeilConjectures.CategoryTheory.RingedForgetTensorTransposition.RingedForgetTensorUnitLeftRepresentatives
import WeilConjectures.CategoryTheory.RingedForgetTensorTransposition.RingedForgetTensorUnitRightRepresentatives

/-! # Representative constraints for exact ringed tensor comparison

Source: Stacks Project, Tags 0FPT, 06YU and 0G7D
(blueprint: lem-sf-ringed-forget-tensor-unit-representatives).
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

variable [HasDerivedCategory.{wb} (RingedTensorModules.{c, v, r} J R)]
  [HasDerivedCategory.{wa} (RingedTensorModules.{d, vd, s} J' R')]
  [∀ I : Type (max c v r), PreservesLimitsOfShape (Discrete I) U]
  [U.PreservesKInjectiveComplexes]
  (u : Underived.{c, v, r, d, vd, s} J R J' R' U)
  (SB : CoefficientClosedStructure (derivedInternalHomOfUniverses.{c, v, r, wb} J R))
  (TB : CoefficientTensorModels.{r, c, v, wb} J R SB)
  (βB : @SymmetricCategory (DerivedCategory (RingedTensorModules.{c, v, r} J R))
    _ SB.monoidal)
  (cB : RingedDerivedTensorCoherence.{c, v, r, wb} J R SB TB βB)
  (SA : CoefficientClosedStructure (derivedInternalHomOfUniverses.{d, vd, s, wa} J' R'))
  (TA : CoefficientTensorModels.{s, d, vd, wa} J' R' SA)
  (βA : @SymmetricCategory (DerivedCategory (RingedTensorModules.{d, vd, s} J' R'))
    _ SA.monoidal)
  (cA : RingedDerivedTensorCoherence.{d, vd, s, wa} J' R' SA TA βA)

/-- The normalized unit is a composite of existing isomorphisms, with no chosen data.
Source: Stacks 0FPT, the unit part of the representative construction
(blueprint: lem-sf-ringed-forget-tensor-unit-representatives). -/
def ringedForgetTensorUnitIso :
    U.mapDerivedCategory.obj SB.monoidal.tensorUnit ≅ SA.monoidal.tensorUnit :=
  U.mapDerivedCategory.mapIso cB.unitIso ≪≫
    U.mapDerivedCategoryFactors.app (ringedTensorUnitComplex.{c, v, r} J R) ≪≫
    DerivedCategory.Q.mapIso
      ((HomologicalComplex.singleMapHomologicalComplex U (.up ℤ) 0).app
        (SheafOfModules.unit ((sheafCompose J
          (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R))) ≪≫
    DerivedCategory.Q.mapIso
      ((HomologicalComplex.single _ (.up ℤ) (0 : ℤ)).mapIso u.coherence.unit) ≪≫
    cA.unitIso.symm

/-- Both unit squares on a flat-term K-flat representative for the explicitly
constructed degree-zero unit comparison. No assertion is made on other objects,
or about associators or symmetry.

Source: Stacks Project, sites-cohomology.tex, Tags 0FPT and 06YU;
the unit part of step 3 of lem-sf-ringed-forget-tensor-coherence
(blueprint: lem-sf-ringed-forget-tensor-unit-representatives).

Proof: the coefficient ring placed in degree zero is flat-term K-flat. Apply the
representative square to it and P. Substitute the displayed composite defining
ringedForgetTensorUnitIso, and use the left-unitor-model equations of cB and cA.
Naturality of the tensor model for the degree-zero unit isomorphism and the
exact-functor localization factor reduces the equation to the localized chain
unit square. In degree n, restrict to the (0,n) summand; all other summands
vanish since the single complex is zero away from zero. The summand equation
and the single-complex comparison reduce the square to u.coherence.left_unit.
The sheafification universal property and local pure tensors detect the
structural maps, without requiring global generation. The right-unit proof is
the same calculation on (n,0), using cB.rightUnitor_model, cA.rightUnitor_model
and u.coherence.right_unit. -/
theorem ringed_forget_tensor_unit_representatives
    (hU : ∀ P : CochainComplex (RingedTensorModules.{c, v, r} J R) ℤ,
      P.IsKFlatIndependentCoefficients →
      (∀ p : ℤ, SheafOfModules.IsFlatOnSite.{c, v, max c v r, max c v r}
        (R := R) (P.X p)) →
      CochainComplex.IsKFlatIndependentCoefficients (R := R')
        ((U.mapHomologicalComplex (.up ℤ)).obj P) ∧
      ∀ p : ℤ, SheafOfModules.IsFlatOnSite.{d, vd, max d vd s, max d vd s}
        (R := R') (U.obj (P.X p)))
    (chain : coefficientTotalTensor.{r, c, v} J R ⋙ U.mapHomologicalComplex (.up ℤ) ≅
      ((U.mapHomologicalComplex (.up ℤ)).prod (U.mapHomologicalComplex (.up ℤ))) ⋙
        coefficientTotalTensor.{s, d, vd} J' R')
    (summand : ∀ (P Q : CochainComplex (RingedTensorModules.{c, v, r} J R) ℤ)
      (p q n : ℤ) (hpq : p + q = n),
      U.map (tensorSummand.{c, v, r} J R P Q p q n hpq) ≫ (chain.hom.app (P, Q)).f n =
        u.tensor.hom.app (P.X p, Q.X q) ≫
          tensorSummand.{d, vd, s} J' R' ((U.mapHomologicalComplex (.up ℤ)).obj P)
            ((U.mapHomologicalComplex (.up ℤ)).obj Q) p q n hpq)
    (μ : SB.tensor ⋙ U.mapDerivedCategory ≅
      (U.mapDerivedCategory.prod U.mapDerivedCategory) ⋙ SA.tensor)
    (hμ : RepresentativeModel.{c, v, r, d, vd, s, wb, wa}
      J R J' R' U SB TB SA TA chain μ.hom)
    (P : CochainComplex (RingedTensorModules.{c, v, r} J R) ℤ)
    (hP : P.IsKFlatIndependentCoefficients)
    (fP : ∀ p : ℤ, SheafOfModules.IsFlatOnSite.{c, v, max c v r, max c v r}
      (R := R) (P.X p)) :
    (μ.hom.app (SB.monoidal.tensorUnit, DerivedCategory.Q.obj P) ≫
        SA.tensor.map
          (X := (U.mapDerivedCategory.obj SB.monoidal.tensorUnit,
            U.mapDerivedCategory.obj (DerivedCategory.Q.obj P)))
          (Y := (SA.monoidal.tensorUnit, U.mapDerivedCategory.obj (DerivedCategory.Q.obj P)))
          ((ringedForgetTensorUnitIso J R J' R' U u SB TB βB cB SA TA βA cA).hom, 𝟙 _) ≫
        (SA.monoidal.leftUnitor (U.mapDerivedCategory.obj (DerivedCategory.Q.obj P))).hom =
      U.mapDerivedCategory.map (SB.monoidal.leftUnitor (DerivedCategory.Q.obj P)).hom) ∧
    (μ.hom.app (DerivedCategory.Q.obj P, SB.monoidal.tensorUnit) ≫
        SA.tensor.map
          (X := (U.mapDerivedCategory.obj (DerivedCategory.Q.obj P),
            U.mapDerivedCategory.obj SB.monoidal.tensorUnit))
          (Y := (U.mapDerivedCategory.obj (DerivedCategory.Q.obj P), SA.monoidal.tensorUnit))
          (𝟙 _, (ringedForgetTensorUnitIso J R J' R' U u SB TB βB cB SA TA βA cA).hom) ≫
        (SA.monoidal.rightUnitor (U.mapDerivedCategory.obj (DerivedCategory.Q.obj P))).hom =
      U.mapDerivedCategory.map (SB.monoidal.rightUnitor (DerivedCategory.Q.obj P)).hom) := by
  exact ⟨ringed_forget_tensor_left_representatives (J := J) (R := R) (J' := J')
    (R' := R') (U := U) (u := u) (SB := SB) (TB := TB) (βB := βB) (cB := cB)
    (SA := SA) (TA := TA) (βA := βA) (cA := cA) hU chain summand μ hμ P hP fP,
    ringed_forget_tensor_right_representatives (J := J) (R := R) (J' := J')
      (R' := R') (U := U) (u := u) (SB := SB) (TB := TB) (βB := βB) (cB := cB)
      (SA := SA) (TA := TA) (βA := βA) (cA := cA) hU chain summand μ hμ P hP fP⟩

end CategoryTheory.RingedForgetTensorTransposition
