/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.AdicImmersionResidueComparisonCore
import WeilConjectures.AlgebraicGeometry.AdicResidueNormalization
import all WeilConjectures.AlgebraicGeometry.AdicStratumCompletionUnit
import WeilConjectures.AlgebraicGeometry.ImmersionConstantResidueSquare

/-! # Residue comparisons for the specified completed immersion pullback

Source: Stacks Tags 03A0, 03CY, 06YY, 099L and 099R.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048

attribute [local instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall

universe u
open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme

private local instance modelSheafify (S : Scheme.{u}) :
    HasSheafify (proEtaleModelTopology S) AddCommGrpCat.{u + 1} :=
  SheafOfModules.hasSheafify_coefficientUniverse.{u + 1, u + 1, u + 1}

private local instance modelLocallyBijective (S : Scheme.{u}) :
    (proEtaleModelTopology S).WEqualsLocallyBijective AddCommGrpCat.{u + 1} :=
  SheafOfModules.wEqualsLocallyBijective_coefficientUniverse.{u + 1, u + 1, u + 1}

private local instance fixedSheafify (X : Scheme.{u}) :
    HasSheafify (ProEt.topology X) AddCommGrpCat.{u + 1} :=
  SheafOfModules.hasSheafify_coefficientUniverse.{u + 1, u, u + 1}

attribute [local instance 50000] modelSheafify modelLocallyBijective fixedSheafify

private local instance standardDerived {D : Type (u + 1)} [SmallCategory D]
    {J : GrothendieckTopology D} (O : Sheaf J CommRingCat.{u + 1}) :
    HasDerivedCategory (ConstantCompletion.Mod O) := HasDerivedCategory.standard _

private local instance fixedLocallyBijective (X : Scheme.{u}) :
    (ProEt.topology X).WEqualsLocallyBijective AddCommGrpCat.{u + 1} :=
  SheafOfModules.wEqualsLocallyBijective_coefficientUniverse.{u + 1, u, u + 1}

private noncomputable local instance modelAbelian (S : Scheme.{u})
    (R : Sheaf (proEtaleModelTopology S) CommRingCat.{u + 1}) :
    Abelian (ConstantCompletion.Mod R) :=
  SheafOfModules.instAbelian.{u + 1, u + 1, u + 1, u + 1} _

private noncomputable local instance fixedAbelian (X : Scheme.{u})
    (R : Sheaf (ProEt.topology X) CommRingCat.{u + 1}) :
    Abelian (proEtaleRingModules X R) :=
  SheafOfModules.instAbelian.{u + 1, u, u + 1, u + 1} _

attribute [local instance 40000] modelAbelian fixedAbelian standardDerived
  fixedLocallyBijective
attribute [local instance 30000] proEtaleRingModules_hasDerivedCategory

private local instance residueModelInverseEquivalence (X : Scheme.{u})
    (k : Type (u + 1)) [CommRing k] :
    (SfbAdicRestriction.modelEquivalence X (ModuleCat.{u + 1} k)).inverse.IsEquivalence :=
  (SfbAdicRestriction.modelEquivalence X (ModuleCat.{u + 1} k)).isEquivalence_inverse

private local instance residueScalarInverseEquivalence (X : Scheme.{u})
    (k : Type (u + 1)) [CommRing k] :
    (ConstantScalarRestriction.restriction
      (proEtaleModelTopology X) k).asEquivalence.inverse.IsEquivalence :=
  (ConstantScalarRestriction.restriction
    (proEtaleModelTopology X) k).asEquivalence.isEquivalence_inverse

private local instance residueModelInverseAdditive (X : Scheme.{u})
    (k : Type (u + 1)) [CommRing k] :
    (SfbAdicRestriction.modelEquivalence X (ModuleCat.{u + 1} k)).inverse.Additive :=
  Functor.additive_of_preserves_binary_products _

private local instance residueScalarInverseAdditive (X : Scheme.{u})
    (k : Type (u + 1)) [CommRing k] :
    (ConstantScalarRestriction.restriction
      (proEtaleModelTopology X) k).asEquivalence.inverse.Additive :=
  Functor.additive_of_preserves_binary_products _

attribute [-instance] coefficientModelAdditiveSheafify coefficientEtaleModelAdditiveSheafify
  ConstantScalarRestriction.ringAbelian ConstantScalarRestriction.fixedAbelian
  ConstantScalarRestriction.ringGrothendieck ConstantScalarRestriction.fixedGrothendieck
  WeilConjectures.integralCoefficientAbSheafify
  WeilConjectures.integralCoefficientAbLocallyBijective in
/-- The fixed completed-model residue comparison, isolated from the etale comparison clause.
Source: Stacks Tags 03A0, 03CY, 06YY, 099L and 099R; Bhatt--Scholze, Lemma 6.5.8
(auxiliary; not a blueprint node).
Proof: apply the normalized finite derived comparison at exponent one to the
transported inverse image.  The finite comparison is then conjugated by the
AsSmall and fixed-scalar equivalences, yielding the displayed isomorphism for
every completed complex.  This is the first clause of the parent comparison
statement and is strictly smaller because it contains no etale-origin clause.
-/
theorem sfbImmersion_residueComparison_fixed
    {X S : Scheme.{u}} (i : S ⟶ X) [IsImmersion i]
    {A : Type (u + 1)} [CommRing A] [IsNoetherianRing A] (I : Ideal A) :
    letI := HasDerivedCategory.standard
      (ConstantCompletion.Mod (ConstantCompletion.constant (proEtaleModelTopology S)
        (A ⧸ I ^ (0 + 1))))
    ∀ K : @DerivedCategory (proEtaleRingModules X (adicLisseCompletedRing X I)) _ _
        (proEtaleRingModules_hasDerivedCategory X (adicLisseCompletedRing X I)),
      Nonempty ((ConstantCompletion.extend
        (ConstantCompletion.projection (proEtaleModelTopology S) A I 0)).obj
          (sfbImmersionCompletedModel i I K) ≅
        (Functor.mapDerivedCategory.{u + 1, u + 2}
          (SfbResidueComparisonCore.sfbFixedResiduePull i (A ⧸ I ^ (0 + 1)))).obj
          (DerivedCategory.Q.obj (sfbResidueComplex X I K))) := by
  let := HasDerivedCategory.standard
    (ConstantCompletion.Mod (ConstantCompletion.constant (proEtaleModelTopology S)
      (A ⧸ I ^ (0 + 1))))
  intro K
  obtain ⟨n⟩ := sfbResidue_normalization X I K
  obtain ⟨e⟩ := sfbImmersion_constantResidueSquare i (A ⧸ I ^ (0 + 1))
  refine ⟨(SfbAdicRestriction.finiteComparison (sfbImmersionAlgebra i)
    (SfbAdicRestriction.direct i) (SfbAdicRestriction.adjunction i) A I 0).app
      (SfbCompletionNormalization.object X I K) ≪≫ ?_⟩
  let T : Sheaf (ProEt.topology X) (ModuleCat.{u + 1} (A ⧸ I ^ (0 + 1))) ⥤
      ConstantCompletion.Mod (ConstantCompletion.constant (proEtaleModelTopology X)
        (A ⧸ I ^ (0 + 1))) :=
    (SfbAdicRestriction.modelEquivalence X
    (ModuleCat.{u + 1} (A ⧸ I ^ (0 + 1)))).inverse ⋙
      (ConstantScalarRestriction.restriction (proEtaleModelTopology X)
        (A ⧸ I ^ (0 + 1))).asEquivalence.inverse
  letI : T.IsEquivalence := by
    dsimp [T]
    infer_instance
  letI : T.Additive := Functor.additive_of_preserves_binary_products T
  let d := ConstantCompletion.derivedPull (sfbImmersionAlgebra i)
    (SfbAdicRestriction.direct i) (SfbAdicRestriction.adjunction i)
    (ConstantCompletion.constantMap (sfbImmersionAlgebra i) (A ⧸ I ^ (0 + 1)))
  let C := sfbResidueComplex X I K
  let P := (T.mapHomologicalComplex (.up ℤ)).obj C
  have : IsIso (ConstantCompletion.constantMap (sfbImmersionAlgebra i)
      (A ⧸ I ^ (0 + 1))) := by
    change IsIso (((sfbImmersionAlgebra i).constants.app
      (CommRingCat.of (A ⧸ I ^ (0 + 1)))).hom)
    infer_instance
  have := SfbAdicRestriction.derivedPull_computes (sfbImmersionAlgebra i)
    (SfbAdicRestriction.direct i) (SfbAdicRestriction.adjunction i)
    (ConstantCompletion.constantMap (sfbImmersionAlgebra i) (A ⧸ I ^ (0 + 1))) P
  exact d.functor.mapIso n ≪≫
    d.functor.mapIso (T.mapDerivedCategoryFactors.app C) ≪≫
    asIso (d.comparison.app P) ≪≫
    (ConstantCompletion.Q _).mapIso
      ((Functor.mapHomologicalComplexCompIso e (.up ℤ)).app C) ≪≫
    ((SfbResidueComparisonCore.sfbFixedResiduePull i
      (A ⧸ I ^ (0 + 1))).mapDerivedCategoryFactors.app C).symm

end AlgebraicGeometry.Scheme
