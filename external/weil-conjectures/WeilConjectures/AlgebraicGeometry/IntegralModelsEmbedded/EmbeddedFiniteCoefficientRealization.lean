/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.IntegralModelsEmbedded.IntegralModelsEmbedded

/-! # Realization of the embedded constant finite coefficient ring

Use the specified constant-function scalar map,
followed by the existing intrinsic realization. No coefficient isomorphism is chosen.

## References

* Stacks Tags 03ET and 00YV
* Stacks Tags 099L and 03ET
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open WeilConjectures.SixFunctors
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale.IntegralModelsEmbedded

attribute [local irreducible] upperStarFromPoint upperStarFromPointComp
  monoidal_upperStarFromPoint monoidal_pointUpperStar oplaxMonoidal_pointUpperStar

/-- Constant functions on the point, with precisely the scalar map used for the integers. -/
def finiteScalarPointMap (A : Type) [CommRing A] [TopologicalSpace A]
    [IsTopologicalRing A] : discreteObj.{u} A ⟶ Profinite.continuousMapRingObj.{u} A :=
  (sheafCompose _ (forget₂ RingCat.{u + 1} Ab.{u + 1})).map (constantToContinuous A)

/-- Constant functions preserve multiplication and the unit. -/
instance finiteScalarPointMap_mon (A : Type) [CommRing A] [TopologicalSpace A]
    [IsTopologicalRing A] : IsMonHom (finiteScalarPointMap.{u} A) :=
  Sheaf.isMonHom_sheafCompose_map (coherentTopology Profinite.{u}) (constantToContinuous A)

/-- The specified constant-function scalar map after pullback to the scheme. -/
def finiteScalarMap (X : Scheme.{u}) (A : Type) [CommRing A] [TopologicalSpace A]
    [IsTopologicalRing A] := (upperStarFromPoint X).map (finiteScalarPointMap A)

/-- Pullback retains the ring-object homomorphism. -/
instance finiteScalarMap_mon (X : Scheme.{u}) (A : Type) [CommRing A]
    [TopologicalSpace A] [IsTopologicalRing A] : IsMonHom (finiteScalarMap X A) :=
  inferInstanceAs (IsMonHom ((upperStarFromPoint X).map (finiteScalarPointMap A)))

set_option backward.isDefEq.respectTransparency.types false in
attribute [-instance] integralModel_coefficientMonObj in
/-- Realize the constant embedded coefficient presentation via constant functions.
This is the concrete composite of the two existing derived functors. -/
def finiteRealization (X : Scheme.{u}) (A : Type) [CommRing A] [TopologicalSpace A]
    [IsTopologicalRing A] [Finite A] [DiscreteTopology A] :
    letI : HasSheafify (Scheme.ProEt.topology X) AddCommGrpCat.{u + 1} :=
      CategoryTheory.siteAbelianHasSheafify.{u + 1, u, u + 1} _
    letI : (Scheme.ProEt.topology X).WEqualsLocallyBijective AddCommGrpCat.{u + 1} :=
      CategoryTheory.siteAbelianWEqualsLocallyBijective.{u + 1, u, u + 1} _
    DerivedCategory.{u + 1} (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (discreteObj.{u} A) X)) ⥤
        Scheme.proEtaleDerivedCategory.{u} X (ULift.{u, 0} A) := by
  letI : HasSheafify (Scheme.ProEt.topology X) AddCommGrpCat.{u + 1} :=
    CategoryTheory.siteAbelianHasSheafify.{u + 1, u, u + 1} _
  letI : (Scheme.ProEt.topology X).WEqualsLocallyBijective AddCommGrpCat.{u + 1} :=
    CategoryTheory.siteAbelianWEqualsLocallyBijective.{u + 1, u, u + 1} _
  exact (Mod.extendScalars (C := Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
    (finiteScalarMap.{u} X A)).leftDerivedFunctor ⋙
      (integralModelIntrinsicRealization.{u} X A).rightDerivedFunctor

/-- The actual first constant reduction, with its source and target fixed explicitly. -/
@[irreducible] def constantFirstReduction (ℓ : ℕ) [Fact ℓ.Prime]
    (E : PadicAlgCl.FiniteIntermediateField ℓ) (π : PadicAlgCl.integers ℓ E.1)
    (X : Scheme.{u}) :
    DerivedCategory.{u + 1} (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (discreteObj (PadicAlgCl.integers ℓ E.1)) X)) ⥤
    DerivedCategory.{u + 1} (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (discreteObj (completedResidue ℓ E π 0)) X)) := by
  exact (Mod.extendScalars (residueMap ℓ E π X)).leftDerivedFunctor

set_option backward.isDefEq.respectTransparency.types false in
attribute [-instance] integralModel_coefficientMonObj in
/-- The actual first continuous reduction, with its source and target fixed explicitly. -/
@[irreducible] def continuousFirstReduction (ℓ : ℕ) [Fact ℓ.Prime]
    (E : PadicAlgCl.FiniteIntermediateField ℓ) (π : PadicAlgCl.integers ℓ E.1)
    (X : Scheme.{u}) :
    DerivedCategory.{u + 1} (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (integralCoefficientObject X ℓ E)) ⥤
    DerivedCategory.{u + 1} (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousMapRingObj (completedResidue ℓ E π 0)) X)) := by
  exact (Mod.extendScalars (integralModelReductionMap X ℓ E π 1).hom).leftDerivedFunctor

set_option backward.isDefEq.respectTransparency.types false in
attribute [-instance] integralModel_coefficientMonObj in
/-- The specified realized first reduction, with the intermediate scalar categories hidden. -/
@[irreducible] def constantResidueRealization (ℓ : ℕ) [Fact ℓ.Prime]
    (E : PadicAlgCl.FiniteIntermediateField ℓ) (π : PadicAlgCl.integers ℓ E.1)
    (X : Scheme.{u}) [Finite (completedResidue ℓ E π 0)]
    [DiscreteTopology (completedResidue ℓ E π 0)] :
    letI : HasSheafify (Scheme.ProEt.topology X) AddCommGrpCat.{u + 1} :=
      CategoryTheory.siteAbelianHasSheafify.{u + 1, u, u + 1} _
    letI : (Scheme.ProEt.topology X).WEqualsLocallyBijective AddCommGrpCat.{u + 1} :=
      CategoryTheory.siteAbelianWEqualsLocallyBijective.{u + 1, u, u + 1} _
    DerivedCategory.{u + 1} (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (integralCoefficientObject X ℓ E)) ⥤
        Scheme.proEtaleDerivedCategory.{u} X (ULift.{u, 0} (completedResidue ℓ E π 0)) := by
  letI : HasSheafify (Scheme.ProEt.topology X) AddCommGrpCat.{u + 1} :=
    CategoryTheory.siteAbelianHasSheafify.{u + 1, u, u + 1} _
  letI : (Scheme.ProEt.topology X).WEqualsLocallyBijective AddCommGrpCat.{u + 1} :=
    CategoryTheory.siteAbelianWEqualsLocallyBijective.{u + 1, u, u + 1} _
  exact restriction ℓ E X ⋙ constantFirstReduction ℓ E π X ⋙ finiteRealization X
    (completedResidue ℓ E π 0)

set_option backward.isDefEq.respectTransparency.types false in
attribute [-instance] integralModel_coefficientMonObj in
/-- The specified realized first reduction, with the intermediate scalar categories hidden. -/
@[irreducible] def continuousResidueRealization (ℓ : ℕ) [Fact ℓ.Prime]
    (E : PadicAlgCl.FiniteIntermediateField ℓ) (π : PadicAlgCl.integers ℓ E.1)
    (X : Scheme.{u}) [Finite (completedResidue ℓ E π 0)]
    [DiscreteTopology (completedResidue ℓ E π 0)] :
    letI : HasSheafify (Scheme.ProEt.topology X) AddCommGrpCat.{u + 1} :=
      CategoryTheory.siteAbelianHasSheafify.{u + 1, u, u + 1} _
    letI : (Scheme.ProEt.topology X).WEqualsLocallyBijective AddCommGrpCat.{u + 1} :=
      CategoryTheory.siteAbelianWEqualsLocallyBijective.{u + 1, u, u + 1} _
    DerivedCategory.{u + 1} (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (integralCoefficientObject X ℓ E)) ⥤
        Scheme.proEtaleDerivedCategory.{u} X (ULift.{u, 0} (completedResidue ℓ E π 0)) := by
  letI : HasSheafify (Scheme.ProEt.topology X) AddCommGrpCat.{u + 1} :=
    CategoryTheory.siteAbelianHasSheafify.{u + 1, u, u + 1} _
  letI : (Scheme.ProEt.topology X).WEqualsLocallyBijective AddCommGrpCat.{u + 1} :=
    CategoryTheory.siteAbelianWEqualsLocallyBijective.{u + 1, u, u + 1} _
  exact continuousFirstReduction ℓ E π X ⋙
    (integralModelIntrinsicRealization X (completedResidue ℓ E π 0)).rightDerivedFunctor

end AlgebraicGeometry.ProEtale.IntegralModelsEmbedded
