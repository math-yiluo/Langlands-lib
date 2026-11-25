/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.IntegralConstantModelRealization
public import WeilConjectures.AlgebraicGeometry.IntegralModelsStacksData

/-! # The normalized completed integral section ring

Source: Stacks Tags 099C, 099L and 00YV.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale.IntegralModelsStacks

attribute [local irreducible] upperStarFromPoint integralSectionRingIso
  WeilConjectures.purCoefficientIso Scheme.pbcCompletedComparison
  IntegralConstantModel.pointComparison

/-- Section reconstruction of the specified point comparison.
Source: Stacks Tag 00YV and the normalized integral point identification.
(auxiliary; not a blueprint node). -/
def pointSectionIso (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (X : Scheme.{u}) :
    InternalAbelianSheafModule.sectionRingSheaf.{u + 1, u + 1, u} (Scheme.ProEt.topology X)
        (AdicCompletion.ring l E X) ≅
      InternalAbelianSheafModule.sectionRingSheaf.{u + 1, u + 1, u} (Scheme.ProEt.topology X)
        (condensedRingObj (integersObj l E) X) := by
  let e := (upperStarFromPoint X).mapMon.mapIso (IntegralConstantModel.pointComparison l E)
  let c : CommMon.mk (AdicCompletion.ring l E X) ≅
      CommMon.mk (condensedRingObj (integersObj l E) X) :=
    (CommMon.fullyFaithfulForget₂Mon _).preimageIso e
  let h := (Monoidal.commMonFunctorCategoryEquivalence X.ProEtᵒᵖ Ab.{u + 1}).functor.mapIso
    ((sheafToPresheaf (Scheme.ProEt.topology X) Ab.{u + 1}).mapCommMon.mapIso c)
  let k := Functor.isoWhiskerRight h InternalAbelianSheafModule.commMonToRing
  exact { hom := ⟨k.hom⟩, inv := ⟨k.inv⟩,
          hom_inv_id := by ext1; exact k.hom_inv_id
          inv_hom_id := by ext1; exact k.inv_hom_id }

/-- The normalized completed coefficient ring, in continuous section coordinates.
Source: Stacks Tags 00YV and 099L, and the normalized integral limit comparison.
(auxiliary; not a blueprint node). -/
def completedSectionIso (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (X : Scheme.{u}) :
    Scheme.adicLisseCompletedRing X (IntegralConstantCompletion.ideal l E) ≅
      InternalAbelianSheafModule.sectionRingSheaf.{u + 1, u + 1, u}
        (Scheme.ProEt.topology X) (condensedRingObj (integersObj l E) X) :=
  Scheme.pbcCompletedComparison X (Scheme.pbcIntegralDatum l E) ≪≫
    WeilConjectures.purCoefficientIso l E X ≪≫
      (integralSectionRingIso l E X).symm ≪≫ pointSectionIso l E X

end AlgebraicGeometry.ProEtale.IntegralModelsStacks
