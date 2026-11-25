/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.QuotientSectionTensor.QuotientSectionTensorData
import WeilConjectures.AlgebraicGeometry.IntegralResidueDerivedMonoidal

/-! # Conjugating the internal scalar tensor comparison

## References

* Stacks 07A4, functoriality of the canonical derived tensor comparison
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency.types false

attribute [local irreducible] CategoryTheory.Functor.leftDerivedFunctor
  CategoryTheory.Functor.mapDerivedCategory DerivedCategory.monoidalClosed
  CategoryTheory.Mod.monoidalClosed AlgebraicGeometry.ProEtale.upperStarFromPoint
  CategoryTheory.Sheaf.monoidalCategory
  DerivedCategory.monoidalCategoryOfMonoidalClosedBraidedCategory

universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open scoped CategoryTheory.Obj ChangeOfRings

namespace AlgebraicGeometry.ProEtale.QuotientSectionTensor

open QuotientChange IntegralQuotient
open ModuleRingedComparison

variable {Λ Λ' : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
  [MonObj Λ] [IsCommMonObj Λ] [MonObj Λ'] [IsCommMonObj Λ']
  (a : Λ ⟶ Λ') [IsMonHom a]
  [∀ T : Scheme.{u}, HasDerivedCategory.{u + 1} (modules Λ T)]
  [∀ T : Scheme.{u}, HasDerivedCategory.{u + 1} (modules Λ' T)]

/-- Conjugate an internal tensor comparison through the specified section equivalences. -/
theorem section_tensor_conjugate_exists (T : Scheme.{u})
    (c : ScalarSectionData a T) (b : TensorIso a T) :
    ∃ barB : tensor Λ T ⋙ c.model.T ≅
        (c.model.T.prod c.model.T) ⋙ tensor Λ' T,
      TensorSectionCondition a T c b barB := by
  let ed := derivedEquivalence Λ T
  let es := derivedEquivalence Λ' T
  let ep := ed.prod ed
  let i : ep.functor ⋙ (tensor Λ T ⋙ c.model.T) ≅
      ep.functor ⋙ ((c.model.T.prod c.model.T) ⋙ tensor Λ' T) :=
    Functor.isoWhiskerRight (tensorComparison Λ T).symm c.model.T ≪≫
      Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft (Functor.uncurry.obj (CondensedRing.derivedTensor Λ T))
        c.derived.symm ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight b es.functor ≪≫
      Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft ((D a T).prod (D a T)) (tensorComparison Λ' T) ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (NatIso.prod c.derived c.derived) (tensor Λ' T)
  let ff :=
    (ep.congrLeft :
      (_ ⥤ DerivedCategory (modules Λ' T)) ≌
        (_ ⥤ DerivedCategory (modules Λ' T))).fullyFaithfulInverse
  let barB := ff.preimageIso i
  refine ⟨barB, ?_⟩
  intro M N
  have h := congrArg (fun t ↦ t.app (M, N)) (ff.map_preimage i.hom)
  change barB.hom.app (ed.functor.obj M, ed.functor.obj N) = i.hom.app (M, N) at h
  erw [h]
  dsimp only [i, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom,
    Functor.whiskerRight_app, Functor.whiskerLeft_app, NatIso.prod, NatTrans.prod,
    Functor.associator_hom_app, Functor.associator_inv_app]
  simp only [Category.assoc, ← Functor.map_comp_assoc, Iso.hom_inv_id_app,
    Category.id_comp, ← Functor.map_comp, prod_comp, ← prod_id]
  erw [CategoryTheory.Functor.map_id, Category.id_comp, Iso.hom_inv_id_app_assoc,
    CategoryTheory.Functor.map_id, Category.comp_id]
  rfl

end AlgebraicGeometry.ProEtale.QuotientSectionTensor
