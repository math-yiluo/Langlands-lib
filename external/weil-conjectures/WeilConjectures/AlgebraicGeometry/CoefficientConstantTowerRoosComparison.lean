/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.CoefficientRingedSequenceSite
public import WeilConjectures.CategoryTheory.StrictRoosModel
import WeilConjectures.AlgebraicGeometry.IntegralOperationsWellDefined
import all WeilConjectures.CategoryTheory.StrictRoosDerivation
import all WeilConjectures.CategoryTheory.StrictRoosDerivedLimitComparison

set_option linter.privateModule false

/-! # Projection-normalized Roos comparison for completed coefficient towers

Source: Stacks 0941 and the strict Roos comparison.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 4096
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
universe u v w g t
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
namespace CategoryTheory
variable {B : Type u} [Category.{v} B] [Abelian B]
  [HasCountableProducts B] [HasLimitsOfShape ℕᵒᵖ B]
  [HasExactLimitsOfShape (Discrete ℕ) B] [EnoughInjectives B]
  [HasDerivedCategory.{w} B] [HasDerivedCategory (ℕᵒᵖ ⥤ B)]
  [IsGrothendieckAbelian.{g} (ℕᵒᵖ ⥤ B)]

private theorem normalizedRoosIso
    (RF : DerivedCategory (ℕᵒᵖ ⥤ B) ⥤ DerivedCategory B)
    (η : roosLimitFunctor ⋙ DerivedCategory.Q ⟶ DerivedCategory.Q ⋙ RF)
    (hI : ∀ I : CochainComplex (ℕᵒᵖ ⥤ B) ℤ, I.IsKInjective → IsIso (η.app I)) :
    ∃ e : roosF ⋙ DerivedCategory.Q ≅ DerivedCategory.Q ⋙ RF,
      Functor.whiskerRight roosInclusion DerivedCategory.Q ≫ e.hom = η := by
  let F := CochainComplex.kInjectiveResolutionFunctor.{g} (ℕᵒᵖ ⥤ B)
  let q := CochainComplex.toKInjectiveResolution.{g} (ℕᵒᵖ ⥤ B)
  let α := Functor.whiskerRight q (roosF ⋙ DerivedCategory.Q)
  have hi (X : CochainComplex (ℕᵒᵖ ⥤ B) ℤ) : IsIso (α.app X) := by
    have : QuasiIso (q.app X) :=
      (CochainComplex.monoQuasiIso_toKInjectiveResolution_app.{g} (ℕᵒᵖ ⥤ B) X).2
    have : QuasiIso (roosF.map (q.app X)) := roos_map_quasiIso (q.app X)
    exact (DerivedCategory.isIso_Q_map_iff_quasiIso B _).2 inferInstance
  have : IsIso α := NatIso.isIso_of_isIso_app _
  let β := Functor.whiskerLeft F (Functor.whiskerRight roosInclusion DerivedCategory.Q)
  have (X : CochainComplex (ℕᵒᵖ ⥤ B) ℤ) : IsIso (β.app X) := by
    have : QuasiIso (roosInclusion.app (F.obj X)) := roos_inclusion_quasiIso _
    exact (DerivedCategory.isIso_Q_map_iff_quasiIso B _).2 inferInstance
  have : IsIso β := NatIso.isIso_of_isIso_app _
  let δ := Functor.whiskerRight q DerivedCategory.Q
  have (X : CochainComplex (ℕᵒᵖ ⥤ B) ℤ) : IsIso (δ.app X) := by
    have : QuasiIso (q.app X) :=
      (CochainComplex.monoQuasiIso_toKInjectiveResolution_app.{g} (ℕᵒᵖ ⥤ B) X).2
    exact (DerivedCategory.isIso_Q_map_iff_quasiIso (ℕᵒᵖ ⥤ B) _).2 inferInstance
  have : IsIso δ := NatIso.isIso_of_isIso_app _
  let ε := Functor.whiskerLeft F η
  have (X : CochainComplex (ℕᵒᵖ ⥤ B) ℤ) : IsIso (ε.app X) := hI _ inferInstance
  have : IsIso ε := NatIso.isIso_of_isIso_app _
  let γ : F ⋙ roosLimitFunctor ⋙ DerivedCategory.Q ≅ DerivedCategory.Q ⋙ RF :=
    asIso ε ≪≫ (Functor.associator F DerivedCategory.Q RF).symm ≪≫
      Functor.isoWhiskerRight (asIso δ).symm RF
  let e : roosF ⋙ DerivedCategory.Q ≅ DerivedCategory.Q ⋙ RF :=
    asIso α ≪≫ (Functor.associator F roosF DerivedCategory.Q) ≪≫
      (asIso β).symm ≪≫ γ
  refine ⟨e, ?_⟩
  apply NatTrans.ext
  funext X
  change DerivedCategory.Q.map (roosInclusion.app X) ≫ e.hom.app X = η.app X
  have hq : IsIso (DerivedCategory.Q.map (q.app X)) := inferInstanceAs (IsIso (δ.app X))
  have hc : IsIso (DerivedCategory.Q.map (roosInclusion.app (F.obj X))) :=
    inferInstanceAs (IsIso (β.app X))
  dsimp only [e, γ, α, β, δ, ε, Iso.trans_hom, Iso.symm_hom, asIso_hom,
    asIso_inv, NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Functor.associator_hom_app, Functor.associator_inv_app, Functor.isoWhiskerRight_hom]
  simp only [Functor.comp_map, NatIso.isIso_inv_app, Functor.whiskerLeft_app,
    Functor.whiskerRight_app, Category.id_comp]
  erw [Category.id_comp]
  change DerivedCategory.Q.map (roosInclusion.app X) ≫
    DerivedCategory.Q.map (roosF.map (q.app X)) ≫
      inv (DerivedCategory.Q.map (roosInclusion.app (F.obj X))) ≫
        η.app (F.obj X) ≫ RF.map (inv (DerivedCategory.Q.map (q.app X))) = _
  rw [← DerivedCategory.Q.map_comp_assoc, ← roosInclusion.naturality,
    DerivedCategory.Q.map_comp, Category.assoc, IsIso.hom_inv_id_assoc]
  have hn := η.naturality (q.app X)
  dsimp only [Functor.comp_map] at hn
  rw [← Category.assoc, hn, Category.assoc]
  rw [← RF.map_comp, IsIso.hom_inv_id, RF.map_id]
  exact Category.comp_id _

end CategoryTheory

namespace WeilConjectures

end WeilConjectures
