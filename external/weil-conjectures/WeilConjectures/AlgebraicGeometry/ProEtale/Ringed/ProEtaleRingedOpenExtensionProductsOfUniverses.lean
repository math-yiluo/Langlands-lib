/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.Completed.CompletedIntegralCoefficientsSupplement
public import WeilConjectures.CategoryTheory.LocalizedModuleExactForSystems
public import WeilConjectures.Algebra.Homology.SmoothPurity.LocalizedModuleExactIndependent
public import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
public import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
public import WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact

import WeilConjectures.AlgebraicGeometry.ProEtale.Closed.ProEtaleClosedAbelianProductsOfUniverses
import WeilConjectures.AlgebraicGeometry.ProEtale.Open.ProEtaleOpenClosedModuleSupportOfUniverses
import WeilConjectures.AlgebraicGeometry.ReducedInducedClosedSubscheme
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
import Mathlib.CategoryTheory.Adjunction.Triple

/-! # Open extension products with independent coefficient universes

## References

* Stacks Project, Tag 09BP
-/

@[expose] public section
set_option autoImplicit false
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_proEtTopology
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_over_proEtTopology
universe t u
open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme

private theorem open_unit_isIso
    {X : Scheme.{t}} (U : X.ProEt) [IsOpenImmersion U.hom]
    (R : Sheaf (ProEt.topology X) CommRingCat.{max u (t + 1)}) :
    IsIso (SheafOfModules.localizedSystemAdjunction.{t + 1, t, u} R U).unit := by
  let A := (sheafCompose (ProEt.topology X)
    (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})).obj R
  let b := SheafOfModules.overPushforwardOverAdj (R := A) U
  have hsub : ∀ W : X.ProEt, Subsingleton (W ⟶ U) := by
    intro W
    constructor
    intro f g
    apply MorphismProperty.Over.Hom.ext
    apply (cancel_mono U.hom).mp
    exact f.w.trans g.w.symm
  have : (Over.forget U).Full := by
    constructor
    intro V V' f
    exact ⟨Over.homMk f (@Subsingleton.elim _ (hsub V.left) _ _), rfl⟩
  have : IsIso (Over.forgetAdjStar U).unit := inferInstance
  have : IsIso b.counit := by
    rw [NatTrans.isIso_iff_isIso_app]
    intro N
    rw [← isIso_iff_of_reflects_iso _
      (SheafOfModules.forget _ ⋙ PresheafOfModules.toPresheaf _)]
    rw [NatTrans.isIso_iff_isIso_app]
    intro W
    change IsIso (N.val.presheaf.map ((Over.forgetAdjStar U).unit.app W.unop).op)
    infer_instance
  let triple : Adjunction.Triple _ _ _ :=
    ⟨SheafOfModules.localizedSystemAdjunction.{t + 1, t, u} R U, b⟩
  exact triple.isIso_unit_iff_isIso_counit.mpr inferInstance

private theorem restriction_product_comparison
    {C D : Type*} [Category* C] [Category* D]
    [HasProductsOfShape ℕ C] [HasProductsOfShape ℕ D]
    (L : C ⥤ D) (J : D ⥤ C) (adj : L ⊣ J)
    [PreservesLimitsOfShape (Discrete ℕ) J]
    (hunit : ∀ F, IsIso (adj.unit.app F)) (M : ℕ → C) :
    IsIso (J.map (piComparison L M)) := by
  let c := piComparison L M
  have he : adj.unit.app (∏ᶜ M) ≫ J.map c ≫
      piComparison J (fun n ↦ L.obj (M n)) =
      Limits.Pi.map (fun n ↦ adj.unit.app (M n)) := by
    apply Limits.Pi.hom_ext
    intro n
    simp only [Category.assoc, piComparison_comp_π, ← J.map_comp]
    dsimp [c]
    rw [piComparison_comp_π]
    exact (adj.unit.naturality (Limits.Pi.π M n)).symm.trans
      (Limits.Pi.map_π (fun n ↦ adj.unit.app (M n)) n).symm
  have hc : J.map c = inv (adj.unit.app (∏ᶜ M)) ≫
      Limits.Pi.map (fun n ↦ adj.unit.app (M n)) ≫
        inv (piComparison J (fun n ↦ L.obj (M n))) := by
    rw [← he]
    simp only [Category.assoc, IsIso.hom_inv_id, Category.comp_id]
    rw [← Category.assoc, IsIso.inv_hom_id, Category.id_comp]
  rw [hc]
  infer_instance

/-- Quasi-compact open extension commutes with countable products in every
coefficient universe containing the site. -/
theorem proEtaleRingedExtensionByZero_products_of_universes
    {X : Scheme.{t}} (U : X.ProEt) [IsOpenImmersion U.hom] [QuasiCompact U.hom]
    (R : Sheaf (ProEt.topology X) CommRingCat.{max u (t + 1)})
    (M : ℕ → ringedSiteModules.{max u (t + 1)}
      (((sheafCompose (ProEt.topology X)
        (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})).obj R).over U)) :
    IsIso (piComparison (SheafOfModules.localizedSystemExtension.{t + 1, t, u} R U) M) := by
  classical
  let A := (sheafCompose (ProEt.topology X)
    (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})).obj R
  let L := SheafOfModules.localizedSystemExtension.{t + 1, t, u} R U
  let J := SheafOfModules.localizedSystemRestriction.{t + 1, t, u} R U
  let adj := SheafOfModules.localizedSystemAdjunction.{t + 1, t, u} R U
  have : PreservesLimitsOfSize.{0, 0} J := adj.rightAdjoint_preservesLimits
  have : IsIso adj.unit := open_unit_isIso U R
  have hunit (F) : IsIso (adj.unit.app F) := by infer_instance
  let c := piComparison L M
  have hJc : IsIso (J.map c) := restriction_product_comparison L J adj hunit M
  let T : TopologicalSpace.Closeds X :=
    ⟨(Set.range U.hom)ᶜ, (IsOpenImmersion.isOpen_range U.hom).isClosed_compl⟩
  let i := (IdealSheafData.vanishingIdeal T).subschemeι
  have hi : Set.range i = (T : Set X) :=
    (IdealSheafData.reduced_induced_closed_subscheme X T).2.2.2.2.2.1
  have hU : Set.range U.hom = (Set.range i)ᶜ := by
    rw [hi]
    exact (compl_compl _).symm
  let B := Functor.sheafPullbackConstruction.sheafPullback (proEtaleBaseChange i)
    AddCommGrpCat.{max u (t + 1)} (ProEt.topology X) (ProEt.topology _)
  let I := SheafOfModules.toSheaf.{max u (t + 1)} A ⋙ B
  obtain ⟨hz, hd⟩ := proEtaleOpenClosedModuleSupportOfUniverses i U hU R
  have : PreservesLimitsOfShape (Discrete ℕ) B :=
    proEtaleClosedAbelianProductsOfUniverses i
  have : PreservesLimitsOfShape (Discrete ℕ) (SheafOfModules.toSheaf.{max u (t + 1)} A) := by
    have : PreservesLimitsOfShape (Discrete ℕ)
        (SheafOfModules.toSheaf.{max u (t + 1)} A ⋙ sheafToPresheaf _ _) :=
      show PreservesLimitsOfShape (Discrete ℕ)
        (SheafOfModules.forget A ⋙ PresheafOfModules.toPresheaf A.obj) by infer_instance
    exact preservesLimitsOfShape_of_reflects_of_preserves _ (sheafToPresheaf _ _)
  have : PreservesLimitsOfShape (Discrete ℕ) I := inferInstance
  have hIc : IsIso (I.map c) := by
    have hsrc : IsZero (I.obj (L.obj (∏ᶜ M))) := hz _
    have hprod : IsZero (∏ᶜ fun n ↦ I.obj (L.obj (M n))) := by
      apply (IsZero.iff_id_eq_zero _).2
      apply Limits.Pi.hom_ext
      intro n
      exact (hz (M n)).eq_of_tgt _ _
    have htgt : IsZero (I.obj (∏ᶜ fun n ↦ L.obj (M n))) :=
      hprod.of_iso (PreservesProduct.iso I (fun n ↦ L.obj (M n)))
    exact isIso_of_source_target_iso_zero (I.map c) hsrc.isoZero htgt.isoZero
  exact hd c hJc hIc

end AlgebraicGeometry.Scheme
