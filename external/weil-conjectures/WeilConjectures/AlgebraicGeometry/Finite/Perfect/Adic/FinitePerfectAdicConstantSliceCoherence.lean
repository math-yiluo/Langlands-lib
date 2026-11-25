/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Finite.Perfect.Adic.FinitePerfectAdicScalarCoherence
import all WeilConjectures.AlgebraicGeometry.Finite.Perfect.Adic.FinitePerfectAdicConstantPresentation

/-! # Fixed scalar comparisons commute with constant and slice units -/

-- After pruning, this module only keeps private declarations.
set_option linter.privateModule false


@[expose] public noncomputable section
set_option autoImplicit false
universe t
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor Opposite
attribute [local irreducible] AlgebraicGeometry.Scheme.directCoefficientMap
  AlgebraicGeometry.Scheme.overDirectMap
  AlgebraicGeometry.Scheme.directCoefficientIso AlgebraicGeometry.Scheme.overDirectIso
  AlgebraicGeometry.Scheme.constantAssociatedIso

namespace AlgebraicGeometry.Scheme
section
variable {C : Type (t + 1)} [Category.{t} C] {J : GrothendieckTopology C}
  [HasWeakSheafify J AddCommGrpCat.{t + 1}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{t + 1}]
  {B D : Type (t + 1)} [CommRing B] [CommRing D]
  {R S : Sheaf J RingCat.{t + 1}}
  (α : (Functor.const Cᵒᵖ).obj (RingCat.of B) ⟶ R.obj)
  (β : (Functor.const Cᵒᵖ).obj (RingCat.of D) ⟶ S.obj)
  [Presheaf.IsLocallyInjective J α] [Presheaf.IsLocallySurjective J α]
  [Presheaf.IsLocallyInjective J β] [Presheaf.IsLocallySurjective J β]
  (q : B →+* D) (p : R ⟶ S)
  (h : ∀ Z, α.app Z ≫ p.hom.app Z = RingCat.ofHom q ≫ β.app Z)
  (V : C)
  [HasWeakSheafify (J.over V) AddCommGrpCat.{t + 1}]
  [(J.over V).WEqualsLocallyBijective AddCommGrpCat.{t + 1}]
  [Presheaf.IsLocallyInjective (J.over V) (whiskerLeft (Over.forget V).op α)]
  [Presheaf.IsLocallySurjective (J.over V) (whiskerLeft (Over.forget V).op α)]
  [Presheaf.IsLocallyInjective (J.over V) (whiskerLeft (Over.forget V).op β)]
  [Presheaf.IsLocallySurjective (J.over V) (whiskerLeft (Over.forget V).op β)]

private lemma overDirectIso_coefficient (N : ModuleCat.{t + 1} D) :
    (directCoefficientIso (C := Over V) (J := J.over V) (R := R.over V)
        (S := S.over V) (whiskerLeft (Over.forget V).op α)
        (whiskerLeft (Over.forget V).op β) q ((J.overPullback RingCat.{t + 1} V).map p)
        (fun Z ↦ h ((Over.forget V).op.obj Z))).hom.app N ≫
      (SheafOfModules.restrictScalars ((J.overPullback RingCat.{t + 1} V).map p)).map
        ((overDirectIso β V).hom.app N) =
    (overDirectIso α V).hom.app ((ModuleCat.restrictScalars q).obj N) ≫
      (SheafOfModules.overFunctor R V).map ((directCoefficientIso α β q p h).hom.app N) := by
  erw [directCoefficientIso_hom_app, directCoefficientIso_hom_app,
    overDirectIso_hom_app, overDirectIso_hom_app]
  apply (SheafOfModules.toSheaf (R.over V)).map_injective
  simp only [Functor.map_comp]
  change (SheafOfModules.toSheaf (R.over V)).map
      (directCoefficientMap (C := Over V) (J := J.over V) (R := R.over V)
        (S := S.over V) (whiskerLeft (Over.forget V).op α)
        (whiskerLeft (Over.forget V).op β) q ((J.overPullback RingCat.{t + 1} V).map p)
        (fun Z ↦ h ((Over.forget V).op.obj Z)) N) ≫
      (SheafOfModules.toSheaf (S.over V)).map (overDirectMap β V N) =
    (SheafOfModules.toSheaf (R.over V)).map
      (overDirectMap α V ((ModuleCat.restrictScalars q).obj N)) ≫
      (J.overPullback AddCommGrpCat.{t + 1} V).map
        ((SheafOfModules.toSheaf R).map (directCoefficientMap α β q p h N))
  erw [directCoefficientMap_underlying (C := Over V) (J := J.over V)
      (R := R.over V) (S := S.over V)
      (whiskerLeft (Over.forget V).op α) (whiskerLeft (Over.forget V).op β) q
      ((J.overPullback RingCat.{t + 1} V).map p)
      (fun Z ↦ h ((Over.forget V).op.obj Z)) N,
    directCoefficientMap_underlying α β q p h N,
    CategoryTheory.Functor.map_id, Category.id_comp, Category.comp_id]
  apply Sheaf.hom_ext
  apply sheafify_hom_ext (J.over V) _ _ (((directConstant β).obj N).over V).isSheaf
  change toSheafify (J.over V) ((Functor.const (Over V)ᵒᵖ).obj (AddCommGrpCat.of N)) ≫
      (PresheafOfModules.toPresheaf _).map (overDirectMap β V N).val =
    toSheafify (J.over V) ((Functor.const (Over V)ᵒᵖ).obj (AddCommGrpCat.of N)) ≫
      (PresheafOfModules.toPresheaf _).map
        (overDirectMap α V ((ModuleCat.restrictScalars q).obj N)).val
  erw [overDirectMap_unit β V N,
    overDirectMap_unit α V ((ModuleCat.restrictScalars q).obj N)]
  rfl

end
end AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.Scheme

end AlgebraicGeometry.Scheme
