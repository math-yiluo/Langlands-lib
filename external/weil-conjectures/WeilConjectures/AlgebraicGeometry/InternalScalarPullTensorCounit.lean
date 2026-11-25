/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.IntegralResidueOrdinaryTensorSquare
public import WeilConjectures.AlgebraicGeometry.InternalScalarTensorPullModels
import all WeilConjectures.AlgebraicGeometry.CanonicalCoefficientTensorNormalization
import all WeilConjectures.AlgebraicGeometry.IntegralResidueTensorPullCounitCore
import WeilConjectures.AlgebraicGeometry.InternalScalarRegularPullCounit

/-! # The normalized tensor presentation and scalar pullback model target -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
attribute [local irreducible] AlgebraicGeometry.ProEtale.upperStarFromPoint
  CategoryTheory.Functor.leftDerivedFunctor CategoryTheory.Functor.mapDerivedCategory
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale.QuotientChange
variable {Λ Λ' : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
  [MonObj Λ] [IsCommMonObj Λ] [MonObj Λ'] [IsCommMonObj Λ']

set_option allowUnsafeReducibility true
attribute [local reducible] D L CondensedRing.moduleObjectDerivedPullback

private theorem cochain_tensor_comparison_isIso
    {T : Scheme.{u}} (P Q : CochainComplex (Modules Λ T) ℤ)
    (hP : (HomotopyCategory.quasiIso (Modules Λ T) (.up ℤ)).kFlat
      ((HomotopyCategory.quotient _ _).obj P)) :
    IsIso (Functor.LaxMonoidal.μ DerivedCategory.Q P Q) := by
  have := DerivedCategory.isLeftDerivedFunctor₂CurriedTensor (Modules Λ T)
  have hder := MorphismProperty.kFlat_prod_id_derives_curriedTensor
    (HomotopyCategory.quasiIso (Modules Λ T) (.up ℤ)) DerivedCategory.Qh
  have : IsIso (Functor.LaxMonoidal.μ DerivedCategory.Qh
      ((HomotopyCategory.quotient _ _).obj P)
      ((HomotopyCategory.quotient _ _).obj Q)) :=
    hder.isIso_of_isLeftDerivabilityStructure
        (LF := curriedTensor (DerivedCategory (Modules Λ T)))
        (Functor.LaxMonoidal.μNatTrans DerivedCategory.Qh)
        ⟨(HomotopyCategory.quotient _ _).obj P, hP⟩
        ((HomotopyCategory.quotient _ _).obj Q)
  have he : Functor.LaxMonoidal.μ DerivedCategory.Q P Q =
      Functor.LaxMonoidal.μ DerivedCategory.Qh
        ((HomotopyCategory.quotient _ _).obj P)
        ((HomotopyCategory.quotient _ _).obj Q) := by
    change (𝟙 (DerivedCategory.Q.obj P) ⊗ₘ 𝟙 (DerivedCategory.Q.obj Q)) ≫
      (Functor.LaxMonoidal.μ DerivedCategory.Qh
        ((HomotopyCategory.quotient _ _).obj P)
        ((HomotopyCategory.quotient _ _).obj Q) ≫
        (DerivedCategory.Qh (C := Modules Λ T)).map
          (𝟙 ((HomotopyCategory.quotient _ _).obj (P ⊗ Q)))) ≫ 𝟙 _ = _
    simp only [id_tensorHom_id, Category.comp_id, Category.id_comp]
    erw [DerivedCategory.Qh.map_id, Category.comp_id]
  rwa [he]

private theorem tensor_normalization_unique (a : Λ ⟶ Λ') [IsMonHom a]
    (T : Scheme.{u}) (t : TensorNormalization a T) (ht : TensorNormalized a T t) :
    t.derived.hom = (canonicalCoefficientTensorNormalization a T).derived.hom := by
  let t₀ := canonicalCoefficientTensorNormalization a T
  have ht₀ := (canonicalCoefficientTensorNormalization_normalized a).1 T
  have ho : t.ordinary = t₀.ordinary := by
    apply Iso.ext
    apply NatTrans.ext
    funext M
    apply Mod.hom_ext
    exact (t.ordinary_hom M).trans (t₀.ordinary_hom M).symm
  apply NatTrans.ext
  funext M
  obtain ⟨P, hP, ⟨e⟩⟩ := DerivedCategory.exists_kFlat_iso M
  have h : t.derived.hom.app (DerivedCategory.Qh.obj P) =
      t₀.derived.hom.app (DerivedCategory.Qh.obj P) := by
    obtain ⟨P, rfl⟩ := HomotopyCategory.quotient_obj_surjective P
    have := cochain_tensor_comparison_isIso P
      ((CochainComplex.singleFunctor _ 0).obj (B₀ a T)) hP
    apply (cancel_mono (Functor.LaxMonoidal.μ DerivedCategory.Q P
      ((CochainComplex.singleFunctor _ 0).obj (B₀ a T)) ≫
      DerivedCategory.Q.map (singleTensor a T P).hom)).mp
    erw [ht P, ht₀ P, ho]
  have hn := t.derived.hom.naturality e.hom
  rw [h, ← t₀.derived.hom.naturality e.hom] at hn
  exact (cancel_epi ((D a T ⋙ V a T).map e.hom)).mp hn

-- The comparison traverses several derived functors and tensor normalizations.
/-- Normalize the X tensor presentation followed by the tensor-model target.

Source: Stacks 06YY, 0G7E, 07A6; integral proper-base-change proof (1), (3),
first step of the scalar-route normalization.
(auxiliary; not a blueprint node).

Proof. Naturality of the normalized tensor presentation moves the exact pullback
computation counit to its input. On a cochain representative apply TensorNormalized,
using the ordinary_hom field to identify the balanced scalar tensor presentation.
Equivalently, compare this presentation with Mod.residueDerivedTensorIso on a
K-flat resolution, where the localization tensor comparison is invertible, then
extend the equality to arbitrary objects by naturality. Apply the defining
counit identity of derivedTensorPresentationIso. The coefficient comparison
scalarTensorRegularPullIso is the exact single-object pullback comparison of
the restricted regular module: expand its restriction/pullback factors and use
the exact singleFunctor comparison; the ordinary pullback unit agrees with the
transported unit by the balanced coprojection formula. Naturality of the braiding
then cancels the coefficient comparison against its inverse in the model target.
What remains is the restricted X scalar counit, the exact restriction factor,
and the ordinary balanced presentation followed by eH inverse on the coefficient.
No tensor localization comparison at the arbitrary P is cancelled. -/
theorem scalar_pull_tensor_counit (a : Λ ⟶ Λ') [IsMonHom a]
    {X Y : Scheme.{u}} (f : X ⟶ Y) (tX : TensorNormalization a X)
    (hX : TensorNormalized a X tX)
    (P : HomotopyCategory (Modules Λ Y) (.up ℤ)) :
    let F := CondensedRing.upperStar Λ f
    let FP := (F.mapHomotopyCategory (.up ℤ)).obj P
    let e := CondensedRing.residueOrdinaryRestrictedRegularPullIso Λ Λ' a f
    let eH := (F.mapHomotopyCategoryFactors (.up ℤ)).app
        ((CochainComplex.singleFunctor _ 0).obj (B₀ a Y)) ≪≫
      (HomotopyCategory.quotient _ (.up ℤ)).mapIso
        ((F.mapCochainComplexSingleFunctor 0).app (B₀ a Y) ≪≫
          (HomologicalComplex.single _ (.up ℤ) 0).mapIso e)
    tX.derived.hom.app ((L Λ f).obj (DerivedCategory.Qh.obj P)) ≫
        scalarTensorPullModelTarget a f P =
      (V a X).map ((D a X).map ((pullCounit (Λ := Λ) f).app P)) ≫
        (V a X).map ((scalarCounit a X).app FP) ≫
        (V₀ a X).mapDerivedCategoryFactorsh.hom.app
          (((extension a X).mapHomotopyCategory (.up ℤ)).obj FP) ≫
        DerivedCategory.Qh.map
          ((Mod.tensorPresentationHomotopyIso (coefficientMap a X)).hom.app FP ≫
            (homotopyTensorSingleIso (B₀ a X)).inv.app FP ≫ eH.inv ▷ FP) := by
  rw [tensor_normalization_unique a X tX hX]
  dsimp only
  let : SymmetricCategory (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) :=
    { toBraidedCategory := sheafBraidedCategory Ab.{u + 1} X
      symmetry := fun M N ↦ @SymmetricCategory.symmetry _ _ _
        (sheafSymmetricCategory X) M N }
  let ε := Mod.tensorPresentationDerivedCounit (coefficientMap a X)
  let := Mod.tensorPresentationDerivedCounit_isLeftDerivedFunctor (coefficientMap a X)
  have hc := scalar_regular_pull_counit a f
  dsimp only at hc
  have h := tensorPullCounit_fac (CondensedRing.upperStar Λ f) (L Λ f)
    (pullCounit (Λ := Λ) f) (B₀ a Y) (B₀ a X) (scalarTensorRegularPullIso a f)
    (((CondensedRing.upperStar Λ f).mapHomotopyCategoryFactors (.up ℤ)).app
        ((CochainComplex.singleFunctor _ 0).obj (B₀ a Y)) ≪≫
      (HomotopyCategory.quotient _ (.up ℤ)).mapIso
        (((CondensedRing.upperStar Λ f).mapCochainComplexSingleFunctor 0).app (B₀ a Y) ≪≫
          (HomologicalComplex.single _ (.up ℤ) 0).mapIso
            (CondensedRing.residueOrdinaryRestrictedRegularPullIso Λ Λ' a f)))
    hc ((extension a X).leftDerivedFunctor ⋙ (V₀ a X).mapDerivedCategory) ε P
  unfold scalarTensorPullModelTarget
  unfold canonicalCoefficientTensorNormalization Mod.residueDerivedTensorIso
  dsimp only [id]
  simp only [Functor.mapIso_hom, Functor.flip_map_app, curriedTensor_obj_map,
    Iso.symm_hom] at h
  erw [h]
  erw [CategoryTheory.tensorPresentation_app (coefficientMap a X)
    (((CondensedRing.upperStar Λ f).mapHomotopyCategory (.up ℤ)).obj P)]
  simp only [Functor.comp_map, Functor.map_comp, Category.assoc]
  rfl

end AlgebraicGeometry.ProEtale.QuotientChange
