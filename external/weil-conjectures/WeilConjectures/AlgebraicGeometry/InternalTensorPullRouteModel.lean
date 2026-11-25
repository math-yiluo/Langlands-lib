/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import Mathlib.Algebra.Homology.Localization
import all Mathlib.Algebra.Homology.Localization
public import WeilConjectures.AlgebraicGeometry.InternalScalarTensorPullModels
import WeilConjectures.AlgebraicGeometry.InternalCanonicalTensorPullRouteModel

/-! # The tensor route in the common tensor model

Source: Stacks 06YY, 0G7E; integral proper-base-change proof (1), (3).
(auxiliary; not a blueprint node). -/

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
attribute [local reducible] L CondensedRing.moduleObjectDerivedPullback

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

/-- The tensor route computes the same ordinary tensorator model.

Source: Stacks 06YY, 0G7E; integral proper-base-change proof (1), (3), step 2
of the tensor-pull normalization argument.
(auxiliary; not a blueprint node).

Proof. The prescribed `ordinary_hom` fixes the ordinary tensor presentation
uniquely. Compare `TensorNormalized` for the given presentation and for the
canonical presentation on a K-flat cochain complex. The localization tensor
comparison is invertible when its first factor is K-flat, and the single-tensor
comparison is an isomorphism, so cancellation proves equality of the two
derived hom components on these representatives. Naturality along an
isomorphism from a K-flat representative to each arbitrary derived object
proves equality everywhere. Rewrite by this uniqueness equality and apply
`canonical_tensor_pull_route_model`. No flatness of the coefficient is used. -/
theorem tensor_pull_route_model (a : Λ ⟶ Λ') [IsMonHom a]
    {X Y : Scheme.{u}} (f : X ⟶ Y) (tY : TensorNormalization a Y)
    (hY : TensorNormalized a Y tY)
    (P : HomotopyCategory (Modules Λ Y) (.up ℤ)) :
    (L Λ f).map (tY.derived.hom.app (DerivedCategory.Qh.obj P)) ≫
        ((CondensedRing.leftDerivedUpperStarTensor Λ f).app
          (DerivedCategory.Qh.obj P)).app (B a Y) ≫
        ((L Λ f).obj (DerivedCategory.Qh.obj P) ◁ (scalarTensorRegularPullIso a f).hom) ≫
        scalarTensorPullModelTarget a f P = scalarTensorPullModelMap a f P := by
  rw [tensor_normalization_unique a Y tY hY]
  exact canonical_tensor_pull_route_model a f P

end AlgebraicGeometry.ProEtale.QuotientChange
