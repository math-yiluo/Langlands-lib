/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.QuotientSectionTensor.QuotientScalarTensorCanonical
import all WeilConjectures.AlgebraicGeometry.QuotientSectionTensor.QuotientScalarTensorCanonical
import WeilConjectures.AlgebraicGeometry.IntegralResidueDerivedMonoidal

/-! # Uniqueness of normalized scalar tensors

## References

* Stacks 07A4, 06YS
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u v w
open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped CategoryTheory.Obj
private theorem natTrans_ext_flat
    {C D : Type*} [Category.{v} C] [Abelian C] [IsGrothendieckAbelian.{v} C]
    [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalClosed C] [BraidedCategory C]
    [Abelian.HasFunctorialFlatResolution C] [HasDerivedCategory.{v} C] [Category.{w} D]
    {F G : DerivedCategory C × DerivedCategory C ⥤ D} (α β : F ⟶ G)
    (h : ∀ P Q : CochainComplex C ℤ,
      (HomologicalComplex.quasiIso C (.up ℤ)).kFlat P →
      (HomologicalComplex.quasiIso C (.up ℤ)).kFlat Q →
      (∀ i : ℤ, ObjectProperty.flat (P.X i)) →
      (∀ i : ℤ, ObjectProperty.flat (Q.X i)) →
      α.app (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q) =
        β.app (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q)) : α = β := by
  ext ⟨U, V⟩
  obtain ⟨P, p, hp, hPflat, hP⟩ :=
    CochainComplex.exists_quasiIso_flat_kFlat (DerivedCategory.Q.objPreimage U)
  obtain ⟨Q, q, hq, hQflat, hQ⟩ :=
    CochainComplex.exists_quasiIso_flat_kFlat (DerivedCategory.Q.objPreimage V)
  have := hp
  have := hq
  let eP := asIso (DerivedCategory.Q.map p) ≪≫ DerivedCategory.Q.objObjPreimageIso U
  let eQ := asIso (DerivedCategory.Q.map q) ≪≫ DerivedCategory.Q.objObjPreimageIso V
  apply (cancel_epi (F.mapIso (eP.prod eQ)).hom).1
  change F.map (Prod.mkHom eP.hom eQ.hom) ≫ α.app (U, V) =
    F.map (Prod.mkHom eP.hom eQ.hom) ≫ β.app (U, V)
  rw [α.naturality, β.naturality, h P Q hP hQ hPflat hQflat]

set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

attribute [local irreducible] CategoryTheory.Functor.leftDerivedFunctor
  CategoryTheory.Functor.mapDerivedCategory
  DerivedCategory.monoidalClosed CategoryTheory.Mod.monoidalClosed
  AlgebraicGeometry.ProEtale.upperStarFromPoint
  CategoryTheory.Sheaf.monoidalCategory
  DerivedCategory.monoidalCategoryOfMonoidalClosedBraidedCategory

attribute [local instance] AlgebraicGeometry.ProEtale.CondensedRing.projectionDerivedMonoidal
  AlgebraicGeometry.ProEtale.CondensedRing.projectionModuleAbelian
  AlgebraicGeometry.ProEtale.CondensedRing.projectionModuleMonoidal
  AlgebraicGeometry.ProEtale.CondensedRing.projectionModuleHasDerived
  AlgebraicGeometry.ProEtale.CondensedRing.projectionSheafMonoidal
  AlgebraicGeometry.ProEtale.CondensedRing.projectionCoefficientMonObj
  AlgebraicGeometry.ProEtale.CondensedRing.projectionModuleCategory

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open scoped CategoryTheory.Obj ChangeOfRings

namespace AlgebraicGeometry.ProEtale.QuotientSectionTensor

open QuotientChange IntegralQuotient

variable {Λ Λ' : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
  [MonObj Λ] [IsCommMonObj Λ] [MonObj Λ'] [IsCommMonObj Λ']
  (a : Λ ⟶ Λ') [IsMonHom a]

open ModuleRingedComparison

/-- The fixed scalar localization comparison is invertible on K-flat complexes. -/
theorem scalar_compute_isIso (T : Scheme.{u}) (A : CochainComplex (Modules Λ T) ℤ)
    (hA : (HomologicalComplex.quasiIso _ (.up ℤ)).kFlat A) :
    IsIso (compute a T A) := by
  let := scalarModuleClosed Λ T
  let := scalarModuleClosed Λ' T
  let := scalarModuleBraided Λ T
  let := scalarModuleBraided Λ' T
  have := scalarModuleFlat Λ T
  have := scalarModuleFlat Λ' T
  have := scalarPreservesKFlat a T
  unfold compute
  apply IsIso.comp_isIso'
  · exact Functor.map_isIso _ _
  · apply IsIso.comp_isIso'
    · unfold scalarCounit D
      exact (extension a T).isIso_leftDerivedFunctorCounit_app_of_kFlat A hA
    · apply IsIso.comp_isIso'
      · exact Functor.map_isIso _ _
      · infer_instance

/-- Flat-term K-flat normalization determines the tensor comparison uniquely. -/
theorem normalized_tensor_eq_canonical (T : Scheme.{u}) (b : TensorIso a T)
    (hb : TensorNormalized a T b) : b = canonicalTensor a T := by
  let := scalarModuleFlat Λ T
  let := scalarModuleClosed Λ T
  let := scalarModuleBraided Λ T
  have := scalarPreservesKFlat a T
  let : (DerivedCategory.Q (C := Modules Λ T)).LaxMonoidal := Mod.laxMonoidalQ
  let : (DerivedCategory.Q (C := Modules Λ' T)).LaxMonoidal := Mod.laxMonoidalQ
  apply Iso.ext
  apply natTrans_ext_flat
  intro P Q hP hQ hPflat hQflat
  have h := hb P Q hP hQ hPflat hQflat
  have hc := canonicalTensor_normalized a T P Q hP hQ hPflat hQflat
  have hcomp := scalar_compute_isIso a T
  let := scalarModuleClosed Λ T
  let := scalarModuleClosed Λ' T
  let := scalarModuleBraided Λ T
  let := scalarModuleBraided Λ' T
  let := scalarModuleFlat Λ T
  let := scalarModuleFlat Λ' T
  have := scalarPreservesKFlat a T
  let := CondensedRing.internalScalarMonoidal a T
  have hPQ : (HomologicalComplex.quasiIso _ (.up ℤ)).kFlat (P ⊗ Q) :=
    (HomologicalComplex.quasiIso _ (.up ℤ)).kFlat.prop_tensor hP hQ
  have := hcomp (P ⊗ Q) hPQ
  have hμ : IsIso (Functor.LaxMonoidal.μ DerivedCategory.Q P Q) := by
    erw [tensorator_Q_strict]
    exact Functor.isIso_μNatTrans_Qh_app_app_of_kFlat _ _
      ((HomotopyCategory.kFlat_quotient_obj_iff Q).2 hQ)
  have ht : IsIso (totalScalar a T P Q) := by
    unfold totalScalar
    change IsIso (((Functor.OplaxMonoidal.mapHomologicalComplexδNatTrans
      (.up ℤ) (extension a T)).app P).app Q)
    infer_instance
  have : IsIso (b.hom.app (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q)) := by
    infer_instance
  have hpost : IsIso
      (b.hom.app (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q) ≫
        (compute a T P ⊗ₘ compute a T Q) ≫
        Functor.LaxMonoidal.μ DerivedCategory.Q
          (((extension a T).mapHomologicalComplex (.up ℤ)).obj P)
          (((extension a T).mapHomologicalComplex (.up ℤ)).obj Q)) := by
    erw [h]
    have hm : IsIso ((D a T).map (Functor.LaxMonoidal.μ DerivedCategory.Q P Q)) :=
      @Functor.map_isIso _ _ _ _ _ _ (D a T) _ hμ
    exact IsIso.comp_isIso' hm (IsIso.comp_isIso' (hcomp (P ⊗ Q) hPQ)
      (Functor.map_isIso DerivedCategory.Q (totalScalar a T P Q)))
  have hp := (isIso_comp_left_iff _ _).1 hpost
  let e := @asIso _ _ _ _ _ hp
  have h' : b.hom.app (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q) ≫ e.hom =
      (canonicalTensor a T).hom.app (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q) ≫
        e.hom := h.trans hc.symm
  have h'' := congrArg (fun q ↦ q ≫ e.inv) h'
  simpa only [Category.assoc, e.hom_inv_id, Category.comp_id] using h''

/-- The normalized scalar tensorator exists uniquely, pointwise in the scheme. -/
theorem scalar_tensor_exists_unique (T : Scheme.{u}) :
    ∃! b : TensorIso a T, TensorNormalized a T b :=
  ⟨canonicalTensor a T, canonicalTensor_normalized a T,
    fun b hb ↦ normalized_tensor_eq_canonical a T b hb⟩

end AlgebraicGeometry.ProEtale.QuotientSectionTensor
