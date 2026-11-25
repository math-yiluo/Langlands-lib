/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.EtaleTorAmplitude
import WeilConjectures.CategoryTheory.DerivedCategory.FlatModel
import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.FlatResolution
import WeilConjectures.FromJoel.Algebra.Homology.Embedding.CochainComplexTrunc
import Mathlib.Algebra.Homology.ShortComplex.FunctorEquivalence
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Colim
import WeilConjectures.Mathlib.Algebra.Homology.ShortComplex.Exact
import WeilConjectures.FromJoel.Algebra.Homology.BifunctorColimits
import WeilConjectures.SixFunctors.Etale.Derived.Tensor

/-!
# Connectivity of the derived tensor product

Source: `literature/blueprint/master/blueprint/sec-smooth-purity/
sk-prop-sf-kunneth-ordinary/lem-kun-derived-tensor-t-est.md`, node
`lem-kun-derived-tensor-t-est`; Stacks Project, Tag 0F1J, first reduction paragraph,
using Tag 0F1M and the lower truncation of Tag 0118.

The first factor has Tor amplitude in `[a, ∞)`, and the second factor has no
cohomology below `b`. We use bounded dévissage for each canonical upper truncation
of the second factor. An unrestricted categorical K-flat model of the first factor
computes every tensor product. The upper truncations have colimit the original
complex, tensoring preserves this colimit, and exact filtered colimits preserve
exactness at each degree below `a + b`. Thus no comparison between the independent
coefficient K-flat predicate and categorical K-flatness is needed.

The finite dévissage is the existing `DerivedCategory.isGE_obj_of_isGE` from
`WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.TStructure`.
The exact-colimit step is proved below from Mathlib's `colim.exact_mapShortComplex`.
-/

@[expose] public section

set_option autoImplicit false

universe u v

open CategoryTheory CategoryTheory.Limits MonoidalCategory

namespace AlgebraicGeometry.Etale

private theorem exactAt_colimit
    {C : Type*} [Category* C] [Abelian C]
    [HasColimitsOfShape ℤ C] [HasExactColimitsOfShape ℤ C]
    (K : ℤ ⥤ CochainComplex C ℤ) (c : Cocone K) (hc : IsColimit c)
    (i : ℤ) (hK : ∀ n, (K.obj n).ExactAt i) : c.pt.ExactAt i := by
  let S := (ShortComplex.functorEquivalence ℤ C).inverse.obj
    (K ⋙ HomologicalComplex.shortComplexFunctor' C (.up ℤ) (i - 1) i (i + 1))
  have hS : S.Exact := (ShortComplex.exact_iff_evaluation S).2 fun n ↦
    (HomologicalComplex.exactAt_iff' (K.obj n) (i - 1) i (i + 1)
      (by simp) (by simp)).1 (hK n)
  have he (j : ℤ) := isColimitOfPreserves (HomologicalComplex.eval C (.up ℤ) j) hc
  rw [HomologicalComplex.exactAt_iff' c.pt (i - 1) i (i + 1) (by simp) (by simp)]
  exact colim.exact_mapShortComplex (S := S) hS
    (hc₁ := he (i - 1)) (hc₂ := he i) (hc₃ := he (i + 1))
    (c.pt.d (i - 1) i) (c.pt.d i (i + 1))
    (fun n ↦ (c.ι.app n).comm (i - 1) i)
    (fun n ↦ (c.ι.app n).comm i (i + 1))

private theorem exactAt_of_filtration
    {C : Type*} [Category* C] [Abelian C]
    [HasColimitsOfShape ℤ C] [HasExactColimitsOfShape ℤ C]
    (F : CochainComplex C ℤ ⥤ CochainComplex C ℤ)
    [PreservesColimitsOfShape ℤ F] (L : CochainComplex C ℤ) (i : ℤ)
    (h : ∀ n, (F.obj (L.truncLE n)).ExactAt i) : (F.obj L).ExactAt i := by
  exact exactAt_colimit (L.filtrationLE ⋙ F)
    (F.mapCocone L.filtrationLECocone)
    (isColimitOfPreserves F L.isColimitFiltrationLECocone) i h

private theorem tensor_isGE_of_single
    {C : Type*} [Category.{v} C] [Abelian C] [IsGrothendieckAbelian.{v} C]
    [MonoidalCategory C] [MonoidalPreadditive C] [BraidedCategory C] [MonoidalClosed C]
    [Abelian.HasFunctorialFlatResolution C] [HasDerivedCategory.{v} C]
    [HasColimitsOfSize.{0, 0} C]
    (A B : _root_.DerivedCategory C) (a b : ℤ)
    (hsingle : ∀ M : C,
      (((curriedTensor (_root_.DerivedCategory C)).obj A).obj
        ((_root_.DerivedCategory.singleFunctor C 0).obj M)).IsGE a)
    [B.IsGE b] : (A ⊗ B).IsGE (b + a) := by
  classical
  have (X₁ X₂ : GradedObject ℤ C) : X₁.HasTensor X₂ := fun j ↦ by
    let : HasColimitsOfShape (Discrete ((fun x : ℤ × ℤ ↦ x.1 + x.2) ⁻¹' {j})) C :=
      HasColimitsOfSize.has_colimits_of_shape _
    exact HasColimitsOfShape.has_colimit _
  have (K₁ K₂ : CochainComplex C ℤ) :
      HomologicalComplex.HasMapBifunctor K₁ K₂ (curriedTensor C) (.up ℤ) :=
    inferInstanceAs (GradedObject.HasTensor K₁.X K₂.X)
  let : ((curriedTensor (_root_.DerivedCategory C)).obj A).CommShift ℤ :=
    _root_.DerivedCategory.commShiftTensorLeft C A
  have : ((curriedTensor (_root_.DerivedCategory C)).obj A).IsTriangulated :=
    _root_.DerivedCategory.isTriangulated_tensorLeft C A
  obtain ⟨P, π, hπ, _hflat, hPk⟩ :=
    CochainComplex.exists_quasiIso_flat_kFlat (_root_.DerivedCategory.Q.objPreimage A)
  have : IsIso (_root_.DerivedCategory.Q.map π) :=
    (_root_.DerivedCategory.isIso_Q_map_iff_quasiIso C π).2 hπ
  let eA : _root_.DerivedCategory.Q.obj P ≅ A :=
    asIso (_root_.DerivedCategory.Q.map π) ≪≫
      _root_.DerivedCategory.Q.objObjPreimageIso A
  obtain ⟨L, _, ⟨eB⟩⟩ := B.exists_iso_Q_obj_of_isGE b
  apply (_root_.DerivedCategory.isGE_iff _ (b + a)).2
  intro i hi
  have hbounded (n : ℤ) : (P ⊗ L.truncLE n).ExactAt i := by
    have : (L.truncLE n).IsGE b := by
      rw [CochainComplex.isGE_iff]
      intro j hj
      by_cases hjn : j ≤ n
      · have := L.quasiIsoAt_ιTruncLE n j hjn
        exact (exactAt_iff_of_quasiIsoAt (L.ιTruncLE n) j).2
          (CochainComplex.exactAt_of_isGE L b j hj)
      · exact CochainComplex.exactAt_of_isLE (L.truncLE n) n j (by omega)
    have : (_root_.DerivedCategory.Q.obj (L.truncLE n)).IsGE b := inferInstance
    have hbnd : _root_.DerivedCategory.TStructure.t.bounded
        (_root_.DerivedCategory.Q.obj (L.truncLE n)) :=
      ⟨⟨b, inferInstance⟩, ⟨n, inferInstance⟩⟩
    have : (A ⊗ _root_.DerivedCategory.Q.obj (L.truncLE n)).IsGE (b + a) :=
      _root_.DerivedCategory.isGE_obj_of_isGE
        ((curriedTensor (_root_.DerivedCategory C)).obj A) a hsingle
        (_root_.DerivedCategory.Q.obj (L.truncLE n)) hbnd b
    have : (_root_.DerivedCategory.Q.obj (P ⊗ L.truncLE n)).IsGE (b + a) :=
      _root_.DerivedCategory.TStructure.t.isGE_of_iso
        (tensorIso eA.symm (Iso.refl _) ≪≫
          _root_.DerivedCategory.QObjTensorQObjIsoOfKFlatLeft P (L.truncLE n) hPk) (b + a)
    have : (P ⊗ L.truncLE n).IsGE (b + a) :=
      (_root_.DerivedCategory.isGE_Q_obj_iff _ _).1 this
    exact CochainComplex.exactAt_of_isGE _ (b + a) i (by omega)
  have (X : C) : PreservesColimitsOfShape ℤ (tensorLeft X) := inferInstance
  let F : CochainComplex C ℤ ⥤ CochainComplex C ℤ :=
    ((curriedTensor C).map₂HomologicalComplex (.up ℤ) (.up ℤ) (.up ℤ)).obj P
  have : PreservesColimitsOfShape ℤ F := inferInstance
  have heq (K : CochainComplex C ℤ) : F.obj K = P ⊗ K := by rfl
  have hexF : (F.obj L).ExactAt i := exactAt_of_filtration F L i (fun n ↦ by
    rw [heq]
    exact hbounded n)
  rw [heq] at hexF
  have hex : (P ⊗ L).ExactAt i := hexF
  have eTensor : (A ⊗ B) ≅
      _root_.DerivedCategory.Q.obj (P ⊗ L) :=
    tensorIso eA.symm eB ≪≫ _root_.DerivedCategory.QObjTensorQObjIsoOfKFlatLeft P L hPk
  exact (hex.isZero_homology.of_iso
    ((_root_.DerivedCategory.homologyFunctorFactors C i).app (P ⊗ L))).of_iso
      ((_root_.DerivedCategory.homologyFunctor C i).mapIso eTensor)

private theorem etale_tensor_isGE_of_single
    (D : Type*) [Category.{u + 1} D] [Abelian D] [IsGrothendieckAbelian.{u + 1} D]
    [MonoidalCategory D] [MonoidalPreadditive D] [SymmetricCategory D]
    [MonoidalClosed D] [Abelian.HasFunctorialFlatResolution D] (T : Scheme.{u})
    (A B : _root_.DerivedCategory (Sheaf T.smallEtaleTopology D)) (a b : ℤ)
    (hsingle : ∀ M : Sheaf T.smallEtaleTopology D,
      ((((derivedTensor D T).obj A).obj
        ((_root_.DerivedCategory.singleFunctor _ 0).obj M))).IsGE a)
    [B.IsGE b] : (((derivedTensor D T).obj A).obj B).IsGE (b + a) := by
  exact tensor_isGE_of_single A B a b hsingle

/-- If `A` has Tor amplitude in `[a, ∞)` and `B` has no cohomology below `b`,
then the derived tensor `A ⊗ᴸ B` has no cohomology below `a + b`.

Source: `literature/blueprint/master/blueprint/sec-smooth-purity/
sk-prop-sf-kunneth-ordinary/lem-kun-derived-tensor-t-est.md`, node
`lem-kun-derived-tensor-t-est` (blueprint: lem-kun-derived-tensor-t-est); corrected source
proof uses the existing bounded dévissage theorem on each good upper truncation,
then the integer-indexed colimit of these truncations. A categorical K-flat model
computes the tensors before passing to this colimit. Exactness of filtered colimits
transfers the lower cohomology bound to the original second factor. This gives the
connectivity estimate used in Stacks Tag 0F1J, first reduction paragraph.
-/
theorem derivedTensor_isZero_homology_of_torAmplitudeGE
    (Λ : Type (u + 1)) [CommRing Λ] (T : Scheme.{u})
    (A B : DerivedCategoryModule Λ T) (a b : ℤ)
    (hA : DerivedCategory.hasTorAmplitudeGE Λ T a A)
    (hB : ∀ (j : ℤ), j < b →
      IsZero ((_root_.DerivedCategory.homologyFunctor
        (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ)) j).obj B))
    (i : ℤ) (hi : i < a + b) :
    IsZero ((_root_.DerivedCategory.homologyFunctor
      (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ)) i).obj
      (((derivedTensor (ModuleCat.{u + 1} Λ) T).obj A).obj B)) := by
  have : B.IsGE b := (_root_.DerivedCategory.isGE_iff B b).2 hB
  have h := etale_tensor_isGE_of_single (ModuleCat.{u + 1} Λ) T A B a b
    (fun M ↦ (_root_.DerivedCategory.isGE_iff _ a).2 (hA M))
  exact (_root_.DerivedCategory.isGE_iff _ (b + a)).1 h i (by omega)

end AlgebraicGeometry.Etale
