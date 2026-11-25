/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Etale.Hom.EtaleHomComparisonModels
import all WeilConjectures.AlgebraicGeometry.Etale.Hom.EtaleHomComparisonModels
import WeilConjectures.CategoryTheory.Right.RightExactTensorShiftCancellation
import WeilConjectures.CategoryTheory.Adjunction.Derived.DerivedAdjointCochainCounit

/-! # Scalar tensor comparison and cancellation of opposite shifts -/

@[expose] public section
set_option autoImplicit false
universe u v w
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated MonoidalCategory
open CategoryTheory.Pretriangulated.Opposite Opposite
namespace AlgebraicGeometry.Etale

set_option backward.defeqAttrib.useBackward true
set_option Elab.async false
-- Reuse the cached sheaf tensor structure used by the model comparison proof.
attribute [local instance 2000] scalarSheafMonoidal
attribute [local irreducible] _root_.DerivedCategory.monoidalClosed
  Functor.leftDerivedFunctor Functor.leftDerivedFunctorCounit
  _root_.DerivedCategory.instMonoidalCategory
  _root_.DerivedCategory.commShift₂CurriedTensor

-- The comparison is transferred to site notation before concrete scalar specialization.
private theorem cancellation_onSite
    (C : Type v) [Category.{u + 1} C] [Abelian C]
    [IsGrothendieckAbelian.{u + 1} C] [MonoidalCategory C] [MonoidalPreadditive C]
    [MonoidalClosed C] [SymmetricCategory C] [Abelian.HasFunctorialFlatResolution C]
    (D : Type w) [Category.{u + 1} D] [Abelian D]
    [IsGrothendieckAbelian.{u + 1} D] [MonoidalCategory D] [MonoidalPreadditive D]
    [MonoidalClosed D] [SymmetricCategory D] [Abelian.HasFunctorialFlatResolution D]
    (X : Scheme.{u})
    (E : Sheaf X.smallEtaleTopology C ⥤ Sheaf X.smallEtaleTopology D)
    (U : Sheaf X.smallEtaleTopology D ⥤ Sheaf X.smallEtaleTopology C)
    [E.Additive] [U.Additive] [E.PreservesKFlatQuasiIso]
    [PreservesFiniteLimits U] [PreservesFiniteColimits U]
    (adj : E ⊣ U) [E.PreservesFlat] [E.IsLeftAdjoint] [E.Monoidal]
    (G : _root_.DerivedCategory (Sheaf X.smallEtaleTopology C) ⥤
      _root_.DerivedCategory (Sheaf X.smallEtaleTopology D)) (ad : G ⊣ U.mapDerivedCategory)
    (r : ∀ P : CochainComplex (Sheaf X.smallEtaleTopology C) ℤ, G.obj (DerivedCategory.Q.obj P) ⟶
      DerivedCategory.Q.obj ((E.mapHomologicalComplex (.up ℤ)).obj P))
    (hr : ∀ P, r P = (ad.leftAdjointUniq
        (adj.derivedAdjunction.ofNatIsoRight U.rightDerivedFunctorIsoMapDerivedCategory)).hom.app
          (DerivedCategory.Q.obj P) ≫ E.rightExact_cochainCounit P)
    (μ : ∀ K L : _root_.DerivedCategory (Sheaf X.smallEtaleTopology C),
      ((derivedTensor D X).obj (G.obj K)).obj (G.obj L) ≅
        G.obj (((derivedTensor C X).obj K).obj L))
    (hμ : (∀ {K K'} (f : K ⟶ K') L,
        ((derivedTensor D X).map (G.map f)).app (G.obj L) ≫ (μ K' L).hom =
          (μ K L).hom ≫ G.map (((derivedTensor C X).map f).app L)) ∧
      (∀ K {L L'} (f : L ⟶ L'),
        ((derivedTensor D X).obj (G.obj K)).map (G.map f) ≫ (μ K L').hom =
          (μ K L).hom ≫ G.map (((derivedTensor C X).obj K).map f)) ∧
      EtaleHomTensorModelNormalization C D X E G r μ)
    (K L : _root_.DerivedCategory (Sheaf X.smallEtaleTopology C)) (n : ℤ) :
    letI := ad.leftAdjointCommShift ℤ
    ((derivedTensor D X).map
        ((G.commShiftIso (-n)).hom.app K)).app
          (G.obj (L⟦n⟧)) ≫
      ((derivedTensor D X).obj
        ((G.obj K)⟦-n⟧)).map
          ((G.commShiftIso n).hom.app L) ≫
      etaleHomTensorShiftCancellation D X
        (G.obj K) (G.obj L) n ≫
      (μ K L).hom =
    (μ (K⟦-n⟧) (L⟦n⟧)).hom ≫
      G.map
        (etaleHomTensorShiftCancellation C X K L n) := by
  dsimp only [derivedTensor, EtaleHomTensorModelNormalization] at hμ
  have h := Functor.rightExactTensorComparison_shiftCancellation E U adj G ad r hr μ hμ K L n
  dsimp only [derivedTensor, etaleHomTensorShiftCancellation]
  exact h

-- Specializing the derived adjunction and tensor structures requires large kernel conversions.
/-- The normalized scalar tensor comparison respects cancellation of opposite shifts.
Source: Stacks Project, Tags 06YY, 07A4 and 08JC; the tensor-balancing calculation
in the proof of `lem-coef-etale-hom-transpose-exact-comm-shift-core`.

Let E ⊣ U be sheaf scalar extension and restriction. E is additive, strong
monoidal, preserves flat objects and K-flat quasi-isomorphisms, and U is exact.
The cochain unit formula and `Adjunction.leftDerivedCochainCounit` identify the
fixed scalar representative map with the total-derived counit of E transported
along uniqueness of left adjoints. The comparison satisfies the flat-model
normalization by its defining property. Apply
`Functor.rightExactTensorComparison_shiftCancellation` (blueprint:
lem-derived-right-exact-tensor-shift-cancellation): the adjoint-mate scalar
shift and the tensor-shift cancellation are definitionally the displayed ones.
This argument involves no internal Hom or evaluation map, and requires no
flatness of B over A.
(blueprint: lem-coef-etale-scalar-tensor-shift-cancellation) -/
theorem etaleHomTensorComparison_shiftCancellation
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (X : Scheme.{u}) (φ : A →+* B) (K L : DerivedCategoryModule A X) (n : ℤ) :
    letI := etaleHomScalarCommShift X φ
    ((derivedTensor (ModuleCat.{u + 1} B) X).map
        (((scalarExtension φ X).commShiftIso (-n)).hom.app K)).app
          ((scalarExtension φ X).obj (L⟦n⟧)) ≫
      ((derivedTensor (ModuleCat.{u + 1} B) X).obj
        (((scalarExtension φ X).obj K)⟦-n⟧)).map
          (((scalarExtension φ X).commShiftIso n).hom.app L) ≫
      etaleHomTensorShiftCancellation (ModuleCat.{u + 1} B) X
        ((scalarExtension φ X).obj K) ((scalarExtension φ X).obj L) n ≫
      (etaleHomTensorComparison X φ K L).hom =
    (etaleHomTensorComparison X φ (K⟦-n⟧) (L⟦n⟧)).hom ≫
      (scalarExtension φ X).map
        (etaleHomTensorShiftCancellation (ModuleCat.{u + 1} A) X K L n) := by
  let E := ProEtale.etaleSheafExtendScalars φ X
  let U := Sheaf.restrictScalars X.smallEtaleTopology φ
  let adj : E ⊣ U := ProEtale.etaleSheafExtendScalarsAdjunction φ X
  let : E.IsLeftAdjoint := adj.isLeftAdjoint
  let : E.PreservesFlat := extension_preservesFlat φ X
  let : E.PreservesKFlatQuasiIso := extension_preservesKFlatQuasiIso φ X
  let : E.OplaxMonoidal := adj.leftAdjointOplaxMonoidal
  let : E.Monoidal := CategoryTheory.composeAndSheafifyMonoidal X.smallEtaleTopology
    (ModuleCat.extendRestrictScalarsAdj.{u + 1, u + 1, u + 1} φ)
  let ad : scalarExtension φ X ⊣ U.mapDerivedCategory := Adjunction.ofIsRightAdjoint _
  let b : E.leftDerivedFunctor ⊣ U.mapDerivedCategory :=
    adj.derivedAdjunction.ofNatIsoRight U.rightDerivedFunctorIsoMapDerivedCategory
  let e : scalarExtension φ X ≅ E.leftDerivedFunctor := ad.leftAdjointUniq b
  have hr : ∀ P, scalarExtensionRepresentative φ X P =
      e.hom.app (_root_.DerivedCategory.Q.obj P) ≫ E.rightExact_cochainCounit P := by
    intro P
    unfold scalarExtensionRepresentative
    rw [← mapComplex_unit_formula]
    dsimp only [Functor.rightExact_cochainCounit]
    have h := (Adjunction.leftDerivedCochainCounit E U adj ad P).symm
    simp only [E, U, adj, ad, e, b, Functor.id_obj,
      Iso.app_inv, Iso.app_hom] at h ⊢
    exact h
  have hμ := (etaleHomTensorComparison_existsUnique X φ).choose_spec.1
  exact cancellation_onSite (ModuleCat.{u + 1} A) (ModuleCat.{u + 1} B) X
    E U adj (scalarExtension φ X) ad
    (scalarExtensionRepresentative φ X) hr (etaleHomTensorComparison X φ) hμ K L n

end AlgebraicGeometry.Etale
