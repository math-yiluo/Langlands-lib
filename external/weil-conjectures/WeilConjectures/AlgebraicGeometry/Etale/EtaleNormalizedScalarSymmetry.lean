/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.Monoidal.EtaleDerivedTensorSymmetrySupplement
public import WeilConjectures.AlgebraicGeometry.Etale.Hom.EtaleHomComparisonModels
import all WeilConjectures.AlgebraicGeometry.ExceptionalCoefficients.ExceptionalCoefficientMaps
import all WeilConjectures.CategoryTheory.Derived.DerivedTensorRightExact
import WeilConjectures.CategoryTheory.Sites.SheafComposeBraided
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Monoidal.RestrictScalarsBraided
import WeilConjectures.CategoryTheory.Monoidal.Braided.Adjunction
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.MonoidalStructure

/-! # The normalized scalar tensor comparison respects the signed symmetry -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option linter.style.haveILetI false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u u₁ u₂
open CategoryTheory CategoryTheory.Limits MonoidalCategory
open CategoryTheory.Functor
namespace CategoryTheory.Functor
variable {C : Type u₁} [Category.{u + 1} C] [Abelian C]
  [IsGrothendieckAbelian.{u + 1} C] [MonoidalCategory C] [MonoidalPreadditive C]
  [MonoidalClosed C] [BraidedCategory C] [Abelian.HasFunctorialFlatResolution C]
  {D : Type u₂} [Category.{u + 1} D] [Abelian D]
  [IsGrothendieckAbelian.{u + 1} D] [MonoidalCategory D] [MonoidalPreadditive D]
  [MonoidalClosed D] [BraidedCategory D] [Abelian.HasFunctorialFlatResolution D]
  (F : C ⥤ D) [F.Additive] [F.PreservesKFlatQuasiIso] [F.PreservesFlat]
  [F.IsLeftAdjoint] [F.Monoidal]
  (G : DerivedCategory C ⥤ DerivedCategory D) (e : G ≅ F.leftDerivedFunctor)

private theorem core_tensor_normalized
    (r : ∀ P : CochainComplex C ℤ, G.obj (DerivedCategory.Q.obj P) ⟶
      DerivedCategory.Q.obj ((F.mapHomologicalComplex (.up ℤ)).obj P))
    (hr : ∀ P, r P = e.hom.app (DerivedCategory.Q.obj P) ≫ F.rightExact_cochainCounit P)
    (μ : ∀ K L : DerivedCategory C, G.obj K ⊗ G.obj L ≅ G.obj (K ⊗ L))
    (hμ : (∀ {K K'} (f : K ⟶ K') L,
        (G.map f ▷ G.obj L) ≫ (μ K' L).hom = (μ K L).hom ≫ G.map (f ▷ L)) ∧
      (∀ K {L L'} (f : L ⟶ L'),
        (G.obj K ◁ G.map f) ≫ (μ K L').hom = (μ K L).hom ≫ G.map (K ◁ f)) ∧
      rightExactTensorModelNormalization F G r μ) :
    letI := F.leftDerivedFunctorMonoidal
    ∀ K L, ((Monoidal.coreMonoidalTransport e.symm).μIso K L).inv = (μ K L).inv := by
  letI := F.leftDerivedFunctorMonoidal
  obtain ⟨ν, hν, huniq⟩ := rightExact_tensorComparison_existsUnique F G e r hr
  have hn : rightExactTensorModelNormalization F G r (normalizedTensorIso F G e) := by
    intro P Q _ _ _ _
    simp only [hr]
    rw [normalizedTensorIso_inv]
    simpa only [Category.assoc] using
      transfer_tensor_counit (C := DerivedCategory C) (D := DerivedCategory D)
        G F.leftDerivedFunctor e
        (T := DerivedCategory.Q.obj (((curriedTensor (CochainComplex C ℤ)).obj P).obj Q))
        _ _ _ _ _ _ (F.rightExact_comparison_cochain P Q)
  have heq : μ = normalizedTensorIso F G e :=
    (huniq μ hμ).trans (huniq _ ⟨normalizedTensorIso_natural₁ F G e,
      normalizedTensorIso_natural₂ F G e, hn⟩).symm
  intro K L
  rw [heq, normalizedTensorIso_inv]
  change (e.hom.app (K ⊗ L) ≫ OplaxMonoidal.δ F.leftDerivedFunctor K L) ≫
    (e.inv.app K ⊗ₘ e.inv.app L) = _
  rw [Category.assoc]
  rfl

private theorem core_braiding
    (hF : ∀ K L, F.map (β_ K L).hom ≫ OplaxMonoidal.δ F L K =
      OplaxMonoidal.δ F K L ≫ (β_ (F.obj K) (F.obj L)).hom) :
    letI := F.leftDerivedFunctorMonoidal
    let c := Monoidal.coreMonoidalTransport e.symm
    ∀ K L, ((DerivedCategory.canonicalTensorSymmetry D).hom.app (G.obj K)).app (G.obj L) ≫
        (c.μIso L K).hom =
      (c.μIso K L).hom ≫ G.map (((DerivedCategory.canonicalTensorSymmetry C).hom.app K).app L) := by
  letI := F.leftDerivedFunctorMonoidal
  letI := DerivedCategory.braidedCategory' C
  letI := DerivedCategory.braidedCategory' D
  letI : F.leftDerivedFunctor.Braided := F.leftDerivedFunctorBraided hF
  letI : G.Monoidal := Monoidal.transport e.symm
  letI : NatTrans.IsMonoidal e.symm.hom :=
    Monoidal.natTransIsMonoidal_of_transport e.symm
  letI : G.LaxBraided := LaxBraided.ofNatIso e.symm
  dsimp only
  intro K L
  exact (LaxBraided.braided (F := G) K L).symm

end CategoryTheory.Functor

namespace AlgebraicGeometry.Etale.ExceptionalCoefficients
attribute [local irreducible] Functor.leftDerivedFunctor Functor.leftDerivedFunctorCounit
private theorem scalarDerivedComparison
    (A B : Type (u + 1)) [CommRing A] [CommRing B] (φ : A →+* B) (T : Scheme.{u})
    [(ProEtale.etaleSheafExtendScalars φ T).PreservesKFlatQuasiIso] :
    ∃ e : scalarExtension φ T ≅ (ProEtale.etaleSheafExtendScalars φ T).leftDerivedFunctor,
      ∀ P, scalarExtensionRepresentative φ T P =
        e.hom.app (_root_.DerivedCategory.Q.obj P) ≫
          (ProEtale.etaleSheafExtendScalars φ T).rightExact_cochainCounit P := by
  let E := ProEtale.etaleSheafExtendScalars φ T
  let U := Sheaf.restrictScalars T.smallEtaleTopology φ
  let adj : E ⊣ U := ProEtale.etaleSheafExtendScalarsAdjunction φ T
  let : E.IsLeftAdjoint := adj.isLeftAdjoint
  let ad : scalarExtension φ T ⊣ U.mapDerivedCategory := Adjunction.ofIsRightAdjoint _
  let b : E.leftDerivedFunctor ⊣ U.mapDerivedCategory :=
    adj.derivedAdjunction.ofNatIsoRight U.rightDerivedFunctorIsoMapDerivedCategory
  let e : scalarExtension φ T ≅ E.leftDerivedFunctor := ad.leftAdjointUniq b
  refine ⟨e, ?_⟩
  intro P
  unfold scalarExtensionRepresentative
  rw [← mapComplex_unit_formula]
  exact (Adjunction.leftDerivedCochainCounit E U adj ad P).symm

end AlgebraicGeometry.Etale.ExceptionalCoefficients
namespace AlgebraicGeometry.Etale

/-- The canonical scalar tensor comparison preserves the Koszul symmetry.
Source: Stacks 07A4 and 06YU; the signed scalar-balancing step
(blueprint: lem-pur-etale-normalized-scalar-symmetry).

Proof: identify scalar extension with the native derived functor by uniqueness of
left adjoints, computing its representative counit. Transport the native monoidal
structure along this identification. The unique K-flat normalization identifies its
tensorator with etaleHomTensorComparison. The ordinary scalar adjunction is braided,
so its derived functor and its transported monoidal structure are braided as well.
The resulting braidedness equation is exactly the displayed signed symmetry law. -/
theorem etaleNormalizedScalarSymmetry
    {A B : Type (u + 1)} [CommRing A] [CommRing B] (φ : A →+* B) (Z : Scheme.{u})
    (K L : DerivedCategoryModule A Z) :
    (((derivedTensorSymmetry (ModuleCat.{u + 1} B) Z).hom.app
      ((scalarExtension φ Z).obj K)).app ((scalarExtension φ Z).obj L)) ≫
        (etaleHomTensorComparison Z φ L K).hom =
      (etaleHomTensorComparison Z φ K L).hom ≫ (scalarExtension φ Z).map
        (((derivedTensorSymmetry (ModuleCat.{u + 1} A) Z).hom.app K).app L) := by
  let E := ProEtale.etaleSheafExtendScalars φ Z
  let U := Sheaf.restrictScalars Z.smallEtaleTopology φ
  let adj : E ⊣ U := ProEtale.etaleSheafExtendScalarsAdjunction φ Z
  let : E.IsLeftAdjoint := adj.isLeftAdjoint
  let : E.PreservesFlat := extension_preservesFlat φ Z
  let : E.PreservesKFlatQuasiIso := extension_preservesKFlatQuasiIso φ Z
  let : E.OplaxMonoidal := adj.leftAdjointOplaxMonoidal
  let : E.Monoidal := composeAndSheafifyMonoidal Z.smallEtaleTopology
    (ModuleCat.extendRestrictScalarsAdj.{u + 1} φ)
  obtain ⟨e, hr⟩ := ExceptionalCoefficients.scalarDerivedComparison A B φ Z
  letI := E.leftDerivedFunctorMonoidal
  let c := Monoidal.coreMonoidalTransport e.symm
  have ht := Functor.core_tensor_normalized E (scalarExtension φ Z) e
    (scalarExtensionRepresentative φ Z) hr (etaleHomTensorComparison Z φ)
    (etaleHomTensorComparison_existsUnique Z φ).choose_spec.1
  have hb := Functor.core_braiding E (scalarExtension φ Z) e
    (fun K L ↦ (adj.leftAdjointOplaxMonoidal_δ_braiding K L).symm) K L
  have heq (P Q : DerivedCategoryModule A Z) :
      c.μIso P Q = etaleHomTensorComparison Z φ P Q := by
    suffices h : (c.μIso P Q).symm = (etaleHomTensorComparison Z φ P Q).symm from
      congrArg Iso.symm h
    apply Iso.ext
    exact ht P Q
  change _ ≫ (c.μIso L K).hom = (c.μIso K L).hom ≫ _ at hb
  rw [heq, heq] at hb
  exact hb

end AlgebraicGeometry.Etale
