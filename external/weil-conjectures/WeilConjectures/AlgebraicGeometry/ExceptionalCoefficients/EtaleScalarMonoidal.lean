/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Etale.EtaleFiniteCoefficientHomArrow
import all WeilConjectures.AlgebraicGeometry.ExceptionalCoefficients.ExceptionalCoefficientMaps
import all WeilConjectures.AlgebraicGeometry.Etale.Hom.EtaleHomComparisonModels
import WeilConjectures.AlgebraicGeometry.ExceptionalCoefficients.ExceptionalCoefficientLeftUnitCoherence
import WeilConjectures.AlgebraicGeometry.ExceptionalCoefficients.EtaleScalarDerivedComparison
import WeilConjectures.CategoryTheory.Sites.SheafComposeBraided
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Monoidal.RestrictScalarsBraided
import WeilConjectures.CategoryTheory.Monoidal.Braided.Adjunction
import all WeilConjectures.CategoryTheory.Derived.DerivedTensorRightExact
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.MonoidalStructure

/-! # The normalized monoidal structure on etale scalar extension

The native derived monoidal structure is transported along uniqueness of left adjoints.
Tensor normalization identifies its tensorator, and the left unit law identifies its unit.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option linter.style.haveILetI false
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
    ∀ K L, (WeilConjectures.finiteHomKoszulIso D (G.obj K) (G.obj L)).hom ≫
        (c.μIso L K).hom =
      (c.μIso K L).hom ≫ G.map (WeilConjectures.finiteHomKoszulIso C K L).hom := by
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

private theorem core_unit_unique
    {V W : Type*} [Category V] [Category W] [MonoidalCategory V] [MonoidalCategory W]
    (H : V ⥤ W) (c : H.CoreMonoidal) (i : H.obj (𝟙_ V) ≅ 𝟙_ W)
    (hi : ∀ K, (c.μIso (𝟙_ V) K).inv ≫ (i.hom ▷ H.obj K) ≫
      (λ_ (H.obj K)).hom = H.map (λ_ K).hom) :
    c.εIso.symm = i := by
  letI := c.toMonoidal
  let j : tensorRight (H.obj (𝟙_ V)) ≅ 𝟭 W :=
    (tensoringRight W).mapIso c.εIso.symm ≪≫ rightUnitorNatIso W
  letI : (tensorRight (H.obj (𝟙_ V))).Faithful := Functor.Faithful.of_iso j.symm
  apply Iso.ext
  apply (tensorRight (H.obj (𝟙_ V))).map_injective
  apply (cancel_mono (λ_ (H.obj (𝟙_ V))).hom).1
  apply (cancel_epi (c.μIso (𝟙_ V) (𝟙_ V)).inv).1
  exact (OplaxMonoidal.left_unitality_hom H (𝟙_ V)).trans (hi (𝟙_ V)).symm

private theorem normalized_core
    (r : ∀ P : CochainComplex C ℤ, G.obj (DerivedCategory.Q.obj P) ⟶
      DerivedCategory.Q.obj ((F.mapHomologicalComplex (.up ℤ)).obj P))
    (hr : ∀ P, r P = e.hom.app (DerivedCategory.Q.obj P) ≫ F.rightExact_cochainCounit P)
    (μ : ∀ K L : DerivedCategory C, G.obj K ⊗ G.obj L ≅ G.obj (K ⊗ L))
    (hμ : (∀ {K K'} (f : K ⟶ K') L,
        (G.map f ▷ G.obj L) ≫ (μ K' L).hom = (μ K L).hom ≫ G.map (f ▷ L)) ∧
      (∀ K {L L'} (f : L ⟶ L'),
        (G.obj K ◁ G.map f) ≫ (μ K L').hom = (μ K L).hom ≫ G.map (K ◁ f)) ∧
      rightExactTensorModelNormalization F G r μ)
    (i : G.obj (𝟙_ (DerivedCategory C)) ≅ 𝟙_ (DerivedCategory D))
    (hi : ∀ K, (μ (𝟙_ (DerivedCategory C)) K).inv ≫ (i.hom ▷ G.obj K) ≫
      (λ_ (G.obj K)).hom = G.map (λ_ K).hom)
    (hF : ∀ K L, F.map (β_ K L).hom ≫ OplaxMonoidal.δ F L K =
      OplaxMonoidal.δ F K L ≫ (β_ (F.obj K) (F.obj L)).hom) :
    ∃ c : G.CoreMonoidal,
      c.εIso.symm = i ∧ (∀ K L, (c.μIso K L).symm = (μ K L).symm) ∧
      (∀ K L, (WeilConjectures.finiteHomKoszulIso D (G.obj K) (G.obj L)).hom ≫
        (c.μIso L K).hom =
        (c.μIso K L).hom ≫ G.map (WeilConjectures.finiteHomKoszulIso C K L).hom) := by
  letI := F.leftDerivedFunctorMonoidal
  let c := Monoidal.coreMonoidalTransport e.symm
  have hc (K L) : (c.μIso K L).inv = (μ K L).inv :=
    core_tensor_normalized F G e r hr μ hμ K L
  have hu : c.εIso.symm = i := by
    apply core_unit_unique G c i
    intro K
    rw [hc]
    exact hi K
  refine ⟨c, hu, fun K L ↦ ?_, core_braiding F G e hF⟩
  apply Iso.ext
  exact hc K L

end CategoryTheory.Functor

namespace AlgebraicGeometry.Etale.ExceptionalCoefficients
set_option synthInstance.maxSize 4096
attribute [local irreducible] Functor.leftDerivedFunctor Functor.leftDerivedFunctorCounit

private theorem site_normalized_core
    (C : Type u₁) [Category.{u + 1} C] [Abelian C]
    [IsGrothendieckAbelian.{u + 1} C] [MonoidalCategory C] [MonoidalPreadditive C]
    [MonoidalClosed C] [SymmetricCategory C] [Abelian.HasFunctorialFlatResolution C]
    (D : Type u₂) [Category.{u + 1} D] [Abelian D]
    [IsGrothendieckAbelian.{u + 1} D] [MonoidalCategory D] [MonoidalPreadditive D]
    [MonoidalClosed D] [SymmetricCategory D] [Abelian.HasFunctorialFlatResolution D]
    (T : Scheme.{u})
    (E : Sheaf T.smallEtaleTopology C ⥤ Sheaf T.smallEtaleTopology D)
    [E.Additive] [E.PreservesKFlatQuasiIso] [E.PreservesFlat] [E.IsLeftAdjoint] [E.Monoidal]
    (S : _root_.DerivedCategory (Sheaf T.smallEtaleTopology C) ⥤
      _root_.DerivedCategory (Sheaf T.smallEtaleTopology D))
    (e : S ≅ E.leftDerivedFunctor)
    (r : ∀ P : CochainComplex (Sheaf T.smallEtaleTopology C) ℤ,
      S.obj (_root_.DerivedCategory.Q.obj P) ⟶
        _root_.DerivedCategory.Q.obj ((E.mapHomologicalComplex (.up ℤ)).obj P))
    (hr : ∀ P, r P = e.hom.app (_root_.DerivedCategory.Q.obj P) ≫
      E.rightExact_cochainCounit P)
    (δ : Functor.uncurry.obj (derivedTensor C T) ⋙ S ≅
      S.prod S ⋙ Functor.uncurry.obj (derivedTensor D T))
    (ht : SiteTensorNormalizationAux C D T E S r δ)
    (i : S.obj (𝟙_ (_root_.DerivedCategory (Sheaf T.smallEtaleTopology C))) ≅
      𝟙_ (_root_.DerivedCategory (Sheaf T.smallEtaleTopology D)))
    (hi : SiteScalarLeftUnitLaw C D T S δ i)
    (hE : ∀ K L, E.map (β_ K L).hom ≫ Functor.OplaxMonoidal.δ E L K =
      Functor.OplaxMonoidal.δ E K L ≫ (β_ (E.obj K) (E.obj L)).hom) :
    ∃ c : S.CoreMonoidal,
      c.εIso.symm = i ∧ (∀ K L, (c.μIso K L).symm = δ.app (K, L)) ∧
      (∀ K L, (WeilConjectures.finiteHomKoszulIso (Sheaf T.smallEtaleTopology D)
          (S.obj K) (S.obj L)).hom ≫ (c.μIso L K).hom =
        (c.μIso K L).hom ≫ S.map
          (WeilConjectures.finiteHomKoszulIso (Sheaf T.smallEtaleTopology C) K L).hom) := by
  exact Functor.normalized_core E S e r hr (fun K L ↦ (δ.app (K, L)).symm)
    ⟨productIso_natural₁ _ _ _ δ, productIso_natural₂ _ _ _ δ,
      tensor_normalization_flat E S r δ ht⟩ i hi hE

/-- The fixed scalar left adjoint is strong monoidal for the published tensor and unit
comparisons, and respects the actual Koszul braiding.
Source: Stacks 07A4 and 0FPT; the tensor-model and left-unit normalization theorems
(blueprint: lem-coef-etale-scalar-monoidal).

Proof: ordinary sheaf extension preserves flat objects and quasi-isomorphisms of
K-flat complexes. Its native left derived functor is therefore strong monoidal.
Transport that structure to the fixed scalar adjoint using uniqueness of left adjoints.
The transported cochain counit is the published scalar representative. Uniqueness
of the right-exact tensor comparison identifies its tensorator with tensorIso.
The published left unit law then identifies its unit: tensoring with the image
of the source unit is faithful, since that image is isomorphic to the target unit.
Finally ordinary restriction is braided lax monoidal, so its scalar left adjoint
respects braiding by adjunction. The derived braiding theorem and transport along
the adjoint isomorphism give the signed Koszul compatibility displayed below. -/
theorem scalarExtension_coreMonoidal (A B : Type (u + 1)) [CommRing A] [CommRing B]
    (φ : A →+* B) (T : Scheme.{u}) :
    ∃ c : (scalarExtension φ T).CoreMonoidal,
      c.εIso.symm = unitIso φ T ∧
      (∀ K L, (c.μIso K L).symm = (tensorIso φ T).app (K, L)) ∧
      (∀ K L,
        (WeilConjectures.finiteHomKoszulIso
          (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} B))
          ((scalarExtension φ T).obj K) ((scalarExtension φ T).obj L)).hom ≫
            (c.μIso L K).hom =
        (c.μIso K L).hom ≫ (scalarExtension φ T).map
          (WeilConjectures.finiteHomKoszulIso
            (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)) K L).hom) := by
  let E := ProEtale.etaleSheafExtendScalars φ T
  let U := Sheaf.restrictScalars T.smallEtaleTopology φ
  let adj : E ⊣ U := ProEtale.etaleSheafExtendScalarsAdjunction φ T
  letI : E.IsLeftAdjoint := adj.isLeftAdjoint
  letI : E.PreservesFlat := extension_preservesFlat φ T
  letI : E.PreservesKFlatQuasiIso := extension_preservesKFlatQuasiIso φ T
  letI : E.OplaxMonoidal := adj.leftAdjointOplaxMonoidal
  letI : E.Monoidal := composeAndSheafifyMonoidal T.smallEtaleTopology
    (ModuleCat.extendRestrictScalarsAdj.{u + 1} φ)
  let S := scalarExtension φ T
  obtain ⟨e, hr⟩ := scalarExtension_derivedComparison A B φ T
  let δ := tensorIso φ T
  have ht : TensorNormalization φ T δ := by
    have he : δ = (tensorIso_existsUnique φ T).choose :=
      eq_of_heq (siteTensorIso_existsUnique φ T).choose_spec.1
    exact he.symm ▸ (tensorIso_existsUnique φ T).choose_spec.1
  have hE (K L) : E.map (β_ K L).hom ≫ Functor.OplaxMonoidal.δ E L K =
      Functor.OplaxMonoidal.δ E K L ≫ (β_ (E.obj K) (E.obj L)).hom :=
    (adj.leftAdjointOplaxMonoidal_δ_braiding K L).symm
  exact site_normalized_core (ModuleCat.{u + 1} A) (ModuleCat.{u + 1} B)
    T E S e (scalarExtensionRepresentative φ T) hr δ ht
    (unitIso φ T) (tensorIso_left_unit φ T) hE

end AlgebraicGeometry.Etale.ExceptionalCoefficients
