/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.CoefficientAffineConstructibleProEtaleModules
import WeilConjectures.AlgebraicGeometry.CoefficientComparisonInjectiveAcyclic
import all WeilConjectures.AlgebraicGeometry.CoefficientOriginClosedDirectImage
import WeilConjectures.AlgebraicGeometry.CoefficientOriginLocalizationKernel
import WeilConjectures.AlgebraicGeometry.ConstructibleComparisonModuleExact
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusAdjunctionAcyclic
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian

/-! # Affine open-closed gluing of coefficient-sized etale origin

Source: Stacks Project, proetale.tex, Tag 09AK, proof of lemma-compare-constructible.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u v

open CategoryTheory CategoryTheory.Limits

-- The universe-polymorphic `hasSheafify_of_essentiallySmall` gets stuck on the universe of
-- `ModuleCat.{max v (u + 1)}`; Mathlib's concrete-category instance applies instead.
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall

namespace AlgebraicGeometry.ProEtale

private theorem extensions_of_derived_unit
    {C E : Type*} [Category C] [Category E] [Abelian C] [Abelian E]
    [HasDerivedCategory C] [HasDerivedCategory E] [EnoughInjectives E]
    {L : C ⥤ E} {R : E ⥤ C}
    [L.Additive] [R.Additive] [PreservesFiniteLimits L] [PreservesFiniteColimits L]
    (adj : L ⊣ R) [IsIso adj.derivedPlus.unit]
    {S : ShortComplex E} (hS : S.ShortExact)
    (h₁ : L.essImage S.X₁) (h₃ : L.essImage S.X₃) : L.essImage S.X₂ := by
  obtain ⟨G₁, ⟨e₁⟩⟩ := h₁
  obtain ⟨G₃, ⟨e₃⟩⟩ := h₃
  let α₁ := (L.mapDerivedCategorySingleFunctor 0).app G₁ ≪≫
    (DerivedCategory.singleFunctor _ 0).mapIso e₁
  let α₃ := (L.mapDerivedCategorySingleFunctor 0).app G₃ ≪≫
    (DerivedCategory.singleFunctor _ 0).mapIso e₃
  let K := (DerivedCategory.singleFunctor C 0).obj G₃
  let M := ((DerivedCategory.singleFunctor C 0).obj G₁)⟦(1 : ℤ)⟧
  have hM : DerivedCategory.TStructure.t.plus M :=
    ⟨-1, DerivedCategory.TStructure.t.isGE_shift _ 0 1 (-1)⟩
  let Kp : DerivedCategory.Plus C := ⟨K, 0, inferInstance⟩
  let Mp : DerivedCategory.Plus C := ⟨M, hM⟩
  let ff := adj.derivedPlus.fullyFaithfulLOfIsIsoUnit
  let d : L.mapDerivedCategory.obj K ⟶ L.mapDerivedCategory.obj M :=
    α₃.hom ≫ hS.singleTriangle.mor₃ ≫ α₁.inv⟦(1 : ℤ)⟧' ≫
      (L.mapDerivedCategory.commShiftIso (1 : ℤ)).inv.app _
  obtain ⟨δp, hδp⟩ := ff.map_surjective (ObjectProperty.homMk d :
    L.mapDerivedCategoryPlus.obj Kp ⟶ L.mapDerivedCategoryPlus.obj Mp)
  let δ : K ⟶ M := δp.hom
  have hδ : L.mapDerivedCategory.map δ = d :=
    congrArg (fun f ↦ f.hom) hδp
  obtain ⟨B, f, g, hT⟩ := Pretriangulated.distinguished_cocone_triangle₂ δ
  have hcomm : (L.mapDerivedCategory.map δ ≫
      (L.mapDerivedCategory.commShiftIso (1 : ℤ)).hom.app _) ≫ α₁.hom⟦(1 : ℤ)⟧' =
      α₃.hom ≫ hS.singleTriangle.mor₃ := by
    rw [hδ]
    simp [d, ← Functor.map_comp]
  let e₂ := Pretriangulated.Triangle.π₂.mapIso (Pretriangulated.isoTriangleOfIso₁₃ _ _
    (L.mapDerivedCategory.map_distinguished _ hT) hS.singleTriangle_distinguished
      α₁ α₃ hcomm)
  refine ⟨(DerivedCategory.homologyFunctor C 0).obj B, ⟨?_⟩⟩
  exact (L.mapDerivedCategoryHomologyFunctorIso 0).app B ≪≫
    (DerivedCategory.homologyFunctor E 0).mapIso e₂ ≪≫
    (DerivedCategory.singleFunctorCompHomologyFunctorIso E 0).app S.X₂

private theorem intrinsic_extensions (X : Scheme.{u})
    (A : Type (max v (u + 1))) [CommRing A]
    {S : ShortComplex (ConstantCompletion.Mod (ConstantCompletion.constant
      (Scheme.coefficientProEtaleModelTopology.{u, v} X) A))} (hS : S.ShortExact)
    (h₁ : (constructibleComparisonPullback X A).essImage S.X₁)
    (h₃ : (constructibleComparisonPullback X A).essImage S.X₃) :
    (constructibleComparisonPullback X A).essImage S.X₂ := by
  let : HasSheafify (Scheme.smallModelComparisonEtaleTopology.{u, v} X)
      AddCommGrpCat.{max v (u + 1)} :=
    GrothendieckTopology.hasSheafify_of_isGrothendieckAbelian _ _
  let : HasSheafify (Scheme.coefficientProEtaleModelTopology.{u, v} X)
      AddCommGrpCat.{max v (u + 1)} :=
    GrothendieckTopology.hasSheafify_of_isGrothendieckAbelian _ _
  let C := ConstantCompletion.Mod (ConstantCompletion.constant
    (Scheme.smallModelComparisonEtaleTopology.{u, v} X) A)
  let E := ConstantCompletion.Mod (ConstantCompletion.constant
    (Scheme.coefficientProEtaleModelTopology.{u, v} X) A)
  let : HasDerivedCategory C := HasDerivedCategory.standard C
  let : HasDerivedCategory E := HasDerivedCategory.standard E
  let : IsGrothendieckAbelian.{max v (u + 1)} C := SheafOfModules.isGrothendieckAbelian _
  let : IsGrothendieckAbelian.{max v (u + 1)} E := SheafOfModules.isGrothendieckAbelian _
  let L := constructibleComparisonPullback.{u, v} X A
  let R := SheafOfModules.pushforward.{max v (u + 1)}
    (F := Scheme.smallModelComparisonInclusion.{u, v} X)
    (constructibleComparisonRingMap.{u, v} X A)
  let adj : L ⊣ R := SheafOfModules.pullbackPushforwardAdjunction
    (constructibleComparisonRingMap.{u, v} X A)
  have : PreservesFiniteLimits L := (constructibleComparisonPullback_exact_faithful X A).1
  have : L.IsLeftAdjoint := adj.isLeftAdjoint
  have : L.Additive := Functor.additive_of_preserves_binary_products L
  have : R.Additive := adj.right_adjoint_additive
  have : R.IsRightAdjoint := adj.isRightAdjoint
  have : IsIso adj.derivedPlus.unit := by
    rw [NatTrans.isIso_iff_isIso_app]
    intro K
    exact adj.isIso_derivedPlus_unit_app_of_rightAcyclic
      (fun I _ ↦ (coefficientComparison_injectiveAcyclic X A adj I).1)
      (fun I _ ↦ (coefficientComparison_injectiveAcyclic X A adj I).2) K
  exact extensions_of_derived_unit adj hS h₁ h₃

private abbrev fixedComparison (X : Scheme.{u})
    (A : Type (max v (u + 1))) [CommRing A] :=
  Functor.sheafPullbackConstruction.sheafPullback
    (Scheme.smallModelComparisonInclusion.{u, v} X) (ModuleCat.{max v (u + 1)} A)
    (Scheme.smallModelComparisonEtaleTopology.{u, v} X)
    (Scheme.coefficientProEtaleModelTopology.{u, v} X)

private theorem fixed_extensions (X : Scheme.{u})
    (A : Type (max v (u + 1))) [CommRing A]
    {S : ShortComplex (Sheaf (Scheme.coefficientProEtaleModelTopology.{u, v} X)
      (ModuleCat.{max v (u + 1)} A))} (hS : S.ShortExact)
    (h₁ : (fixedComparison.{u, v} X A).essImage S.X₁)
    (h₃ : (fixedComparison.{u, v} X A).essImage S.X₃) :
    (fixedComparison.{u, v} X A).essImage S.X₂ := by
  let : Abelian (Sheaf (Scheme.coefficientProEtaleModelTopology.{u, v} X)
    (ModuleCat.{max v (u + 1)} A)) :=
      fixedSiteAbelian (Scheme.coefficientProEtaleModelTopology.{u, v} X) A
  let : Abelian (ConstantCompletion.Mod (ConstantCompletion.constant
      (Scheme.coefficientProEtaleModelTopology.{u, v} X) A)) :=
    intrinsicSiteAbelian (Scheme.coefficientProEtaleModelTopology.{u, v} X) A
  have := scalarEquiv (Scheme.smallModelComparisonEtaleTopology.{u, v} X) A
  have := scalarEquiv (Scheme.coefficientProEtaleModelTopology.{u, v} X) A
  let eE := (coefficientModelFixedScalars
    (Scheme.smallModelComparisonEtaleTopology.{u, v} X) A).asEquivalence
  let eP := (coefficientModelFixedScalars
    (Scheme.coefficientProEtaleModelTopology.{u, v} X) A).asEquivalence
  have : eP.inverse.Additive := Functor.additive_of_preserves_binary_products _
  let q := comparisonFixedLeft.{u, v} X A
  have hp (Y) (hY : (fixedComparison.{u, v} X A).essImage Y) :
      (constructibleComparisonPullback X A).essImage (eP.inverse.obj Y) := by
    obtain ⟨G, ⟨e⟩⟩ := hY
    refine ⟨eE.inverse.obj G, ⟨?_⟩⟩
    apply eP.functor.preimageIso
    exact q.app _ ≪≫ (fixedComparison.{u, v} X A).mapIso (eE.counitIso.app G) ≪≫
      e ≪≫ (eP.counitIso.app Y).symm
  obtain ⟨G, ⟨e⟩⟩ := intrinsic_extensions.{u, v} X A (hS.map_of_exact eP.inverse)
    (hp _ h₁) (hp _ h₃)
  exact ⟨eE.functor.obj G, ⟨(q.app G).symm ≪≫ eP.functor.mapIso e ≪≫
    eP.counitIso.app S.X₂⟩⟩

/-- Etale origin glues from the complementary open and closed subschemes of an
 affine scheme, with coefficients of independent size.
Source: Stacks Project, Tag 09AK, proof of lemma-compare-constructible, the open-closed
short exact sequence; Tag 09AH, lemma-ses-associated-to-open
(auxiliary; not a blueprint node).

Proof: let eta:F -> i_*i^*F be the unit of the canonical fixed-module adjunction.
The localization-kernel lemma makes eta epic and puts its kernel in the etale
comparison essential image from the hypothesis on j^*F. Closed direct image
preserves etale origin, so i_*i^*F is in that image by the hypothesis on i^*F.
The canonical kernel sequence is therefore short exact with both endpoints in
the image.

To prove closure under extensions, first work with intrinsic constant-ring
modules. Exactness of comparison and the existing injective-acyclicity statement
make its bounded-below derived adjunction unit invertible. Lift the connecting
arrow of the single-complex triangle through this fully faithful functor and
complete it to a distinguished triangle. Its image has the same endpoints and
connecting map as the original triangle, so their middle objects are isomorphic.
Apply zeroth homology and its comparison isomorphism to obtain an antecedent for
the original middle sheaf. Transfer this assertion through the constant-scalar
equivalences, and apply it to the kernel sequence above. No concentration assertion
for the lifted middle complex is needed. All module values remain in max v (u+1).
Empty endpoint schemes, the zero ring, and full-image nonisomorphic closed
immersions use the same unit, kernel and triangle constructions.
-/
theorem coefficientFixed_essImage_affine_openClosed
    (A : Type (max v (u + 1))) [CommRing A]
    {X Z U : Scheme.{u}} [IsAffine X] (i : Z ⟶ X) (j : U ⟶ X)
    [IsClosedImmersion i] [IsOpenImmersion j] [QuasiCompact j]
    (hU : Set.range j = (Set.range i)ᶜ)
    (F : Sheaf (Scheme.coefficientProEtaleModelTopology.{u, v} X)
      (ModuleCat.{max v (u + 1)} A))
    (hi : (Functor.sheafPullbackConstruction.sheafPullback
      (Scheme.smallModelComparisonInclusion.{u, v} Z) (ModuleCat.{max v (u + 1)} A)
      (Scheme.smallModelComparisonEtaleTopology.{u, v} Z)
      (Scheme.coefficientProEtaleModelTopology.{u, v} Z)).essImage
      ((Scheme.coefficientProEtaleFixedModulePullback.{u, v} i A).obj F))
    (hj : (Functor.sheafPullbackConstruction.sheafPullback
      (Scheme.smallModelComparisonInclusion.{u, v} U) (ModuleCat.{max v (u + 1)} A)
      (Scheme.smallModelComparisonEtaleTopology.{u, v} U)
      (Scheme.coefficientProEtaleModelTopology.{u, v} U)).essImage
      ((Scheme.coefficientProEtaleFixedModulePullback.{u, v} j A).obj F)) :
    (Functor.sheafPullbackConstruction.sheafPullback
      (Scheme.smallModelComparisonInclusion.{u, v} X) (ModuleCat.{max v (u + 1)} A)
      (Scheme.smallModelComparisonEtaleTopology.{u, v} X)
      (Scheme.coefficientProEtaleModelTopology.{u, v} X)).essImage F := by
  let : Abelian (Sheaf (Scheme.coefficientProEtaleModelTopology.{u, v} X)
    (ModuleCat.{max v (u + 1)} A)) :=
      fixedSiteAbelian (Scheme.coefficientProEtaleModelTopology.{u, v} X) A
  let adj := fixedSiteAdjunction
    (Scheme.coefficientProEtaleModelBaseChange.{u, v} i)
    (Scheme.coefficientProEtaleModelTopology.{u, v} X)
    (Scheme.coefficientProEtaleModelTopology.{u, v} Z) A
  let : HasKernel (adj.unit.app F) := fixedSiteHasKernel
    (Scheme.coefficientProEtaleModelTopology.{u, v} X) A (adj.unit.app F)
  obtain ⟨he, hk⟩ := coefficientFixed_localization_kernel_origin.{u, v} A i j hU F hj adj
  have : Epi (adj.unit.app F) := he
  let S := ShortComplex.kernelSequence (adj.unit.app F)
  have hS : S.ShortExact :=
    { exact := ShortComplex.kernelSequence_exact _, epi_g := he }
  exact fixed_extensions.{u, v} X A hS hk
    (coefficientFixed_closed_directImage_essImage.{u, v} A i _ hi)

end AlgebraicGeometry.ProEtale
