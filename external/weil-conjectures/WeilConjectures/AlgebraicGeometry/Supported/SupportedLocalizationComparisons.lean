/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ExactPullbackTensorComparison
public import WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal.Comparison
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.FlatModuleCat

public import WeilConjectures.AlgebraicGeometry.Normalized.NormalizedSupportTriangle

/-!
# Canonical support comparisons for product localization

Source: Stacks Tags 09XP and 0F1E; blueprint lem-pur-supported-product-localization,
proof steps 1 and 5 (blueprint: def-pur-supported-localization-comparisons).
All changes of support use equality of open complements. All changes of ambient scheme
use the uniquely specified open-complement isomorphism and normalized support restriction.
-/

@[expose] public section
set_option autoImplicit false
universe u v w₁ w₂ w₃ w₄
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated MonoidalCategory
namespace AlgebraicGeometry.Etale

section

variable (E : Type v) [Category.{u + 1} E] [Abelian E]
  [IsGrothendieckAbelian.{u + 1} E] [MonoidalCategory E] [MonoidalPreadditive E]
  [SymmetricCategory E] [MonoidalClosed E] [Abelian.HasFunctorialFlatResolution E]

/-- Cache the upstream graded-tensor property at a variable scheme, so that later
specializations reuse its proof without reopening the monoidal sheaf construction.
Source: upstream K-flat tensor construction
(blueprint: def-pur-supported-localization-comparisons). -/
noncomputable instance supportGradedTensorFour (T : Scheme.{u}) :
    ∀ (X₁ X₂ X₃ X₄ : GradedObject ℤ (Sheaf T.smallEtaleTopology E)),
      GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄ :=
  inferInstance

/-- Cache the upstream graded-tensor property at a variable scheme, so that later
specializations reuse its proof without reopening the monoidal sheaf construction.
Source: upstream K-flat tensor construction
(blueprint: def-pur-supported-localization-comparisons). -/
noncomputable instance supportGradedTensorLeft (T : Scheme.{u}) :
    ∀ (X₁ X₂ X₃ : GradedObject ℤ (Sheaf T.smallEtaleTopology E)),
      GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃ :=
  inferInstance

/-- Cache the upstream graded-tensor property at a variable scheme, so that later
specializations reuse its proof without reopening the monoidal sheaf construction.
Source: upstream K-flat tensor construction
(blueprint: def-pur-supported-localization-comparisons). -/
noncomputable instance supportGradedTensorRight (T : Scheme.{u}) :
    ∀ (X₁ X₂ X₃ : GradedObject ℤ (Sheaf T.smallEtaleTopology E)),
      GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃ :=
  inferInstance

/-- The existing external product is the displayed tensor of projection pullbacks.
The equality keeps the upstream construction opaque to downstream kernel reduction.
Source: Tag 0F1E and upstream Kunneth.Defs
(blueprint: def-pur-supported-localization-comparisons).
Proof: unfold externalProduct. Its definition is exactly this derived-tensor expression
with the two generic left derived inverse-image functors; all instance proof arguments
agree by proof irrelevance. No model or comparison map is changed. -/
theorem supportedExternalProduct_eq {S X Y : Scheme.{u}}
    (f : X ⟶ S) (g : Y ⟶ S)
    (K : DerivedCategory (Sheaf X.smallEtaleTopology E))
    (L : DerivedCategory (Sheaf Y.smallEtaleTopology E)) :
    externalProduct E f g K L =
      ((derivedTensor E (pullback f g)).obj
        ((upperStar E (pullback.fst f g)).leftDerivedFunctor.obj K)).obj
        ((upperStar E (pullback.snd f g)).leftDerivedFunctor.obj L) := by
  rfl

/-- The canonical equality isomorphism exposing the upstream external-product formula.
Source: Tag 0F1E (blueprint: def-pur-supported-localization-comparisons). -/
noncomputable def supportedExternalProductIso {S X Y : Scheme.{u}}
    (f : X ⟶ S) (g : Y ⟶ S)
    (K : DerivedCategory (Sheaf X.smallEtaleTopology E))
    (L : DerivedCategory (Sheaf Y.smallEtaleTopology E)) :
    externalProduct E f g K L ≅
      ((derivedTensor E (pullback f g)).obj
        ((upperStar E (pullback.fst f g)).leftDerivedFunctor.obj K)).obj
        ((upperStar E (pullback.snd f g)).leftDerivedFunctor.obj L) :=
  eqToIso (supportedExternalProduct_eq E f g K L)

end

/-- Compose a functorial equality comparison with the tensor-square comparison,
keeping the categorical composition generic before specializing the scheme arguments.
Source: Tag 0F1E (blueprint: def-pur-supported-localization-comparisons). -/
noncomputable def supportIsoTransport
    {C : Type w₁} {D : Type w₂} [Category.{w₃} C] [Category.{w₄} D]
    (F : C ⥤ D) {X Y : C} {Z W : D}
    (e : X ≅ Y) (c : F.obj Y ≅ Z) (d : W ≅ Z) : F.obj X ≅ W :=
  F.mapIso e ≪≫ c ≪≫ d.symm

section

variable (E : Type v) [Category.{u + 1} E] [Abelian E]
  [IsGrothendieckAbelian.{u + 1} E] [MonoidalCategory E] [MonoidalPreadditive E]
  [SymmetricCategory E] [MonoidalClosed E] [Abelian.HasFunctorialFlatResolution E]
  [UpperStarPreservesFlat E]

/-- Exact inverse image composition, induced by the existing sheaf composition iso.
Source: Tag 0F1E (blueprint: def-pur-supported-localization-comparisons). -/
noncomputable def supportExactPullbackCompIso
    {R S T : Scheme.{u}} (a : R ⟶ S) (b : S ⟶ T) (c : R ⟶ T) (hc : c = a ≫ b) :
    (upperStar E c).mapDerivedCategory ≅
      (upperStar E b).mapDerivedCategory ⋙ (upperStar E a).mapDerivedCategory :=
  Functor.mapDerivedCategoryNatIso (upperStarComp E a b c hc) ≪≫
    (Functor.mapDerivedCategoryCompIso (upperStar E b) (upperStar E a)).symm

/-- Pullback comparison for a commuting projection square.
Source: Tag 0F1E (blueprint: def-pur-supported-localization-comparisons). -/
noncomputable def supportPullbackSquareIso
    {P Q X X' : Scheme.{u}} (h : Q ⟶ P) (p : P ⟶ X) (q : Q ⟶ X')
    (a : X' ⟶ X) (hp : h ≫ p = q ≫ a) (K : DerivedCategory (Sheaf X.smallEtaleTopology E)) :
    (upperStar E h).mapDerivedCategory.obj ((upperStar E p).leftDerivedFunctor.obj K) ≅
      (upperStar E q).leftDerivedFunctor.obj (((upperStar E a).mapDerivedCategory).obj K) :=
  (leftDerivedUpperStarIsoMapDerivedCategory E h).symm.app
      ((upperStar E p).leftDerivedFunctor.obj K) ≪≫
    (leftDerivedUpperStarComp E h p).symm.app K ≪≫
    (leftDerivedUpperStarComp E q a (h ≫ p) hp).app K ≪≫
    (upperStar E q).leftDerivedFunctor.mapIso
      ((leftDerivedUpperStarIsoMapDerivedCategory E a).app K)

/-- Pullback comparison when the uncut projection has the same target.
Source: Tag 0F1E (blueprint: def-pur-supported-localization-comparisons). -/
noncomputable def supportPullbackProjectionIso
    {P Q X : Scheme.{u}} (h : Q ⟶ P) (p : P ⟶ X) (q : Q ⟶ X)
    (hp : h ≫ p = q) (K : DerivedCategory (Sheaf X.smallEtaleTopology E)) :
    (upperStar E h).mapDerivedCategory.obj ((upperStar E p).leftDerivedFunctor.obj K) ≅
      (upperStar E q).leftDerivedFunctor.obj K :=
  (leftDerivedUpperStarIsoMapDerivedCategory E h).symm.app
      ((upperStar E p).leftDerivedFunctor.obj K) ≪≫
    (leftDerivedUpperStarComp E h p q hp.symm).symm.app K

/-- Tensor the two projection-square comparisons before specializing the ambient schemes.
Source: Tag 0F1E (blueprint: def-pur-supported-localization-comparisons). -/
noncomputable def supportTensorFirstSquareIso
    {P Q X X' Y : Scheme.{u}} (h : Q ⟶ P) (p : P ⟶ X) (q : P ⟶ Y)
    (p' : Q ⟶ X') (q' : Q ⟶ Y) (a : X' ⟶ X)
    (hp : h ≫ p = p' ≫ a) (hq : h ≫ q = q')
    (K : DerivedCategory (Sheaf X.smallEtaleTopology E))
    (L : DerivedCategory (Sheaf Y.smallEtaleTopology E)) :
    (upperStar E h).mapDerivedCategory.obj
        (((derivedTensor E P).obj ((upperStar E p).leftDerivedFunctor.obj K)).obj
          ((upperStar E q).leftDerivedFunctor.obj L)) ≅
      ((derivedTensor E Q).obj
        ((upperStar E p').leftDerivedFunctor.obj (((upperStar E a).mapDerivedCategory).obj K))).obj
        ((upperStar E q').leftDerivedFunctor.obj L) :=
  supportExactPullbackTensorIso E h
      ((upperStar E p).leftDerivedFunctor.obj K) ((upperStar E q).leftDerivedFunctor.obj L) ≪≫
    supportDerivedTensorIso E Q (supportPullbackSquareIso E h p p' a hp K)
      (supportPullbackProjectionIso E h q q' hq L)

/-- Canonical exterior-product transport for a projection square with variable schemes.
Its construction composes the canonical tensor and pullback comparisons before any
open subscheme is substituted for the variable ambient scheme.
Source: Tag 0F1E (blueprint: def-pur-supported-localization-comparisons). -/
noncomputable def supportExternalFirstSquareIso
    {S X X' Y : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S)
    (f' : X' ⟶ S) (a : X' ⟶ X)
    (h : pullback f' g ⟶ pullback f g)
    (hp : h ≫ pullback.fst f g = pullback.fst f' g ≫ a)
    (hq : h ≫ pullback.snd f g = pullback.snd f' g)
    (K : DerivedCategory (Sheaf X.smallEtaleTopology E))
    (L : DerivedCategory (Sheaf Y.smallEtaleTopology E)) :
    (upperStar E h).mapDerivedCategory.obj (externalProduct E f g K L) ≅
      externalProduct E f' g ((upperStar E a).mapDerivedCategory.obj K) L :=
  supportIsoTransport (upperStar E h).mapDerivedCategory
    (supportedExternalProductIso E f g K L)
    (supportTensorFirstSquareIso E h (pullback.fst f g) (pullback.snd f g)
      (pullback.fst f' g) (pullback.snd f' g) a hp hq K L)
    (supportedExternalProductIso E f' g ((upperStar E a).mapDerivedCategory.obj K) L)

end

/-- Canonical supported restriction followed by a specified coefficient comparison.
The construction is shared before specializing to product schemes.
Source: Tags 09XP and 0F1E (blueprint: def-pur-supported-localization-comparisons). -/
noncomputable def supportedRestrictionWithComparison (A : Type (u + 1)) [CommRing A]
    {T S B D : Scheme.{u}} (h : S ⟶ T) [IsOpenImmersion h]
    (b : B ⟶ T) (d : D ⟶ S) [IsClosedImmersion b] [IsClosedImmersion d]
    (hd : d.openComplement = h ⁻¹ᵁ b.openComplement)
    (K : DerivedCategoryModule A T) (L : DerivedCategoryModule A S)
    (e : (upperStar (ModuleCat.{u + 1} A) h).mapDerivedCategory.obj K ≅ L) :
    (supportedSectionsDerived A b).obj K ⟶ (supportedSectionsDerived A d).obj L :=
  (derivedSupportTransport A h b d hd).app K ≫ (supportedSectionsDerived A d).map e.hom

/-- Canonical support transport through a scheme isomorphism over an ambient scheme,
followed by the canonical pullback-composition and the specified coefficient comparison.
Source: Tags 09XP and 0F1E (blueprint: def-pur-supported-localization-comparisons). -/
noncomputable def supportedAmbientComparison (A : Type (u + 1)) [CommRing A]
    {P T S B D : Scheme.{u}} (e : S ≅ T)
    (b : B ⟶ T) (d : D ⟶ S) [IsClosedImmersion b] [IsClosedImmersion d]
    (hd : d.openComplement = e.hom ⁻¹ᵁ b.openComplement)
    (h : T ⟶ P) (a : S ⟶ P) (ha : a = e.hom ≫ h)
    (K : DerivedCategoryModule A P) (L : DerivedCategoryModule A S)
    (c : (upperStar (ModuleCat.{u + 1} A) a).mapDerivedCategory.obj K ≅ L) :
    (supportedSectionsDerived A b).obj
        ((upperStar (ModuleCat.{u + 1} A) h).mapDerivedCategory.obj K) ≅
      (supportedSectionsDerived A d).obj L :=
  (asIso (derivedSupportTransport A e.hom b d hd)).app
      ((upperStar (ModuleCat.{u + 1} A) h).mapDerivedCategory.obj K) ≪≫
    (supportedSectionsDerived A d).mapIso
      ((supportExactPullbackCompIso (ModuleCat.{u + 1} A) e.hom h a ha).symm.app K ≪≫ c)

/-- The product map after restricting the First ambient scheme.
Source: Tag 0F1E (blueprint: def-pur-supported-localization-comparisons). -/
noncomputable def supportedFirstOpenMap {S X Y : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S)
    (U : X.Opens) : pullback (U.ι ≫ f) g ⟶ pullback f g :=
  pullback.map (U.ι ≫ f) g f g U.ι (𝟙 Y) (𝟙 S) (by simp) (by simp)

/-- The fst projection square for the product-open inclusion.
Source: Tag 0F1E (blueprint: def-pur-supported-localization-comparisons).
Proof: apply pullback.map_fst, and simplify the identity on the uncut factor. -/
theorem supportedFirstOpenMap_fst {S X Y : Scheme.{u}}
    (f : X ⟶ S) (g : Y ⟶ S) (U : X.Opens) :
    supportedFirstOpenMap f g U ≫ pullback.fst f g =
      pullback.fst (U.ι ≫ f) g ≫ U.ι := by
  simp [supportedFirstOpenMap]

/-- The snd projection square for the product-open inclusion.
Source: Tag 0F1E (blueprint: def-pur-supported-localization-comparisons).
Proof: apply pullback.map_snd, and simplify the identity on the uncut factor. -/
theorem supportedFirstOpenMap_snd {S X Y : Scheme.{u}}
    (f : X ⟶ S) (g : Y ⟶ S) (U : X.Opens) :
    supportedFirstOpenMap f g U ≫ pullback.snd f g =
      pullback.snd (U.ι ≫ f) g := by
  simp [supportedFirstOpenMap]

/-- This product map is an open immersion, by base change of the open inclusion.
Source: Tag 0F1E (blueprint: def-pur-supported-localization-comparisons).
Proof: identify the map with the base change of the open inclusion along the projection;
open immersions are preserved by base change and composition with an isomorphism. -/
@[instance]
theorem supportedFirstOpenMap_open {S X Y : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S)
    (U : X.Opens) : IsOpenImmersion (supportedFirstOpenMap f g U) := by
  unfold supportedFirstOpenMap
  infer_instance

section

variable (E : Type v) [Category.{u + 1} E] [Abelian E]
  [IsGrothendieckAbelian.{u + 1} E] [MonoidalCategory E] [MonoidalPreadditive E]
  [SymmetricCategory E] [MonoidalClosed E] [Abelian.HasFunctorialFlatResolution E]
  [UpperStarPreservesFlat E]

/-- The canonical external-product comparison for the indicated open product.
Source: Tag 0F1E (blueprint: def-pur-supported-localization-comparisons). -/
noncomputable def supportedFirstExternalOpenIso
    {S X Y : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S) (U : X.Opens)
    (K : DerivedCategory (Sheaf X.smallEtaleTopology E))
    (L : DerivedCategory (Sheaf Y.smallEtaleTopology E)) :
    (upperStar E (supportedFirstOpenMap f g U)).mapDerivedCategory.obj
        (externalProduct E f g K L) ≅
      externalProduct E (U.ι ≫ f) g ((upperStar E U.ι).mapDerivedCategory.obj K) L :=
  supportExternalFirstSquareIso E f g (U.ι ≫ f) U.ι (supportedFirstOpenMap f g U)
    (supportedFirstOpenMap_fst f g U) (supportedFirstOpenMap_snd f g U) K L

end

private theorem productComplement {S X Y B D : Scheme.{u}}
    (f : X ⟶ S) (g : Y ⟶ S) (b : B ⟶ X) (d : D ⟶ Y)
    [IsClosedImmersion b] [IsClosedImmersion d] :
    (supportedProductImmersion f g b d).openComplement =
      pullback.fst f g ⁻¹ᵁ b.openComplement ⊔ pullback.snd f g ⁻¹ᵁ d.openComplement := by
  apply TopologicalSpace.Opens.ext
  simp [Scheme.Hom.coe_openComplement, supportedProductImmersion,
    Scheme.Pullback.range_map, Set.compl_inter, Set.preimage_compl]

/-- Complement identity for the product support after open base change.
Source: Tag 09XP (blueprint: def-pur-supported-localization-comparisons).
Proof: on affine charts the product support is defined by the sum of the extended
support ideals. Pulling back to the indicated open restricts those same ideals. -/
theorem supportedFirstOpenSupport_complement {S X Y B D : Scheme.{u}}
    (f : X ⟶ S) (g : Y ⟶ S) (b : B ⟶ X) (d : D ⟶ Y)
    [IsClosedImmersion b] [IsClosedImmersion d] (U : X.Opens) :
    (supportedProductImmersion (U.ι ≫ f) g (supportOnOpen b U) d).openComplement =
      supportedFirstOpenMap f g U ⁻¹ᵁ (supportedProductImmersion f g b d).openComplement := by
  simp only [productComplement, supportOnOpen_complement, Scheme.Hom.preimage_sup,
    ← Scheme.Hom.comp_preimage, supportedFirstOpenMap_fst, supportedFirstOpenMap_snd]

/-- Restriction of supported sections on the external product, with its canonical
external-product pullback comparison. Source: Tags 09XP and 0F1E
(blueprint: def-pur-supported-localization-comparisons). -/
noncomputable def supportedFirstExternalRestriction (A : Type (u + 1)) [CommRing A]
    {S X Y B D : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S) (b : B ⟶ X) (d : D ⟶ Y)
    [IsClosedImmersion b] [IsClosedImmersion d] (U : X.Opens)
    (K : DerivedCategoryModule A X) (L : DerivedCategoryModule A Y) :
    (supportedSectionsDerived A (supportedProductImmersion f g b d)).obj
        (externalProduct (ModuleCat.{u + 1} A) f g K L) ⟶
      (supportedSectionsDerived A (supportedProductImmersion (U.ι ≫ f) g (supportOnOpen b U) d)).obj
        (externalProduct (ModuleCat.{u + 1} A) (U.ι ≫ f) g ((upperStar
      (ModuleCat.{u + 1} A) U.ι).mapDerivedCategory.obj
          K) L) :=
  supportedRestrictionWithComparison A (supportedFirstOpenMap f g U)
    (supportedProductImmersion f g b d) (supportedProductImmersion (U.ι ≫ f) g (supportOnOpen b U)
      d)
    (supportedFirstOpenSupport_complement f g b d U)
    (externalProduct (ModuleCat.{u + 1} A) f g K L) (externalProduct (ModuleCat.{u + 1} A) (U.ι ≫
      f) g ((upperStar (ModuleCat.{u + 1} A) U.ι).mapDerivedCategory.obj K) L)
    (supportedFirstExternalOpenIso (ModuleCat.{u + 1} A) f g U K L)

/-- The actual open-product identification is uniquely specified over the product.
Source: Tag 09XP, affine support identification
(blueprint: def-pur-supported-localization-comparisons).
Proof: the inverse image of the closed cut support has open complement the indicated
open product. The universal property of the open subscheme gives the unique isomorphism. -/
theorem exists_unique_supportedFirstProductComplementIso {S X Y C : Scheme.{u}}
    (f : X ⟶ S) (g : Y ⟶ S) (c : C ⟶ X) [IsClosedImmersion c] :
    ∃! e : pullback (c.openComplement.ι ≫ f) g ≅ (supportedProductImmersion f g c (𝟙
      Y)).openComplement,
      e.hom ≫ (supportedProductImmersion f g c (𝟙 Y)).openComplement.ι = supportedFirstOpenMap f
        g c.openComplement := by
  let h := supportedFirstOpenMap f g c.openComplement
  let U := (supportedProductImmersion f g c (𝟙 Y)).openComplement
  have hr : Set.range h = Set.range U.ι := by
    rw [Scheme.Opens.range_ι]
    simp [h, U, supportedFirstOpenMap, supportedProductImmersion,
      Scheme.Pullback.range_map, Scheme.Hom.coe_openComplement, Set.preimage_compl]
  refine ⟨IsOpenImmersion.isoOfRangeEq h U.ι hr,
    IsOpenImmersion.isoOfRangeEq_hom_fac h U.ι hr, ?_⟩
  intro e he
  apply Iso.ext
  apply (cancel_mono U.ι).mp
  exact he.trans (IsOpenImmersion.isoOfRangeEq_hom_fac h U.ι hr).symm

/-- The uniquely specified identification with the open product.
Source: Tag 09XP (blueprint: def-pur-supported-localization-comparisons). -/
noncomputable def supportedFirstProductComplementIso {S X Y C : Scheme.{u}}
    (f : X ⟶ S) (g : Y ⟶ S) (c : C ⟶ X) [IsClosedImmersion c] :
    pullback (c.openComplement.ι ≫ f) g ≅ (supportedProductImmersion f g c (𝟙 Y)).openComplement :=
  (exists_unique_supportedFirstProductComplementIso f g c).choose

/-- The product-complement isomorphism lies over the original product.
Source: Tag 09XP (blueprint: def-pur-supported-localization-comparisons).
Proof: this is the normalization of the unique open-subscheme isomorphism. -/
theorem supportedFirstProductComplementIso_over {S X Y C : Scheme.{u}}
    (f : X ⟶ S) (g : Y ⟶ S) (c : C ⟶ X) [IsClosedImmersion c] :
    (supportedFirstProductComplementIso f g c).hom ≫ (supportedProductImmersion f g c (𝟙
      Y)).openComplement.ι =
      supportedFirstOpenMap f g c.openComplement := by
  exact (exists_unique_supportedFirstProductComplementIso f g c).choose_spec.1

/-- Identification of the restricted product support under that open-product isomorphism.
Source: Tag 09XP (blueprint: def-pur-supported-localization-comparisons).
Proof: both complements are obtained by restricting the complement of B times D to
the product open. Apply the complement identity for base change and the over equality. -/
theorem supportedFirstProductComplement_support {S X Y B C D : Scheme.{u}}
    (f : X ⟶ S) (g : Y ⟶ S) (b : B ⟶ X) (c : C ⟶ X) (d : D ⟶ Y)
    [IsClosedImmersion b] [IsClosedImmersion c] [IsClosedImmersion d] :
    (supportedProductImmersion (c.openComplement.ι ≫ f) g (supportOnOpen b c.openComplement)
      d).openComplement =
      (supportedFirstProductComplementIso f g c).hom ⁻¹ᵁ
        (supportOnOpen (supportedProductImmersion f g b d) (supportedProductImmersion f g c (𝟙
          Y)).openComplement).openComplement := by
  rw [supportOnOpen_complement, ← Scheme.Hom.comp_preimage,
    supportedFirstProductComplementIso_over, supportedFirstOpenSupport_complement]

/-- The third target term is identified with supported sections on the actual open
product, using the canonical scheme, support and external-product comparisons.
Source: Tags 09XP and 0F1E (blueprint: def-pur-supported-localization-comparisons). -/
noncomputable def supportedFirstLocalizationThirdIso (A : Type (u + 1)) [CommRing A]
    {S X Y B C D : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S)
    (b : B ⟶ X) (c : C ⟶ X) (d : D ⟶ Y)
    [IsClosedImmersion b] [IsClosedImmersion c] [IsClosedImmersion d]
    (K : DerivedCategoryModule A X) (L : DerivedCategoryModule A Y) :
    (supportedSectionsDerived A
        (supportOnOpen (supportedProductImmersion f g b d) (supportedProductImmersion f g c (𝟙
          Y)).openComplement)).obj
        ((upperStar (ModuleCat.{u + 1} A) (supportedProductImmersion f g c (𝟙
      Y)).openComplement.ι).mapDerivedCategory.obj
          (externalProduct (ModuleCat.{u + 1} A) f g K L)) ≅
      (supportedSectionsDerived A (supportedProductImmersion (c.openComplement.ι ≫ f) g
        (supportOnOpen b c.openComplement) d)).obj
        (externalProduct (ModuleCat.{u + 1} A) (c.openComplement.ι ≫ f) g
          ((upperStar (ModuleCat.{u + 1} A) c.openComplement.ι).mapDerivedCategory.obj K) L) :=
  supportedAmbientComparison A (supportedFirstProductComplementIso f g c)
    (supportOnOpen (supportedProductImmersion f g b d) (supportedProductImmersion f g c (𝟙
      Y)).openComplement)
    (supportedProductImmersion (c.openComplement.ι ≫ f) g (supportOnOpen b c.openComplement) d)
    (supportedFirstProductComplement_support f g b c d)
    (supportedProductImmersion f g c (𝟙 Y)).openComplement.ι (supportedFirstOpenMap f g
      c.openComplement)
    (supportedFirstProductComplementIso_over f g c).symm
    (externalProduct (ModuleCat.{u + 1} A) f g K L) (externalProduct (ModuleCat.{u + 1} A)
      (c.openComplement.ι ≫ f) g ((upperStar (ModuleCat.{u + 1} A)
      c.openComplement.ι).mapDerivedCategory.obj K) L)
    (supportedFirstExternalOpenIso (ModuleCat.{u + 1} A) f g c.openComplement K L)

/-- The product map after restricting the Second ambient scheme.
Source: Tag 0F1E (blueprint: def-pur-supported-localization-comparisons). -/
noncomputable def supportedSecondOpenMap {S X Y : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S)
    (V : Y.Opens) : pullback f (V.ι ≫ g) ⟶ pullback f g :=
  pullback.map f (V.ι ≫ g) f g (𝟙 X) V.ι (𝟙 S) (by simp) (by simp)

/-- The fst projection square for the product-open inclusion.
Source: Tag 0F1E (blueprint: def-pur-supported-localization-comparisons).
Proof: apply pullback.map_fst, and simplify the identity on the uncut factor. -/
theorem supportedSecondOpenMap_fst {S X Y : Scheme.{u}}
    (f : X ⟶ S) (g : Y ⟶ S) (V : Y.Opens) :
    supportedSecondOpenMap f g V ≫ pullback.fst f g =
      pullback.fst f (V.ι ≫ g) := by
  simp [supportedSecondOpenMap]

/-- The snd projection square for the product-open inclusion.
Source: Tag 0F1E (blueprint: def-pur-supported-localization-comparisons).
Proof: apply pullback.map_snd, and simplify the identity on the uncut factor. -/
theorem supportedSecondOpenMap_snd {S X Y : Scheme.{u}}
    (f : X ⟶ S) (g : Y ⟶ S) (V : Y.Opens) :
    supportedSecondOpenMap f g V ≫ pullback.snd f g =
      pullback.snd f (V.ι ≫ g) ≫ V.ι := by
  simp [supportedSecondOpenMap]

/-- This product map is an open immersion, by base change of the open inclusion.
Source: Tag 0F1E (blueprint: def-pur-supported-localization-comparisons).
Proof: identify the map with the base change of the open inclusion along the projection;
open immersions are preserved by base change and composition with an isomorphism. -/
@[instance]
theorem supportedSecondOpenMap_open {S X Y : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S)
    (V : Y.Opens) : IsOpenImmersion (supportedSecondOpenMap f g V) := by
  unfold supportedSecondOpenMap
  infer_instance

section

variable (E : Type v) [Category.{u + 1} E] [Abelian E]
  [IsGrothendieckAbelian.{u + 1} E] [MonoidalCategory E] [MonoidalPreadditive E]
  [SymmetricCategory E] [MonoidalClosed E] [Abelian.HasFunctorialFlatResolution E]
  [UpperStarPreservesFlat E]

end

/-- Canonical restriction between the cut complements, specified over the ambient scheme.
Source: Tag 09XP (blueprint: def-pur-supported-localization-comparisons). -/
noncomputable def supportCutOpenMap {T S C C' : Scheme.{u}}
    (h : S ⟶ T) [IsOpenImmersion h] (c : C ⟶ T) (c' : C' ⟶ S)
    [IsClosedImmersion c] [IsClosedImmersion c']
    (hc : c'.openComplement = h ⁻¹ᵁ c.openComplement) :
    c'.openComplement.toScheme ⟶ c.openComplement.toScheme :=
  eqToHom (congrArg (fun U : S.Opens ↦ U.toScheme) hc) ≫
    morphismRestrict h c.openComplement

/-- The canonical cut-complement map has its defining composite.
Source: Tag 09XP (blueprint: def-pur-supported-localization-comparisons).
Proof: use morphismRestrict_ι and transport along the given equality of open subsets. -/
theorem supportCutOpenMap_over {T S C C' : Scheme.{u}}
    (h : S ⟶ T) [IsOpenImmersion h] (c : C ⟶ T) (c' : C' ⟶ S)
    [IsClosedImmersion c] [IsClosedImmersion c']
    (hc : c'.openComplement = h ⁻¹ᵁ c.openComplement) :
    supportCutOpenMap h c c' hc ≫ c.openComplement.ι = c'.openComplement.ι ≫ h := by
  have transport (U V : S.Opens) (e : U = V) :
      eqToHom (congrArg (fun W : S.Opens ↦ W.toScheme) e) ≫ V.ι = U.ι := by
    subst V
    simp
  simp only [supportCutOpenMap, Category.assoc, morphismRestrict_ι]
  rw [← Category.assoc, transport _ _ hc]

/-- Restriction between cut complements is an open immersion.
Source: Tag 09XP (blueprint: def-pur-supported-localization-comparisons).
Proof: its composite with the open inclusion is the composite of two open immersions.
Cancel the open inclusion, or identify the map with the corresponding open base change. -/
@[instance]
theorem supportCutOpenMap_open {T S C C' : Scheme.{u}}
    (h : S ⟶ T) [IsOpenImmersion h] (c : C ⟶ T) (c' : C' ⟶ S)
    [IsClosedImmersion c] [IsClosedImmersion c']
    (hc : c'.openComplement = h ⁻¹ᵁ c.openComplement) :
    IsOpenImmersion (supportCutOpenMap h c c' hc) := by
  unfold supportCutOpenMap
  infer_instance

/-- On the cut complements the restricted support has the inverse-image complement.
Source: Tag 09XP (blueprint: def-pur-supported-localization-comparisons).
Proof: use supportOnOpen_complement on both sides. The defining over equality of the
cut-complement map and the complement equality for B identify the two inverse images. -/
theorem supportRestrictedCut_complement {T S B C B' C' : Scheme.{u}}
    (h : S ⟶ T) [IsOpenImmersion h]
    (b : B ⟶ T) (c : C ⟶ T) (b' : B' ⟶ S) (c' : C' ⟶ S)
    [IsClosedImmersion b] [IsClosedImmersion c]
    [IsClosedImmersion b'] [IsClosedImmersion c']
    (_hb : b'.openComplement = h ⁻¹ᵁ b.openComplement)
    (hc : c'.openComplement = h ⁻¹ᵁ c.openComplement) :
    (supportOnOpen b' c'.openComplement).openComplement =
      supportCutOpenMap h c c' hc ⁻¹ᵁ (supportOnOpen b c.openComplement).openComplement := by
  simp only [supportOnOpen_complement, _hb, ← Scheme.Hom.comp_preimage,
    supportCutOpenMap_over]

/-- Canonical third-term restriction of a support localization triangle.
The coefficient comparison is the composite of the two exact pullback composition
isomorphisms for the commuting square of cut-complement inclusions.
Source: Tag 09XP (blueprint: def-pur-supported-localization-comparisons). -/
noncomputable def supportTriangleRestrictionThird (A : Type (u + 1)) [CommRing A]
    {T S B C B' C' : Scheme.{u}} (h : S ⟶ T) [IsOpenImmersion h]
    (b : B ⟶ T) (c : C ⟶ T) (b' : B' ⟶ S) (c' : C' ⟶ S)
    [IsClosedImmersion b] [IsClosedImmersion c]
    [IsClosedImmersion b'] [IsClosedImmersion c']
    (hb : b'.openComplement = h ⁻¹ᵁ b.openComplement)
    (hc : c'.openComplement = h ⁻¹ᵁ c.openComplement)
    (K : DerivedCategoryModule A T) :
    (normalizedSupportTriangle A b c K).obj₃ ⟶
      (normalizedSupportTriangle A b' c'
        ((upperStar (ModuleCat.{u + 1} A) h).mapDerivedCategory.obj K)).obj₃ :=
  (derivedSupportTransport A (supportCutOpenMap h c c' hc)
      (supportOnOpen b c.openComplement) (supportOnOpen b' c'.openComplement)
      (supportRestrictedCut_complement h b c b' c' hb hc)).app
        ((upperStar (ModuleCat.{u + 1} A) c.openComplement.ι).mapDerivedCategory.obj K) ≫
    (supportedSectionsDerived A (supportOnOpen b' c'.openComplement)).map
      (((supportExactPullbackCompIso (ModuleCat.{u + 1} A) (supportCutOpenMap h c c' hc)
          c.openComplement.ι (c'.openComplement.ι ≫ h)
          (supportCutOpenMap_over h c c' hc).symm).symm ≪≫
        supportExactPullbackCompIso (ModuleCat.{u + 1} A) c'.openComplement.ι h
          (c'.openComplement.ι ≫ h) rfl).hom.app K)

end AlgebraicGeometry.Etale
