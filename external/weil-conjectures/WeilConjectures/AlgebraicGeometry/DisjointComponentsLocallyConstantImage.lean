/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.EtaleSheaves

import WeilConjectures.Mathlib.CategoryTheory.Sites.ConstantSheafOver
import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtaleDisjointCover
import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs

/-! # Local constancy of direct image from disjoint components

Source: smooth purity blueprint, final paragraph of
`lem-weil-pbc-finite-pushforward-generic-constructible`.
(blueprint: lem-weil-pbc-disjoint-components-locally-constant-image).
-/

@[expose] public section

set_option autoImplicit false
universe u
open CategoryTheory
namespace AlgebraicGeometry.Scheme

set_option backward.isDefEq.respectTransparency false in
open CategoryTheory.Limits Opposite in
/-- The component of an etale test object lying over the given open. -/
private noncomputable def componentTest {X : Scheme.{u}} (U : X.Opens)
    (V : X.Etale) : X.Etale :=
  (MorphismProperty.Over.map ⊤ (inferInstance : AlgebraicGeometry.Etale U.ι)).obj
    (U.ι.Etale.obj V)

set_option backward.isDefEq.respectTransparency false in
open CategoryTheory.Limits Opposite in
/-- The open immersion of the component into the test object. -/
private noncomputable def componentTestProjection {X : Scheme.{u}} (U : X.Opens)
    (V : X.Etale) : componentTest U V ⟶ V :=
  MorphismProperty.Over.homMk (pullback.fst V.hom U.ι) pullback.condition

set_option backward.isDefEq.respectTransparency false in
open CategoryTheory.Limits Opposite in
/-- Restriction to an open component, regarded as a map to its pushed-forward restriction. -/
private noncomputable def componentRestrictionMap {X : Scheme.{u}} (U : X.Opens)
    (E : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) :
    E ⟶ (Etale.lowerStar AddCommGrpCat.{u + 1} U.ι).obj
      ((Etale.localizationRestriction AddCommGrpCat.{u + 1} U.ι inferInstance).obj E) where
  hom :=
    { app := fun V ↦ E.obj.map (componentTestProjection U V.unop).op
      naturality := by
        intro V V' g
        change E.obj.map g ≫ E.obj.map (componentTestProjection U V'.unop).op =
          E.obj.map (componentTestProjection U V.unop).op ≫
            E.obj.map ((MorphismProperty.Over.map ⊤
              (inferInstance : AlgebraicGeometry.Etale U.ι)).map
                (U.ι.Etale.map g.unop)).op
        rw [← E.obj.map_comp, ← E.obj.map_comp]
        congr 1
        apply Quiver.Hom.unop_inj
        apply MorphismProperty.Over.Hom.ext
        exact (Scheme.Hom.etale_map_left_comp_fst U.ι g.unop).symm }

set_option backward.isDefEq.respectTransparency false in
open CategoryTheory.Limits Opposite in
/-- The sheaf axiom on disjoint covers identifies a sheaf with its component product. -/
private theorem component_source_product {X : Scheme.{u}}
    (n : ℕ) (W : Fin n → X.Opens)
    (hcover : (⨆ i, W i) = ⊤)
    (hdisjoint : Pairwise (fun i j ↦ Disjoint (W i) (W j)))
    (E : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) :
    Nonempty (E ≅ ∏ᶜ fun i : Fin n ↦
      (Etale.lowerStar AddCommGrpCat.{u + 1} (W i).ι).obj
        ((Etale.localizationRestriction AddCommGrpCat.{u + 1}
          (W i).ι inferInstance).obj E)) := by
  let R (i : Fin n) := (Etale.lowerStar AddCommGrpCat.{u + 1} (W i).ι).obj
    ((Etale.localizationRestriction AddCommGrpCat.{u + 1}
      (W i).ι inferInstance).obj E)
  let φ : E ⟶ ∏ᶜ R := Pi.lift (fun i ↦ componentRestrictionMap (W i) E)
  have hc : ⋃ i, (W i : Set X) = Set.univ := by
    simpa only [TopologicalSpace.Opens.coe_iSup, TopologicalSpace.Opens.coe_top] using
      congrArg (fun U : X.Opens ↦ (U : Set X)) hcover
  have hφ (V : X.Etaleᵒᵖ) : IsIso (φ.hom.app V) := by
    let β (i : Fin n) := componentTestProjection (W i) V.unop
    have hmono (i : Fin n) : Mono (β i) := by
      apply (MorphismProperty.Over.forget @Etale ⊤ X ⋙ Over.forget X).mono_of_mono_map
      change Mono (pullback.fst V.unop.hom (W i).ι)
      infer_instance
    have hcov : Sieve.ofArrows (fun i ↦ componentTest (W i) V.unop) β ∈
        X.smallEtaleTopology V.unop := by
      rw [ofArrows_mem_smallEtaleTopology_iff]
      change (⋃ i, Set.range (pullback.fst V.unop.hom (W i).ι).base) = Set.univ
      simp only [Scheme.Pullback.range_fst, Scheme.Opens.range_ι]
      rw [← Set.preimage_iUnion, hc, Set.preimage_univ]
    have hd : ∀ i j : Fin n, i ≠ j →
        Disjoint (Set.range (β i).left.base) (Set.range (β j).left.base) := by
      intro i j hij
      change Disjoint (Set.range (pullback.fst V.unop.hom (W i).ι).base)
        (Set.range (pullback.fst V.unop.hom (W j).ι).base)
      simp only [Scheme.Pullback.range_fst, Scheme.Opens.range_ι]
      have hdi : Disjoint (W i : Set X) (W j : Set X) :=
        TopologicalSpace.Opens.coe_disjoint.mpr (hdisjoint hij)
      exact hdi.preimage V.unop.hom
    have hiso := Etale.isIso_piLift_of_disjoint E
      (fun i ↦ componentTest (W i) V.unop) β hcov hd
    let ev := sheafToPresheaf X.smallEtaleTopology AddCommGrpCat.{u + 1} ⋙
      (CategoryTheory.evaluation X.Etaleᵒᵖ AddCommGrpCat.{u + 1}).obj V
    have hw : ev.map φ ≫ (PreservesProduct.iso ev R).hom =
        Pi.lift (fun i ↦ E.obj.map (β i).op) := by
      apply Pi.hom_ext
      intro i
      rw [Category.assoc, PreservesProduct.iso_hom, piComparison_comp_π,
        ← ev.map_comp, Pi.lift_comp_π]
      change E.obj.map (β i).op =
        (Pi.lift (fun j ↦ E.obj.map (β j).op)) ≫
          Pi.π (fun j ↦ E.obj.obj (op (componentTest (W j) V.unop))) i
      rw [Pi.lift_comp_π]
    have : IsIso (ev.map φ ≫ (PreservesProduct.iso ev R).hom) := by
      rw [hw]
      exact hiso
    have : IsIso (ev.map φ) := by
      exact IsIso.of_isIso_comp_right _ (PreservesProduct.iso ev R).hom
    exact this
  have hφ' : ∀ V, IsIso
      (((sheafToPresheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}).map φ).app V) := hφ
  have : IsIso ((sheafToPresheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}).map φ) :=
    NatIso.isIso_of_isIso_app _
  have : IsIso φ := isIso_of_reflects_iso φ
    (sheafToPresheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
  exact ⟨asIso φ⟩

open CategoryTheory.Limits Opposite in
/-- Finite products of constant set sheaves are constant, by left exact sheafification. -/
private theorem constant_product {C : Type*} [Category* C]
    (J : GrothendieckTopology C) [HasSheafify J (Type (u + 1))]
    (n : ℕ) (F : Fin n → Sheaf J (Type (u + 1)))
    (hF : ∀ i, (F i).IsConstant J) : (∏ᶜ F).IsConstant J := by
  classical
  have : HasProductsOfShape (Fin n) (Cᵒᵖ ⥤ Type (u + 1)) :=
    functorCategoryHasLimitsOfShape
  have : HasProductsOfShape (Fin n) (Sheaf J (Type (u + 1))) :=
    hasLimitsOfShape_of_hasLimitsOfShape_createsLimitsOfShape
      (sheafToPresheaf J (Type (u + 1)))
  have he (i : Fin n) := @Sheaf.mem_essImage_of_isConstant _ _ J _ _ _ (F i) (hF i)
  choose A e using he
  exact Sheaf.isConstant_of_iso J
    (Pi.mapIso (fun i ↦ (e i).some.symm) ≪≫
      (PreservesProduct.iso (constantSheaf J (Type (u + 1))) A).symm)

open CategoryTheory.Limits Opposite in
/-- Constancy of a localized restriction persists under further localization. -/
private theorem constant_over_map {T : Scheme.{u}}
    (F : Sheaf T.smallEtaleTopology (Type (u + 1)))
    {U V : T.Etale} (f : U ⟶ V)
    (hF : (F.over V).IsConstant (T.smallEtaleTopology.over V)) :
    (F.over U).IsConstant (T.smallEtaleTopology.over U) := by
  have := hF
  obtain ⟨A, ⟨e⟩⟩ := (F.over V).mem_essImage_of_isConstant
  let G := Over.map f
  let J := T.smallEtaleTopology.over U
  let K := T.smallEtaleTopology.over V
  let c : constantSheaf K (Type (u + 1)) ⋙ G.sheafPushforwardContinuous _ J K ≅
      constantSheaf J (Type (u + 1)) :=
    Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft (Functor.const (Over V)ᵒᵖ)
        (G.pushforwardContinuousSheafificationCompatibility (Type (u + 1)) J K).symm ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (Functor.constCompWhiskeringLeftIso _ G.op)
        (presheafToSheaf J (Type (u + 1)))
  exact Sheaf.isConstant_of_iso _
    ((F.pushforwardOverMapIso f).symm ≪≫
      (G.sheafPushforwardContinuous _ J K).mapIso e.symm ≪≫ c.app A)

set_option backward.isDefEq.respectTransparency false in
open CategoryTheory.Limits Opposite in
/-- A finite family of locally constant sheaves has a common trivializing etale cover. -/
private theorem simultaneous_constant_cover {T : Scheme.{u}}
    (n : ℕ) (F : Fin n → Sheaf T.smallEtaleTopology (Type (u + 1)))
    (hF : ∀ i, IsLocallyConstantEtaleSheafOfSets (F i)) :
    ∃ 𝒰 : Cover.{u} etalePrecoverage T, ∀ j : 𝒰.I₀, ∀ i : Fin n,
      ((F i).over (𝒰.etalePrecoverageToEtale j)).IsConstant
        (T.smallEtaleTopology.over (𝒰.etalePrecoverageToEtale j)) := by
  have : etalePrecoverage.{u}.IsStableUnderBaseChange :=
    inferInstanceAs (precoverage @Etale).IsStableUnderBaseChange
  have : etalePrecoverage.{u}.IsStableUnderComposition :=
    inferInstanceAs (precoverage @Etale).IsStableUnderComposition
  induction n with
  | zero =>
    have : etalePrecoverage.{u}.HasIsos := inferInstanceAs (precoverage @Etale).HasIsos
    exact ⟨.singleton (𝟙 T) (Precoverage.mem_coverings_of_isIso _),
      fun _ i ↦ Fin.elim0 i⟩
  | succ n ih =>
    obtain ⟨𝒰, h𝒰⟩ := hF 0
    obtain ⟨𝒱, h𝒱⟩ := ih (fun i ↦ F i.succ) (fun i ↦ hF i.succ)
    refine ⟨𝒰.bind (fun i ↦ 𝒱.pullback₂ (𝒰.f i)), fun ⟨j, k⟩ i ↦ ?_⟩
    refine Fin.cases ?_ (fun i ↦ ?_) i
    · exact constant_over_map (F 0)
        (MorphismProperty.Over.homMk (B := 𝒰.etalePrecoverageToEtale j)
          (pullback.snd (𝒱.f k) (𝒰.f j)) rfl) (h𝒰 j)
    · exact constant_over_map (F i.succ)
        (MorphismProperty.Over.homMk (B := 𝒱.etalePrecoverageToEtale k)
          (pullback.fst (𝒱.f k) (𝒰.f j))
          pullback.condition) (h𝒱 k i)

open CategoryTheory.Limits Opposite in
/-- Restrict to a common cover, then commute restriction with the finite product. -/
private theorem locallyConstant_product {T : Scheme.{u}}
    (n : ℕ) (F : Fin n → Sheaf T.smallEtaleTopology (Type (u + 1)))
    (hF : ∀ i, IsLocallyConstantEtaleSheafOfSets (F i)) :
    IsLocallyConstantEtaleSheafOfSets (∏ᶜ F) := by
  obtain ⟨𝒰, h𝒰⟩ := simultaneous_constant_cover n F hF
  refine ⟨𝒰, fun j ↦ ?_⟩
  have := constant_product (T.smallEtaleTopology.over (𝒰.etalePrecoverageToEtale j))
    n (fun i ↦ (F i).over (𝒰.etalePrecoverageToEtale j)) (h𝒰 j)
  exact Sheaf.isConstant_congr _
    (PreservesProduct.iso
      (T.smallEtaleTopology.overPullback (Type (u + 1))
        (𝒰.etalePrecoverageToEtale j)) F).symm

/-- Assemble locally constant component direct images along a finite disjoint open cover.
Source: smooth purity blueprint, `sk-prop-sf-cbc`, final paragraph of
`lem-weil-pbc-finite-pushforward-generic-constructible`.
(blueprint: lem-weil-pbc-disjoint-components-locally-constant-image).

Proof: For each etale test scheme over Y, base change the disjoint open cover of X.
The sheaf axiom identifies sections over the resulting scheme with the product of
sections over these disjoint components: intersections are empty and an abelian sheaf
has a unique section on the empty scheme. These restriction identifications commute
with maps of test schemes, giving an isomorphism from the underlying direct image to
the finite product of the underlying component direct images. Choose a trivializing
etale cover for each factor. Their finite fibre-product refinement covers Y. On every
member all factors are constant; the constant-sheaf functor preserves finite products
because etale sheafification is left exact. Hence their product is constant. Restrict
the displayed isomorphism to this refinement and transport constancy. For n = 0 the
cover condition implies X is empty; every test-object pullback is empty, so direct
image is the terminal set sheaf, the constant singleton sheaf. -/
theorem isLocallyConstant_disjoint_components_directImage
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    (n : ℕ) (W : Fin n → X.Opens)
    (hcover : (⨆ i, W i) = ⊤)
    (hdisjoint : Pairwise (fun i j ↦ Disjoint (W i) (W j)))
    (E : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    (hcomponents : ∀ i, IsLocallyConstantEtaleSheafOfSets
      ((sheafCompose Y.smallEtaleTopology
        (CategoryTheory.forget AddCommGrpCat.{u + 1})).obj
          ((Etale.lowerStar AddCommGrpCat.{u + 1} ((W i).ι ≫ f)).obj
            ((Etale.upperStar AddCommGrpCat.{u + 1} (W i).ι).obj E)))) :
    IsLocallyConstantEtaleSheafOfSets
      ((sheafCompose Y.smallEtaleTopology
        (CategoryTheory.forget AddCommGrpCat.{u + 1})).obj
          ((Etale.lowerStar AddCommGrpCat.{u + 1} f).obj E)) := by
  obtain ⟨e⟩ := component_source_product n W hcover hdisjoint E
  let R (i : Fin n) := (Etale.lowerStar AddCommGrpCat.{u + 1} (W i).ι).obj
    ((Etale.localizationRestriction AddCommGrpCat.{u + 1}
      (W i).ι inferInstance).obj E)
  let S (i : Fin n) := (Etale.lowerStar AddCommGrpCat.{u + 1} ((W i).ι ≫ f)).obj
    ((Etale.upperStar AddCommGrpCat.{u + 1} (W i).ι).obj E)
  let P := Etale.lowerStar AddCommGrpCat.{u + 1} f
  let Q := sheafCompose Y.smallEtaleTopology
    (CategoryTheory.forget AddCommGrpCat.{u + 1})
  have := (Etale.upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} f).isRightAdjoint
  have : Limits.PreservesLimitsOfShape (Discrete (Fin n))
      (Q ⋙ sheafToPresheaf Y.smallEtaleTopology (Type (u + 1))) := by
    change Limits.PreservesLimitsOfShape (Discrete (Fin n))
      (sheafToPresheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1} ⋙
        (Functor.whiskeringRight Y.Etaleᵒᵖ AddCommGrpCat.{u + 1} (Type (u + 1))).obj
          (CategoryTheory.forget AddCommGrpCat.{u + 1}))
    infer_instance
  have : Limits.PreservesLimitsOfShape (Discrete (Fin n)) Q :=
    Limits.preservesLimitsOfShape_of_reflects_of_preserves Q
      (sheafToPresheaf Y.smallEtaleTopology (Type (u + 1)))
  let c (i : Fin n) : P.obj (R i) ≅ S i :=
    (Etale.lowerStarComp AddCommGrpCat.{u + 1} (W i).ι f).app _ ≪≫
      (Etale.lowerStar AddCommGrpCat.{u + 1} ((W i).ι ≫ f)).mapIso
        ((Etale.upperStarIsoLocalizationRestriction AddCommGrpCat.{u + 1}
          (W i).ι inferInstance).app E).symm
  let e' := Q.mapIso
    (P.mapIso e ≪≫ Limits.PreservesProduct.iso P R ≪≫ Limits.Pi.mapIso c) ≪≫
    Limits.PreservesProduct.iso Q S
  obtain ⟨𝒰, h𝒰⟩ := locallyConstant_product n _ hcomponents
  refine ⟨𝒰, fun i ↦ ?_⟩
  have := h𝒰 i
  exact Sheaf.isConstant_congr _
    ((Y.smallEtaleTopology.overPullback (Type (u + 1))
      (𝒰.etalePrecoverageToEtale i)).mapIso e'.symm)

end AlgebraicGeometry.Scheme
