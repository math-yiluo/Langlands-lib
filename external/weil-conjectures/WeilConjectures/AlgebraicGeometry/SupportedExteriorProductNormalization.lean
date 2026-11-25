/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Supported.SupportedExteriorProduct
public import WeilConjectures.AlgebraicGeometry.KunnethGlobalSections
public import WeilConjectures.SixFunctors.Etale.SupportCohomology
public import WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Defs
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.GlobalSections
public import WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.StrictlyHenselianUnit
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.ShortExactPullback
public import WeilConjectures.AlgebraicGeometry.Supported.SupportedExteriorProduct

/-!
# Exterior products of supported sections, derived on resolutions

Source: literature/blueprint/latest/blueprint/part-duality-trace-formula/
sec-smooth-purity/sec-the-trace-map-of-affine-space/sk-prop-an/
def-pur-supported-exterior-product.md (blueprint: proposition-purity-vector-bundles).

First pull back and tensor ordinary supported sections. Totalize this pairing with the
cochain sign convention, then derive it using K-flat tensor and the injective-resolution
units of the recorded support functors. The resolution characterization determines the
resulting morphism uniquely. No adjunction for supported coefficient objects is used.
-/

@[expose] public section

set_option autoImplicit false
set_option linter.unusedSectionVars false

universe u v

open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite

namespace AlgebraicGeometry.Etale

section Ordinary

variable (C : Type v) [Category.{u + 1} C] [Abelian C]
  [IsGrothendieckAbelian.{u + 1} C] [MonoidalCategory C] [MonoidalPreadditive C]
  [SymmetricCategory C] [MonoidalClosed C] [Abelian.HasFunctorialFlatResolution C]
  [HasSmallSiteSheafify C]

omit [MonoidalPreadditive C] [Abelian.HasFunctorialFlatResolution C] [HasSmallSiteSheafify C] in
/-- Naturality of the pointwise tensor of two sections.
Source: the supported-section pairing of the nested blueprint unit cited above
(blueprint: proposition-purity-vector-bundles).
Proof: restrictions of the two global sections commute with every site morphism;
tensor those two identities and use naturality of the sheafification tensor map. -/
theorem exteriorSections_naturality (T : Scheme.{u})
    (F G : Sheaf T.smallEtaleTopology C) {U V : T.Etaleᵒᵖ} (a : U ⟶ V) :
    ((Functor.const T.Etaleᵒᵖ).obj
        ((Sheaf.Γ T.smallEtaleTopology C).obj F ⊗
          (Sheaf.Γ T.smallEtaleTopology C).obj G)).map a ≫
        (tensorHom (Sheaf.ΓRes F V) (Sheaf.ΓRes G V) ≫
          (Functor.LaxMonoidal.μ (sheafToPresheaf T.smallEtaleTopology C) F G).app V) =
      (tensorHom (Sheaf.ΓRes F U) (Sheaf.ΓRes G U) ≫
        (Functor.LaxMonoidal.μ (sheafToPresheaf T.smallEtaleTopology C) F G).app U) ≫
        (F ⊗ G).obj.map a := by
  have h3 := (Functor.LaxMonoidal.μ (sheafToPresheaf T.smallEtaleTopology C) F G).naturality a
  simp only [Functor.const_obj_map]
  rw [← Sheaf.ΓRes_map F a, ← Sheaf.ΓRes_map G a, ← tensorHom_comp_tensorHom]
  erw [Category.id_comp]
  rw [Category.assoc, Category.assoc]
  exact congrArg (_ ≫ ·) h3

/-- Tensor two global sections, using the actual pointwise tensor followed by
sheafification. Source: the nested blueprint unit cited above
(blueprint: proposition-purity-vector-bundles). -/
noncomputable def exteriorSectionsTensor (T : Scheme.{u})
    (F G : Sheaf T.smallEtaleTopology C) :
    (Sheaf.Γ T.smallEtaleTopology C).obj F ⊗
      (Sheaf.Γ T.smallEtaleTopology C).obj G ⟶
        (Sheaf.Γ T.smallEtaleTopology C).obj (F ⊗ G) :=
  Sheaf.ΓHomEquiv
    { app := fun U ↦ tensorHom (Sheaf.ΓRes F U) (Sheaf.ΓRes G U) ≫
        (Functor.LaxMonoidal.μ (sheafToPresheaf T.smallEtaleTopology C) F G).app U
      naturality := fun _ _ a ↦ exteriorSections_naturality C T F G a }

variable {B X Y Z W : Scheme.{u}}
  (f : X ⟶ B) (g : Y ⟶ B) (i : Z ⟶ X) (j : W ⟶ Y)
  [IsClosedImmersion i] [IsClosedImmersion j]

/-- Pull back and tensor ordinary sections from the two factors.
Source: the nested blueprint unit cited above (blueprint: proposition-purity-vector-bundles). -/
noncomputable def exteriorSectionsMap
    (F : Sheaf X.smallEtaleTopology C) (G : Sheaf Y.smallEtaleTopology C) :
    (Sheaf.Γ X.smallEtaleTopology C).obj F ⊗
      (Sheaf.Γ Y.smallEtaleTopology C).obj G ⟶
        (Sheaf.Γ (pullback f g).smallEtaleTopology C).obj
          ((upperStar C (pullback.fst f g)).obj F ⊗
            (upperStar C (pullback.snd f g)).obj G) :=
  tensorHom (globalSectionsUpperStarMap C (pullback.fst f g) F)
      (globalSectionsUpperStarMap C (pullback.snd f g) G) ≫
    exteriorSectionsTensor C (pullback f g) _ _

/-- The adjoint of a cone map of constant presheaves composed with the restriction recovers the
component of the map. -/
private lemma ΓHomEquiv_comp_ΓRes {D : Type*} [Category D] (J : GrothendieckTopology D)
    (A : Type*) [Category A] [HasWeakSheafify J A] [HasGlobalSectionsFunctor J A]
    {M : A} {F : Sheaf J A} (h : (Functor.const Dᵒᵖ).obj M ⟶ F.obj) (U : Dᵒᵖ) :
    Sheaf.ΓHomEquiv h ≫ F.ΓRes U = h.app U := by
  have := congr_app (Sheaf.ΓHomEquiv_naturality_left_symm (Sheaf.ΓHomEquiv h) (𝟙 _)) U
  rw [Category.comp_id, Equiv.symm_apply_apply] at this
  rw [this]
  rfl

omit [MonoidalPreadditive C] [Abelian.HasFunctorialFlatResolution C] [HasSmallSiteSheafify C] in
/-- Restriction of the tensor of two global sections to an étale scheme. -/
private lemma exteriorSectionsTensor_comp_ΓRes (T : Scheme.{u})
    (F G : Sheaf T.smallEtaleTopology C) (U : T.Etaleᵒᵖ) :
    exteriorSectionsTensor C T F G ≫ (F ⊗ G).ΓRes U =
      tensorHom (Sheaf.ΓRes F U) (Sheaf.ΓRes G U) ≫
        (Functor.LaxMonoidal.μ (sheafToPresheaf T.smallEtaleTopology C) F G).app U :=
  ΓHomEquiv_comp_ΓRes _ _ _ U

private lemma ΓNatIsoSheafSections_hom_app_eq_ΓRes' {D : Type*} [Category D]
    (J : GrothendieckTopology D) (A : Type*) [Category A]
    [HasWeakSheafify J A] [HasTerminal D] {T : D} (hT : IsTerminal T) (F : Sheaf J A) :
    (Sheaf.ΓNatIsoSheafSections J A hT).hom.app F = F.ΓRes (op T) := by
  simp only [Sheaf.ΓNatIsoSheafSections, Sheaf.ΓRes, Sheaf.coneΓ, Sheaf.ΓHomEquiv,
    Adjunction.rightAdjointUniq, conjugateIsoEquiv_apply_hom, conjugateEquiv_apply_app]
  erw [Equiv.symm_trans_apply, Equiv.symm_symm, Adjunction.homEquiv_counit,
    Adjunction.homEquiv_unit]
  simp [constantSheafAdj, Adjunction.comp_unit_app]

omit [MonoidalCategory C] [MonoidalPreadditive C] [SymmetricCategory C] [MonoidalClosed C]
  [Abelian.HasFunctorialFlatResolution C] [HasSmallSiteSheafify C] in
/-- Compatibility of the pullback map on global sections with restriction to an étale
`S`-scheme `W` mapping to an étale `T`-scheme `V`. -/
private theorem globalSectionsUpperStarMap_comp_ΓRes
    {T S : Scheme.{u}} (h : S ⟶ T) (M : Sheaf T.smallEtaleTopology C)
    (V : T.Etale) (W : S.Etale) (φ : W.left ⟶ V.left) (hφ : φ ≫ V.hom = W.hom ≫ h) :
    globalSectionsUpperStarMap C h M ≫ ((upperStar C h).obj M).ΓRes (op W) =
      M.ΓRes (op V) ≫ ((upperStarLowerStarAdjunction C h).unit.app M).hom.app (op V) ≫
        ((upperStar C h).obj M).obj.map (homToPullback h φ hφ).op := by
  let N := (upperStar C h).obj M
  let e := Sheaf.ΓNatIsoSheafSections S.smallEtaleTopology C terminalIsTerminal
  have he : e.inv.app N ≫ N.ΓRes (op W) = N.obj.map (terminal.from W).op := by
    apply (cancel_epi (e.hom.app N)).1
    rw [← Category.assoc, Iso.hom_inv_id_app, Category.id_comp,
      ΓNatIsoSheafSections_hom_app_eq_ΓRes']
    exact (Sheaf.ΓRes_map N (terminal.from W).op).symm
  have hm : terminal.from W ≫ (PreservesTerminal.iso h.Etale).inv =
      homToPullback h φ hφ ≫ h.Etale.map (terminal.from V) :=
    (isLimitOfPreserves h.Etale (limit.isLimit (Functor.empty T.Etale))).hom_ext
      (fun j ↦ isEmptyElim j)
  simp only [globalSectionsUpperStarMap, Category.assoc]
  change _ ≫ _ ≫ N.obj.map _ ≫ e.inv.app N ≫ N.ΓRes (op W) = _
  rw [he, ← N.obj.map_comp, ← op_comp, hm, op_comp, N.obj.map_comp]
  have hu := ((upperStarLowerStarAdjunction C h).unit.app M).hom.naturality
    (terminal.from V).op
  change M.obj.map (terminal.from V).op ≫
      ((upperStarLowerStarAdjunction C h).unit.app M).hom.app (op V) =
    ((upperStarLowerStarAdjunction C h).unit.app M).hom.app (op (⊤_ T.Etale)) ≫
      N.obj.map (h.Etale.map (terminal.from V)).op at hu
  change (Sheaf.ΓNatIsoSheafSections T.smallEtaleTopology C terminalIsTerminal).hom.app M ≫
      ((upperStarLowerStarAdjunction C h).unit.app M).hom.app (op (⊤_ T.Etale)) ≫ _ ≫ _ = _
  rw [← reassoc_of% hu, ΓNatIsoSheafSections_hom_app_eq_ΓRes', Sheaf.ΓRes_map_assoc]

omit [MonoidalCategory C] [MonoidalPreadditive C] [SymmetricCategory C] [MonoidalClosed C]
  [Abelian.HasFunctorialFlatResolution C] [HasSmallSiteSheafify C] in
/-- Sections supported away from an open `U` die after pullback and restriction to any étale
scheme mapping into the pullback of `U`. -/
private lemma supportι_comp_globalSectionsUpperStarMap_comp_ΓRes
    {T S : Scheme.{u}} (h : S ⟶ T) (M : Sheaf T.smallEtaleTopology C)
    (V : T.Etale) (W : S.Etale) (φ : W.left ⟶ V.left) (hφ : φ ≫ V.hom = W.hom ≫ h) :
    (Sheaf.ΓSupportι T.smallEtaleTopology C (op V)).app M ≫
      globalSectionsUpperStarMap C h M ≫ ((upperStar C h).obj M).ΓRes (op W) = 0 := by
  rw [globalSectionsUpperStarMap_comp_ΓRes C h M V W φ hφ,
    Sheaf.ΓSupportι_app_comp_ΓRes_assoc, zero_comp]

/-- Some étale neighbourhood of each point of an étale scheme maps into any open containing the
image of the point. -/
private lemma exists_etale_arrow_range_subset {P : Scheme.{u}} (V : P.Etale) (O : P.Opens)
    (x : V.left) (hx : V.hom x ∈ O) :
    ∃ (Y : P.Etale) (f : Y ⟶ V) (y : Y.left),
      (∀ z : Y.left, Y.hom z ∈ O) ∧ f.left y = x ∧ Etale f.left := by
  have : Etale V.hom := V.prop
  refine ⟨Scheme.Etale.mk ((V.hom ⁻¹ᵁ O).ι ≫ V.hom),
    MorphismProperty.Over.homMk (V.hom ⁻¹ᵁ O).ι rfl, ⟨x, hx⟩, fun z ↦ z.2, rfl,
    inferInstance⟩

/-- The tensor of pulled-back supported sections vanishes off the product support.
Source: the nested blueprint unit cited above (blueprint: proposition-purity-vector-bundles).
Proof: the complement of the product support is covered by the inverse images of the
two complements. On the first open the first factor restricts to zero, and on the
second the second factor does. Tensoring a zero morphism gives zero; the sheaf axiom
then gives vanishing on their union. -/
theorem exteriorSections_support (F : Sheaf X.smallEtaleTopology C)
    (G : Sheaf Y.smallEtaleTopology C) :
    (tensorHom
        ((Sheaf.ΓSupportι X.smallEtaleTopology C
          (op (Scheme.Etale.mk i.openComplement.ι))).app F)
        ((Sheaf.ΓSupportι Y.smallEtaleTopology C
          (op (Scheme.Etale.mk j.openComplement.ι))).app G) ≫
      exteriorSectionsMap C f g F G) ≫
      Sheaf.ΓRes _ (op (Scheme.Etale.mk
        (supportedProductImmersion f g i j).openComplement.ι)) = 0 := by
  classical
  set V₀ : (pullback f g).Etale :=
    Scheme.Etale.mk (supportedProductImmersion f g i j).openComplement.ι with hV₀
  have hc : (supportedProductImmersion f g i j).openComplement =
      pullback.fst f g ⁻¹ᵁ i.openComplement ⊔
        pullback.snd f g ⁻¹ᵁ j.openComplement := by
    apply TopologicalSpace.Opens.ext
    simp [Scheme.Hom.coe_openComplement, supportedProductImmersion,
      Scheme.Pullback.range_map, Set.compl_inter, Set.preimage_compl]
  let S : Sieve V₀ :=
    { arrows := fun W _ ↦
        (∀ y : W.left, W.hom y ∈ pullback.fst f g ⁻¹ᵁ i.openComplement) ∨
        (∀ y : W.left, W.hom y ∈ pullback.snd f g ⁻¹ᵁ j.openComplement)
      downward_closed := fun {W W'} {w} hw g' ↦ by
        rcases hw with hw | hw
        · refine Or.inl fun y ↦ ?_
          rw [← MorphismProperty.Over.w g']
          exact hw (g'.left y)
        · refine Or.inr fun y ↦ ?_
          rw [← MorphismProperty.Over.w g']
          exact hw (g'.left y) }
  have hS : S ∈ (pullback f g).smallEtaleTopology V₀ := by
    rw [Scheme.smallEtaleTopology,
      Scheme.smallGrothendieckTopology_eq_toGrothendieck_smallPretopology _ le_rfl]
    refine (Scheme.mem_toGrothendieck_smallPretopology (P := @Etale) (Q := @Etale) V₀ S).2 ?_
    intro x
    have hx : V₀.hom x ∈ Set.range (supportedProductImmersion f g i j).openComplement.ι :=
      Set.mem_range_self x
    rw [Scheme.Opens.range_ι, hc] at hx
    rcases hx with hx | hx
    · obtain ⟨Y, a, y, hY, hya, hE⟩ :=
        exists_etale_arrow_range_subset V₀ (pullback.fst f g ⁻¹ᵁ i.openComplement) x hx
      exact ⟨Y, a, y, Or.inl hY, hE, hya⟩
    · obtain ⟨Y, a, y, hY, hya, hE⟩ :=
        exists_etale_arrow_range_subset V₀ (pullback.snd f g ⁻¹ᵁ j.openComplement) x hx
      exact ⟨Y, a, y, Or.inr hY, hE, hya⟩
  refine Presheaf.IsSheaf.hom_ext (((upperStar C (pullback.fst f g)).obj F ⊗
    (upperStar C (pullback.snd f g)).obj G).property) ⟨S, hS⟩ _ 0 ?_
  rintro ⟨W, w, hw⟩
  rw [Category.assoc, Sheaf.ΓRes_map, zero_comp]
  have key {A₁ A₂ : C} (a : A₁ ⟶ (Sheaf.Γ X.smallEtaleTopology C).obj F)
      (b : A₂ ⟶ (Sheaf.Γ Y.smallEtaleTopology C).obj G) :
      (tensorHom a b ≫ exteriorSectionsMap C f g F G) ≫
        ((upperStar C (pullback.fst f g)).obj F ⊗
          (upperStar C (pullback.snd f g)).obj G).ΓRes (op W) =
      tensorHom (a ≫ globalSectionsUpperStarMap C (pullback.fst f g) F ≫
          ((upperStar C (pullback.fst f g)).obj F).ΓRes (op W))
        (b ≫ globalSectionsUpperStarMap C (pullback.snd f g) G ≫
          ((upperStar C (pullback.snd f g)).obj G).ΓRes (op W)) ≫
        (Functor.LaxMonoidal.μ (sheafToPresheaf (pullback f g).smallEtaleTopology C) _ _).app
          (op W) := by
    rw [exteriorSectionsMap, Category.assoc, Category.assoc, exteriorSectionsTensor_comp_ΓRes,
      tensorHom_comp_tensorHom_assoc, tensorHom_comp_tensorHom_assoc]
    simp only [Category.assoc]
  rw [key]
  rcases hw with hw | hw
  · have hr : Set.range (W.hom ≫ pullback.fst f g) ⊆ Set.range i.openComplement.ι := by
      rw [Scheme.Opens.range_ι]
      rintro _ ⟨y, rfl⟩
      rw [Scheme.Hom.comp_apply]
      exact hw y
    have h0 := supportι_comp_globalSectionsUpperStarMap_comp_ΓRes C (pullback.fst f g) F
      (Scheme.Etale.mk i.openComplement.ι) W (IsOpenImmersion.lift _ _ hr)
      (IsOpenImmersion.lift_fac _ _ hr)
    rw [h0, MonoidalPreadditive.zero_tensor, zero_comp]
  · have hr : Set.range (W.hom ≫ pullback.snd f g) ⊆ Set.range j.openComplement.ι := by
      rw [Scheme.Opens.range_ι]
      rintro _ ⟨y, rfl⟩
      rw [Scheme.Hom.comp_apply]
      exact hw y
    have h0 := supportι_comp_globalSectionsUpperStarMap_comp_ΓRes C (pullback.snd f g) G
      (Scheme.Etale.mk j.openComplement.ι) W (IsOpenImmersion.lift _ _ hr)
      (IsOpenImmersion.lift_fac _ _ hr)
    rw [h0, MonoidalPreadditive.tensor_zero, zero_comp]

/-- The ordinary supported exterior product is the kernel lift of the pullback and
tensor of sections. Source: the nested blueprint unit cited above
(blueprint: proposition-purity-vector-bundles). -/
noncomputable def exteriorSupportedSections
    (F : Sheaf X.smallEtaleTopology C) (G : Sheaf Y.smallEtaleTopology C) :
    (globalSectionsWithSupport C i).obj F ⊗ (globalSectionsWithSupport C j).obj G ⟶
      (globalSectionsWithSupport C (supportedProductImmersion f g i j)).obj
        ((upperStar C (pullback.fst f g)).obj F ⊗
          (upperStar C (pullback.snd f g)).obj G) :=
  kernel.lift
      (Sheaf.ΓRes _ (op (Scheme.Etale.mk
        (supportedProductImmersion f g i j).openComplement.ι)))
      (tensorHom
        ((Sheaf.ΓSupportι X.smallEtaleTopology C
          (op (Scheme.Etale.mk i.openComplement.ι))).app F)
        ((Sheaf.ΓSupportι Y.smallEtaleTopology C
          (op (Scheme.Etale.mk j.openComplement.ι))).app G) ≫
        exteriorSectionsMap C f g F G)
      (exteriorSections_support C f g i j F G) ≫
    (PreservesKernel.iso ((evaluation _ C).obj _)
      (Sheaf.natTransΓRes (pullback f g).smallEtaleTopology C
        (op (Scheme.Etale.mk
          (supportedProductImmersion f g i j).openComplement.ι)))).inv


omit [MonoidalPreadditive C] [Abelian.HasFunctorialFlatResolution C] [HasSmallSiteSheafify C] in
/-- The pointwise tensor of global sections is natural in both sheaves. -/
@[reassoc]
theorem exteriorSectionsTensor_naturality (T : Scheme.{u})
    {F F' G G' : Sheaf T.smallEtaleTopology C} (a : F ⟶ F') (b : G ⟶ G') :
    tensorHom ((Sheaf.Γ T.smallEtaleTopology C).map a)
        ((Sheaf.Γ T.smallEtaleTopology C).map b) ≫ exteriorSectionsTensor C T F' G' =
      exteriorSectionsTensor C T F G ≫ (Sheaf.Γ T.smallEtaleTopology C).map (tensorHom a b) := by
  rw [exteriorSectionsTensor, exteriorSectionsTensor, ← Sheaf.ΓHomEquiv_naturality_left,
    ← Sheaf.ΓHomEquiv_naturality_right]
  congr 1
  ext U
  have hμ := congr_app (Functor.LaxMonoidal.μ_natural
    (sheafToPresheaf T.smallEtaleTopology C) a b) U
  simp only [NatTrans.comp_app] at hμ
  simp only [NatTrans.comp_app, Functor.const_map_app]
  rw [tensorHom_comp_tensorHom_assoc, Sheaf.ΓRes_naturality, Sheaf.ΓRes_naturality,
    ← tensorHom_comp_tensorHom_assoc, Category.assoc]
  congr 1

/-- The pullback and tensor of sections is natural in both sheaves. -/
@[reassoc]
theorem exteriorSectionsMap_naturality
    {F F' : Sheaf X.smallEtaleTopology C} {G G' : Sheaf Y.smallEtaleTopology C}
    (a : F ⟶ F') (b : G ⟶ G') :
    tensorHom ((Sheaf.Γ X.smallEtaleTopology C).map a)
        ((Sheaf.Γ Y.smallEtaleTopology C).map b) ≫ exteriorSectionsMap C f g F' G' =
      exteriorSectionsMap C f g F G ≫ (Sheaf.Γ (pullback f g).smallEtaleTopology C).map
        (tensorHom ((upperStar C (pullback.fst f g)).map a)
          ((upperStar C (pullback.snd f g)).map b)) := by
  rw [exteriorSectionsMap, exteriorSectionsMap, tensorHom_comp_tensorHom_assoc,
    globalSectionsUpperStarMap_naturality, globalSectionsUpperStarMap_naturality,
    ← tensorHom_comp_tensorHom, Category.assoc, exteriorSectionsTensor_naturality,
    Category.assoc]

/-- The supported exterior product of sections followed by the inclusion of supported
sections is the pullback and tensor of the two included sections. -/
@[reassoc]
theorem exteriorSupportedSections_ΓSupportι
    (F : Sheaf X.smallEtaleTopology C) (G : Sheaf Y.smallEtaleTopology C) :
    exteriorSupportedSections C f g i j F G ≫
        (Sheaf.ΓSupportι (pullback f g).smallEtaleTopology C
          (op (Scheme.Etale.mk (supportedProductImmersion f g i j).openComplement.ι))).app
          ((upperStar C (pullback.fst f g)).obj F ⊗ (upperStar C (pullback.snd f g)).obj G) =
      tensorHom
        ((Sheaf.ΓSupportι X.smallEtaleTopology C
          (op (Scheme.Etale.mk i.openComplement.ι))).app F)
        ((Sheaf.ΓSupportι Y.smallEtaleTopology C
          (op (Scheme.Etale.mk j.openComplement.ι))).app G) ≫
        exteriorSectionsMap C f g F G := by
  rw [exteriorSupportedSections, Category.assoc]
  erw [PreservesKernel.iso_inv_ι]
  exact kernel.lift_ι _ _ _

/-- The supported exterior product of sections is natural in both sheaves. -/
@[reassoc]
theorem exteriorSupportedSections_naturality
    {F F' : Sheaf X.smallEtaleTopology C} {G G' : Sheaf Y.smallEtaleTopology C}
    (a : F ⟶ F') (b : G ⟶ G') :
    tensorHom ((globalSectionsWithSupport C i).map a) ((globalSectionsWithSupport C j).map b) ≫
        exteriorSupportedSections C f g i j F' G' =
      exteriorSupportedSections C f g i j F G ≫
        (globalSectionsWithSupport C (supportedProductImmersion f g i j)).map
          (tensorHom ((upperStar C (pullback.fst f g)).map a)
            ((upperStar C (pullback.snd f g)).map b)) := by
  rw [← cancel_mono ((Sheaf.ΓSupportι (pullback f g).smallEtaleTopology C
    (op (Scheme.Etale.mk (supportedProductImmersion f g i j).openComplement.ι))).app _),
    Category.assoc, exteriorSupportedSections_ΓSupportι, Category.assoc]
  erw [(Sheaf.ΓSupportι (pullback f g).smallEtaleTopology C
    (op (Scheme.Etale.mk (supportedProductImmersion f g i j).openComplement.ι))).naturality]
  rw [reassoc_of% exteriorSupportedSections_ΓSupportι, tensorHom_comp_tensorHom_assoc]
  erw [(Sheaf.ΓSupportι X.smallEtaleTopology C
      (op (Scheme.Etale.mk i.openComplement.ι))).naturality,
    (Sheaf.ΓSupportι Y.smallEtaleTopology C
      (op (Scheme.Etale.mk j.openComplement.ι))).naturality]
  rw [← tensorHom_comp_tensorHom_assoc, exteriorSectionsMap_naturality]

/-- The ordinary exterior product of two cochain complexes, with the signed total
tensor differential. Source: the nested blueprint unit cited above
(blueprint: proposition-purity-vector-bundles). -/
noncomputable def exteriorSectionsComplexTarget
    (P : CochainComplex (Sheaf X.smallEtaleTopology C) ℤ)
    (Q : CochainComplex (Sheaf Y.smallEtaleTopology C) ℤ) :
    CochainComplex (Sheaf (pullback f g).smallEtaleTopology C) ℤ :=
  ((upperStar C (pullback.fst f g)).mapHomologicalComplex (.up ℤ)).obj P ⊗
    ((upperStar C (pullback.snd f g)).mapHomologicalComplex (.up ℤ)).obj Q

section Tensor

open HomologicalComplex in
/-- The differential of the tensor product of two cochain complexes on a summand `(r, s)`. -/
private lemma ιTensorObj_d_tensor {D : Type*} [Category D] [MonoidalCategory D] [Preadditive D]
    [HasZeroObject D] [(curriedTensor D).Additive]
    [∀ X₁ : D, ((curriedTensor D).obj X₁).Additive]
    (K₁ K₂ : CochainComplex D ℤ) [HasTensor K₁ K₂] (r s n : ℤ) (h : r + s = n) :
    ιTensorObj K₁ K₂ r s n h ≫ (tensorObj K₁ K₂).d n (n + 1) =
      ComplexShape.ε₁ (.up ℤ) (.up ℤ) (.up ℤ) (r, s) •
        (K₁.d r (r + 1) ▷ K₂.X s ≫ ιTensorObj K₁ K₂ (r + 1) s (n + 1) (by omega)) +
      ComplexShape.ε₂ (.up ℤ) (.up ℤ) (.up ℤ) (r, s) •
        (K₁.X r ◁ K₂.d s (s + 1) ≫ ιTensorObj K₁ K₂ r (s + 1) (n + 1) (by omega)) := by
  rw [mapBifunctor.d_eq, Preadditive.comp_add, mapBifunctor.ι_D₁, mapBifunctor.ι_D₂,
    mapBifunctor.d₁_eq _ _ _ _ (by simp : (ComplexShape.up ℤ).Rel r (r + 1)) _ _
      (show r + 1 + s = n + 1 by omega),
    mapBifunctor.d₂_eq _ _ _ _ _ (by simp : (ComplexShape.up ℤ).Rel s (s + 1)) _
      (show r + (s + 1) = n + 1 by omega)]
  rfl

end Tensor

/-- The degree `n` component of the totalized supported pairing: the coproduct of the
bidegree pairings followed by the inclusion of that bidegree. -/
private noncomputable def exteriorSupportedSectionsComplexF
    (P : CochainComplex (Sheaf X.smallEtaleTopology C) ℤ)
    (Q : CochainComplex (Sheaf Y.smallEtaleTopology C) ℤ) (n : ℤ) :
    (((globalSectionsWithSupport C i).mapHomologicalComplex (.up ℤ)).obj P ⊗
        ((globalSectionsWithSupport C j).mapHomologicalComplex (.up ℤ)).obj Q).X n ⟶
      (((globalSectionsWithSupport C (supportedProductImmersion f g i j)).mapHomologicalComplex
        (.up ℤ)).obj (exteriorSectionsComplexTarget C f g P Q)).X n :=
  HomologicalComplex.mapBifunctorDesc
    (K₁ := ((globalSectionsWithSupport C i).mapHomologicalComplex (.up ℤ)).obj P)
    (K₂ := ((globalSectionsWithSupport C j).mapHomologicalComplex (.up ℤ)).obj Q)
    (fun r s h ↦ exteriorSupportedSections C f g i j (P.X r) (Q.X s) ≫
      (globalSectionsWithSupport C (supportedProductImmersion f g i j)).map
        (HomologicalComplex.ιTensorObj
          (((upperStar C (pullback.fst f g)).mapHomologicalComplex (.up ℤ)).obj P)
          (((upperStar C (pullback.snd f g)).mapHomologicalComplex (.up ℤ)).obj Q)
          r s n h))

@[reassoc]
private lemma ι_exteriorSupportedSectionsComplexF
    (P : CochainComplex (Sheaf X.smallEtaleTopology C) ℤ)
    (Q : CochainComplex (Sheaf Y.smallEtaleTopology C) ℤ) (r s n : ℤ) (h : r + s = n) :
    HomologicalComplex.ιTensorObj
        (((globalSectionsWithSupport C i).mapHomologicalComplex (.up ℤ)).obj P)
        (((globalSectionsWithSupport C j).mapHomologicalComplex (.up ℤ)).obj Q) r s n h ≫
      exteriorSupportedSectionsComplexF C f g i j P Q n =
    exteriorSupportedSections C f g i j (P.X r) (Q.X s) ≫
      (globalSectionsWithSupport C (supportedProductImmersion f g i j)).map
        (HomologicalComplex.ιTensorObj
          (((upperStar C (pullback.fst f g)).mapHomologicalComplex (.up ℤ)).obj P)
          (((upperStar C (pullback.snd f g)).mapHomologicalComplex (.up ℤ)).obj Q)
          r s n h) := by
  unfold exteriorSupportedSectionsComplexF
  refine HomologicalComplex.ι_mapBifunctorDesc _ r s ?_

/-- Naturality of the supported exterior product in the first sheaf. -/
@[reassoc]
private lemma exteriorSupportedSections_naturality_left'
    {F F' : Sheaf X.smallEtaleTopology C} (a : F ⟶ F') (G : Sheaf Y.smallEtaleTopology C) :
    (globalSectionsWithSupport C i).map a ▷ (globalSectionsWithSupport C j).obj G ≫
        exteriorSupportedSections C f g i j F' G =
      exteriorSupportedSections C f g i j F G ≫
        (globalSectionsWithSupport C (supportedProductImmersion f g i j)).map
          ((upperStar C (pullback.fst f g)).map a ▷ (upperStar C (pullback.snd f g)).obj G) := by
  simpa using exteriorSupportedSections_naturality C f g i j a (𝟙 G)

/-- Naturality of the supported exterior product in the second sheaf. -/
@[reassoc]
private lemma exteriorSupportedSections_naturality_right'
    (F : Sheaf X.smallEtaleTopology C) {G G' : Sheaf Y.smallEtaleTopology C} (b : G ⟶ G') :
    (globalSectionsWithSupport C i).obj F ◁ (globalSectionsWithSupport C j).map b ≫
        exteriorSupportedSections C f g i j F G' =
      exteriorSupportedSections C f g i j F G ≫
        (globalSectionsWithSupport C (supportedProductImmersion f g i j)).map
          ((upperStar C (pullback.fst f g)).obj F ◁ (upperStar C (pullback.snd f g)).map b) := by
  simpa using exteriorSupportedSections_naturality C f g i j (𝟙 F) b

/-- The degreewise supported pairings extend uniquely to the signed total complexes.
Source: the nested blueprint unit cited above (blueprint: proposition-purity-vector-bundles).
Proof: in degree n use the coproduct of the pairings in bidegrees r+s=n, followed by
the inclusion of that bidegree in the sheaf tensor total. Naturality of pullback,
tensor and the support kernel makes this commute with both differentials. The second
one carries the sign (-1)^r on both sides. The coproduct inclusions determine the map. -/
theorem existsUnique_exteriorSupportedSectionsComplex
    (P : CochainComplex (Sheaf X.smallEtaleTopology C) ℤ)
    (Q : CochainComplex (Sheaf Y.smallEtaleTopology C) ℤ) :
    ∃! φ : ((globalSectionsWithSupport C i).mapHomologicalComplex (.up ℤ)).obj P ⊗
        ((globalSectionsWithSupport C j).mapHomologicalComplex (.up ℤ)).obj Q ⟶
      ((globalSectionsWithSupport C (supportedProductImmersion f g i j)).mapHomologicalComplex
        (.up ℤ)).obj (exteriorSectionsComplexTarget C f g P Q),
      ∀ (r s n : ℤ) (h : r + s = n),
        HomologicalComplex.ιTensorObj
            (((globalSectionsWithSupport C i).mapHomologicalComplex (.up ℤ)).obj P)
            (((globalSectionsWithSupport C j).mapHomologicalComplex (.up ℤ)).obj Q) r s n h ≫
          φ.f n =
        exteriorSupportedSections C f g i j (P.X r) (Q.X s) ≫
          (globalSectionsWithSupport C (supportedProductImmersion f g i j)).map
            (HomologicalComplex.ιTensorObj
              (((upperStar C (pullback.fst f g)).mapHomologicalComplex (.up ℤ)).obj P)
              (((upperStar C (pullback.snd f g)).mapHomologicalComplex (.up ℤ)).obj Q)
              r s n h) := by
  classical
  refine ⟨⟨exteriorSupportedSectionsComplexF C f g i j P Q, ?_⟩, ?_, ?_⟩
  · rintro n _ rfl
    apply HomologicalComplex.mapBifunctor.hom_ext
    intro r s h
    rw [ι_exteriorSupportedSectionsComplexF_assoc, Functor.mapHomologicalComplex_obj_d,
      ← Functor.map_comp]
    unfold exteriorSectionsComplexTarget
    erw [ιTensorObj_d_tensor]
    rw [← Category.assoc]
    erw [ιTensorObj_d_tensor]
    simp only [Functor.mapHomologicalComplex_obj_d, Functor.map_add, Functor.map_units_smul,
      Functor.map_comp, Preadditive.add_comp, Linear.units_smul_comp, Category.assoc,
      Linear.comp_units_smul, Preadditive.comp_add, ι_exteriorSupportedSectionsComplexF,
      Preadditive.comp_add]
    congr 2
    · erw [exteriorSupportedSections_naturality_left'_assoc]
      rfl
    · erw [exteriorSupportedSections_naturality_right'_assoc]
      rfl
  · intro r s n h
    exact ι_exteriorSupportedSectionsComplexF C f g i j P Q r s n h
  · intro φ hφ
    ext n : 1
    apply HomologicalComplex.mapBifunctor.hom_ext
    intro r s h
    exact (hφ r s n h).trans (ι_exteriorSupportedSectionsComplexF C f g i j P Q r s n h).symm

/-- The totalized pairing of supported sections. It is the unique chain map whose
bidegree maps are the explicit kernel lifts above; no object is chosen by bare existence.
Source: the nested blueprint unit cited above (blueprint: proposition-purity-vector-bundles). -/
noncomputable def exteriorSupportedSectionsComplex
    (P : CochainComplex (Sheaf X.smallEtaleTopology C) ℤ)
    (Q : CochainComplex (Sheaf Y.smallEtaleTopology C) ℤ) :
    ((globalSectionsWithSupport C i).mapHomologicalComplex (.up ℤ)).obj P ⊗
        ((globalSectionsWithSupport C j).mapHomologicalComplex (.up ℤ)).obj Q ⟶
      ((globalSectionsWithSupport C (supportedProductImmersion f g i j)).mapHomologicalComplex
        (.up ℤ)).obj (exteriorSectionsComplexTarget C f g P Q) :=
  (existsUnique_exteriorSupportedSectionsComplex C f g i j P Q).exists.choose

/-- The canonical comparison from the derived exterior product to the localized
ordinary exterior complex: the two pullback counits followed by the tensor localization map.
Source: the nested blueprint unit cited above (blueprint: proposition-purity-vector-bundles). -/
noncomputable def exteriorProductResolutionComparison
    (P : CochainComplex (Sheaf X.smallEtaleTopology C) ℤ)
    (Q : CochainComplex (Sheaf Y.smallEtaleTopology C) ℤ) :
    externalProduct C f g (DerivedCategory.Q.obj P) (DerivedCategory.Q.obj Q) ⟶
      DerivedCategory.Q.obj (exteriorSectionsComplexTarget C f g P Q) :=
  derivedTensorHom C
      ((upperStar C (pullback.fst f g)).leftDerivedFunctor.map
          ((DerivedCategory.quotientCompQhIso _).inv.app P) ≫
        (upperStar C (pullback.fst f g)).leftDerivedFunctorCounit.app
          ((HomotopyCategory.quotient _ _).obj P) ≫
        DerivedCategory.Qh.map
          (((upperStar C (pullback.fst f g)).mapHomotopyCategoryFactors (.up ℤ)).hom.app P) ≫
        (DerivedCategory.quotientCompQhIso _).hom.app _)
      ((upperStar C (pullback.snd f g)).leftDerivedFunctor.map
          ((DerivedCategory.quotientCompQhIso _).inv.app Q) ≫
        (upperStar C (pullback.snd f g)).leftDerivedFunctorCounit.app
          ((HomotopyCategory.quotient _ _).obj Q) ≫
        DerivedCategory.Qh.map
          (((upperStar C (pullback.snd f g)).mapHomotopyCategoryFactors (.up ℤ)).hom.app Q) ≫
        (DerivedCategory.quotientCompQhIso _).hom.app _) ≫
    Functor.LaxMonoidal.μ DerivedCategory.Q
      (((upperStar C (pullback.fst f g)).mapHomologicalComplex (.up ℤ)).obj P)
      (((upperStar C (pullback.snd f g)).mapHomologicalComplex (.up ℤ)).obj Q)

/-- Inverse image of étale sheaves preserves K-flat complexes.
Missing input: the project only proves this for functorial flat resolutions, under the
hypothesis `Etale.UpperStarPreservesFlat C`
(`AlgebraicGeometry.Etale.kFlat_upperStar_mapHomologicalComplex_obj`). The general
statement, for an arbitrary K-flat complex and an arbitrary coefficient category, needs
the stalkwise description of `g^*` and of the tensor product. -/
theorem kFlat_upperStar_mapHomologicalComplex_obj_of_kFlat {S T : Scheme.{u}} (h : T ⟶ S)
    (K : CochainComplex (Sheaf S.smallEtaleTopology C) ℤ)
    (hK : (HomologicalComplex.quasiIso _ (.up ℤ)).kFlat K) :
    (HomologicalComplex.quasiIso _ (.up ℤ)).kFlat
      (((upperStar C h).mapHomologicalComplex (.up ℤ)).obj K) := by
  sorry

/-- K-flat representatives compute the derived exterior product.
Source: the nested blueprint unit cited above (blueprint: proposition-purity-vector-bundles).
Proof: inverse image is exact and monoidal, so preserves K-flat complexes. Its derived
counit is invertible on K-flat representatives. Tensor localization is invertible on
a pair of K-flat complexes. Thus every factor in the displayed comparison is invertible. -/
theorem isIso_exteriorProductResolutionComparison
    (P : CochainComplex (Sheaf X.smallEtaleTopology C) ℤ)
    (Q : CochainComplex (Sheaf Y.smallEtaleTopology C) ℤ)
    (_hP : (HomologicalComplex.quasiIso _ (.up ℤ)).kFlat P)
    (_hQ : (HomologicalComplex.quasiIso _ (.up ℤ)).kFlat Q) :
    IsIso (exteriorProductResolutionComparison C f g P Q) := by
  have : IsIso (Functor.LaxMonoidal.μ DerivedCategory.Qh
      ((HomotopyCategory.quotient _ (.up ℤ)).obj
        (((upperStar C (pullback.fst f g)).mapHomologicalComplex (.up ℤ)).obj P))
      ((HomotopyCategory.quotient _ (.up ℤ)).obj
        (((upperStar C (pullback.snd f g)).mapHomologicalComplex (.up ℤ)).obj Q))) :=
    DerivedMonoidal.isIso_counit_app_app_of_kFlat_right DerivedCategory.Qh
      (HomotopyCategory.quasiIso _ (.up ℤ)) _ _
      ((HomotopyCategory.kFlat_quotient_obj_iff _).2
        (kFlat_upperStar_mapHomologicalComplex_obj_of_kFlat C (pullback.snd f g) Q _hQ))
  have : IsIso (Functor.LaxMonoidal.μ DerivedCategory.Q
      (((upperStar C (pullback.fst f g)).mapHomologicalComplex (.up ℤ)).obj P)
      (((upperStar C (pullback.snd f g)).mapHomologicalComplex (.up ℤ)).obj Q)) := by
    -- `Q` is lax monoidal as `quotient ⋙ Qh`, transported along an isomorphism.
    change IsIso ((_ ⊗ₘ _) ≫
      (Functor.LaxMonoidal.μ DerivedCategory.Qh _ _ ≫ DerivedCategory.Qh.map _) ≫ _)
    infer_instance
  unfold exteriorProductResolutionComparison derivedTensorHom
  infer_instance

/-- The canonical exterior-product comparison, inverted on K-flat representatives.
Source: the nested blueprint unit cited above (blueprint: proposition-purity-vector-bundles). -/
noncomputable def exteriorProductResolutionIso
    (P : CochainComplex (Sheaf X.smallEtaleTopology C) ℤ)
    (Q : CochainComplex (Sheaf Y.smallEtaleTopology C) ℤ)
    (hP : (HomologicalComplex.quasiIso _ (.up ℤ)).kFlat P)
    (hQ : (HomologicalComplex.quasiIso _ (.up ℤ)).kFlat Q) :
    externalProduct C f g (DerivedCategory.Q.obj P) (DerivedCategory.Q.obj Q) ≅
      DerivedCategory.Q.obj (exteriorSectionsComplexTarget C f g P Q) :=
  letI := isIso_exteriorProductResolutionComparison C f g P Q hP hQ
  asIso (exteriorProductResolutionComparison C f g P Q)

/-- The comparison from termwise supported sections to their injective right derivation.
It is the actual unit of the recorded support functor, and is invertible on injective
support resolutions. Source: the nested blueprint unit cited above
(blueprint: proposition-purity-vector-bundles). -/
noncomputable def exteriorSupportResolutionUnit
    (P : CochainComplex (Sheaf X.smallEtaleTopology C) ℤ) :
    DerivedCategory.Q.obj
        (((globalSectionsWithSupport C i).mapHomologicalComplex (.up ℤ)).obj P) ⟶
      (rightDerivedSectionsWithSupport C i).obj (DerivedCategory.Q.obj P) :=
  (globalSectionsWithSupport C i).rightDerivedFunctorUnitQ P


/-- Resolution normalization of the supported exterior product. On every pair of
K-flat representatives, compare termwise support sections to injective support
resolutions, and totalize the explicit pullback-and-tensor pairing above.
Source: the nested blueprint unit cited above (blueprint: proposition-purity-vector-bundles). -/
def IsResolutionSupportedExteriorProduct
    (K : DerivedCategory (Sheaf X.smallEtaleTopology C))
    (L : DerivedCategory (Sheaf Y.smallEtaleTopology C))
    (κ : (rightDerivedSectionsWithSupport C i).obj K ⊗
        (rightDerivedSectionsWithSupport C j).obj L ⟶
      (rightDerivedSectionsWithSupport C (supportedProductImmersion f g i j)).obj
        (externalProduct C f g K L)) : Prop :=
  ∀ (P : CochainComplex (Sheaf X.smallEtaleTopology C) ℤ)
    (Q : CochainComplex (Sheaf Y.smallEtaleTopology C) ℤ)
    (hP : (HomologicalComplex.quasiIso _ (.up ℤ)).kFlat P)
    (hQ : (HomologicalComplex.quasiIso _ (.up ℤ)).kFlat Q)
    (eP : DerivedCategory.Q.obj P ≅ K) (eQ : DerivedCategory.Q.obj Q ≅ L),
    tensorHom
        (exteriorSupportResolutionUnit C i P ≫
          (rightDerivedSectionsWithSupport C i).map eP.hom)
        (exteriorSupportResolutionUnit C j Q ≫
          (rightDerivedSectionsWithSupport C j).map eQ.hom) ≫ κ =
      Functor.LaxMonoidal.μ DerivedCategory.Q
          (((globalSectionsWithSupport C i).mapHomologicalComplex (.up ℤ)).obj P)
          (((globalSectionsWithSupport C j).mapHomologicalComplex (.up ℤ)).obj Q) ≫
        DerivedCategory.Q.map (exteriorSupportedSectionsComplex C f g i j P Q) ≫
        exteriorSupportResolutionUnit C (supportedProductImmersion f g i j)
          (exteriorSectionsComplexTarget C f g P Q) ≫
        (rightDerivedSectionsWithSupport C (supportedProductImmersion f g i j)).map
          ((exteriorProductResolutionIso C f g P Q hP hQ).inv ≫
            derivedTensorHom C
              ((upperStar C (pullback.fst f g)).leftDerivedFunctor.map eP.hom)
              ((upperStar C (pullback.snd f g)).leftDerivedFunctor.map eQ.hom))

end Ordinary

end AlgebraicGeometry.Etale
