/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.DeformationSpace.BlowupGlobal
public import WeilConjectures.AlgebraicGeometry.DeformationSpace.BlowupChartStrictTransform

/-!
# The image of the Rees model in the blow-up model

The open immersion `D_I X ⟶ Bl_{V(I) × 0} (Spec_X 𝒪_X[t])`
(`AlgebraicGeometry.Scheme.IdealSheafData.deformationSpaceToBlowup`) has image the complement of
the closure of the locus lying over the zero section `t = 0` off the center, i.e. the complement
of the strict transform of the zero section (blueprint `definition-deformation-normal-bundle`). This
is checked on the charts over the affine opens of `X`, where it is
`AlgebraicGeometry.AffineBlowup.compl_closure_zeroFibreOffCenter`. For `I` of finite type the open
locus of the zero section off the center has quasi-compact inclusion, so the closure is the strict
transform (`range_deformationSpaceToBlowup_eq_compl_strictTransform_of_ofFiniteType`).
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme

open AffineZariskiSite AffineBlowup

variable {X : Scheme.{u}}

instance : IsClosedImmersion X.polynomialZeroSpecToPolynomialSpec :=
  relativeGluingMap_of_forall X.coequifibered_toPolynomialPresheaf @IsClosedImmersion
    X.coequifibered_toPolynomialZeroPresheaf _ rfl fun _ ↦
      IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective

instance : IsClosedImmersion X.polynomialSpecZeroSection := by
  unfold polynomialSpecZeroSection; infer_instance

lemma range_polynomialSpecZeroSection :
    Set.range X.polynomialSpecZeroSection = Set.range X.polynomialZeroSpecToPolynomialSpec := by
  rw [polynomialSpecZeroSection, Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp,
    Set.range_eq_univ.mpr (Scheme.Hom.surjective _), Set.image_univ]

/-- On the chart `Spec Γ(U)[t]`, the zero section is `V(t)`. -/
lemma chart_mem_range_polynomialSpecZeroSection_iff (U : X.AffineZariskiSite)
    (p : Spec (.of (Polynomial Γ(X, U.1)))) :
    colimit.ι (relativeGluingData X.coequifibered_toPolynomialPresheaf).functor U p ∈
        Set.range X.polynomialSpecZeroSection ↔ p ∈ Set.range (zeroFibre Γ(X, U.1)) := by
  have hsq := isPullback_ι_relativeGluingMap X.coequifibered_toPolynomialPresheaf
    X.coequifibered_toPolynomialZeroPresheaf X.polynomialToPolynomialZero rfl U
  have hzero : Set.range (zeroFibre Γ(X, U.1)) =
      Set.range (Spec.map (X.polynomialToPolynomialZero.app (.op U))) := by
    rw [zeroFibre]
    change Set.range (PrimeSpectrum.comap _) = Set.range (PrimeSpectrum.comap _)
    rw [_root_.range_comap_of_surjective _ _
        (fun r ↦ ⟨Polynomial.C r, Polynomial.coeff_C_zero⟩),
      _root_.range_comap_of_surjective _ (X.polynomialToPolynomialZero.app (.op U)).hom
        Ideal.Quotient.mk_surjective]
    congr 1
    ext q
    change Polynomial.constantCoeff q = 0 ↔ q ∈ RingHom.ker (Ideal.Quotient.mk _)
    rw [Ideal.mk_ker, Ideal.mem_span_singleton, Polynomial.X_dvd_iff]
    rfl
  rw [hzero, range_polynomialSpecZeroSection]
  constructor
  · rintro ⟨z, hz⟩
    have hz' : z ∈ X.polynomialZeroSpecToPolynomialSpec ⁻¹ᵁ
        ((relativeGluingData X.coequifibered_toPolynomialPresheaf).toBase ⁻¹ᵁ U.1) := by
      rw [Scheme.Hom.mem_preimage]
      rw [hz, toBase_preimage]
      exact ⟨p, rfl⟩
    rw [polynomialZeroSpecToPolynomialSpec, relativeGluingMap_preimage _ _ _ rfl,
      toBase_preimage] at hz'
    obtain ⟨w, rfl⟩ := hz'
    refine ⟨w, (colimit.ι (relativeGluingData X.coequifibered_toPolynomialPresheaf).functor
      U).isOpenEmbedding.injective ?_⟩
    rw [← hz]
    exact congr($(hsq.w) w).symm
  · rintro ⟨w, rfl⟩
    exact ⟨colimit.ι (relativeGluingData X.coequifibered_toPolynomialZeroPresheaf).functor U w,
      congr($(hsq.w) w)⟩

namespace IdealSheafData

variable (I : X.IdealSheafData)

/-- On the chart `Spec Γ(U)[t]`, the support of the center is `V(I(U) Γ(U)[t] + (t))`. -/
lemma chart_mem_support_deformationCenterSheaf_iff (U : X.AffineZariskiSite)
    (p : Spec (.of (Polynomial Γ(X, U.1)))) :
    colimit.ι (relativeGluingData X.coequifibered_toPolynomialPresheaf).functor U p ∈
        I.deformationCenterSheaf.support ↔
      p ∈ PrimeSpectrum.zeroLocus
        (deformationCenter (I.siteIdeal U) : Set (Polynomial Γ(X, U.1))) := by
  set e := sectionsIso X.coequifibered_toPolynomialPresheaf U
  have hx : colimit.ι (relativeGluingData X.coequifibered_toPolynomialPresheaf).functor U p =
      (polynomialSpecChartOpen X U).2.fromSpec (Spec.map e.hom p) := by
    rw [ι_eq_specMap_sectionsIso_hom_fromSpec]
    rfl
  have hmem : colimit.ι (relativeGluingData X.coequifibered_toPolynomialPresheaf).functor U p ∈
      (polynomialSpecChartOpen X U).1 := by
    change _ ∈ (relativeGluingData X.coequifibered_toPolynomialPresheaf).toBase ⁻¹ᵁ U.1
    rw [toBase_preimage]
    exact ⟨p, rfl⟩
  have hb : ∀ g, (polynomialSpecChartOpen X U).2.fromSpec (Spec.map e.hom p) ∈
      X.polynomialSpec.basicOpen g ↔ e.hom g ∉ p.asIdeal := by
    intro g
    have := congr(Spec.map e.hom p ∈
      $((polynomialSpecChartOpen X U).2.fromSpec_preimage_basicOpen g))
    rw [eq_iff_iff] at this
    refine this.trans ?_
    rw [PrimeSpectrum.mem_basicOpen, Spec.map_apply, PrimeSpectrum.comap_asIdeal,
      Ideal.mem_comap]
    rfl
  rw [mem_support_iff_of_mem hmem, Scheme.mem_zeroLocus_iff, PrimeSpectrum.mem_zeroLocus]
  constructor
  · intro h f hf
    obtain ⟨g, rfl⟩ := e.commRingCatIsoToRingEquiv.surjective f
    have := h g (by rw [ideal_deformationCenterSheaf_chart]; exact hf)
    rw [hx, hb, not_not] at this
    exact this
  · intro h g hg
    rw [hx, hb, not_not]
    rw [ideal_deformationCenterSheaf_chart] at hg
    exact h hg

lemma chartBlowupHom_blowupι_blowupMap (U : X.AffineZariskiSite) :
    I.chartBlowupHom U ≫ I.deformationCenterSheaf.blowupι (polynomialSpecChartOpen X U) ≫
        I.deformationCenterSheaf.blowupMap =
      toSpec (deformationCenter (I.siteIdeal U)) ≫
        colimit.ι (relativeGluingData X.coequifibered_toPolynomialPresheaf).functor U := by
  rw [blowupι_blowupMap, blowupNatTrans_app, chartBlowupHom]
  simp only [Category.assoc]
  rw [AffineBlowup.hom_toSpec_assoc, IsAffineOpen.isoSpec_inv_ι, CommRingCat.ofHom_hom,
    ι_eq_specMap_sectionsIso_hom_fromSpec X.coequifibered_toPolynomialPresheaf U]

/-- Blueprint `definition-deformation-normal-bundle`: Deformation space of a closed section. The
image of the Rees model `D_I X` in the blow-up `Bl_{V(I) × 0} (Spec_X 𝒪_X[t])` is the complement of
the closure of the locus over the zero section off the center, i.e. of the strict transform of the
zero section. -/
theorem range_deformationSpaceToBlowup :
    Set.range I.deformationSpaceToBlowup =
      (closure (I.deformationCenterSheaf.blowupMap ⁻¹'
        ((I.deformationCenterSheaf.support : Set X.polynomialSpec)ᶜ ∩
          Set.range X.polynomialSpecZeroSection)))ᶜ := by
  ext y
  obtain ⟨U, hU⟩ : ∃ U : X.AffineZariskiSite,
      y ∈ I.deformationCenterSheaf.blowupMap ⁻¹ᵁ (polynomialSpecChartOpen X U).1 := by
    have : y ∈ I.deformationCenterSheaf.blowupMap ⁻¹ᵁ
        (⨆ U : X.AffineZariskiSite, (polynomialSpecChartOpen X U).1) := by
      rw [iSup_polynomialSpecChartOpen]; trivial
    rw [Scheme.Hom.preimage_iSup] at this
    exact TopologicalSpace.Opens.mem_iSup.mp this
  rw [blowupMap_preimage] at hU
  obtain ⟨y₁, rfl⟩ := hU
  obtain ⟨y', rfl⟩ : ∃ y', I.chartBlowupHom U y' = y₁ :=
    ⟨inv (I.chartBlowupHom U) y₁, by rw [← Scheme.Hom.comp_apply, IsIso.inv_hom_id]; rfl⟩
  let g := I.chartBlowupHom U ≫ I.deformationCenterSheaf.blowupι (polynomialSpecChartOpen X U)
  have hy : I.deformationCenterSheaf.blowupι (polynomialSpecChartOpen X U)
      (I.chartBlowupHom U y') = g y' := (Scheme.Hom.comp_apply _ _ _).symm
  rw [hy]
  have hS : g ⁻¹' (I.deformationCenterSheaf.blowupMap ⁻¹'
        ((I.deformationCenterSheaf.support : Set X.polynomialSpec)ᶜ ∩
          Set.range X.polynomialSpecZeroSection)) =
      zeroFibreOffCenter (I.siteIdeal U) := by
    ext z
    change ((I.chartBlowupHom U ≫ I.deformationCenterSheaf.blowupι (polynomialSpecChartOpen X U))
        ≫ I.deformationCenterSheaf.blowupMap) z ∈
        (I.deformationCenterSheaf.support : Set X.polynomialSpec)ᶜ ∩
          Set.range X.polynomialSpecZeroSection ↔
      toSpec (deformationCenter (I.siteIdeal U)) z ∈
        (centerCompl (I.siteIdeal U) : Set (Spec (.of (Polynomial Γ(X, U.1))))) ∩
          Set.range (zeroFibre Γ(X, U.1))
    rw [Category.assoc, chartBlowupHom_blowupι_blowupMap, Scheme.Hom.comp_apply]
    exact and_congr (not_congr (I.chart_mem_support_deformationCenterSheaf_iff U _))
      (chart_mem_range_polynomialSpecZeroSection_iff U _)
  have hcl : g y' ∈ closure (I.deformationCenterSheaf.blowupMap ⁻¹'
        ((I.deformationCenterSheaf.support : Set X.polynomialSpec)ᶜ ∩
          Set.range X.polynomialSpecZeroSection)) ↔
      y' ∈ closure (zeroFibreOffCenter (I.siteIdeal U)) := by
    rw [← hS, ← g.isOpenEmbedding.isOpenMap.preimage_closure_eq_closure_preimage g.continuous]
    rfl
  rw [Set.mem_compl_iff, hcl, ← Set.mem_compl_iff, compl_closure_zeroFibreOffCenter]
  have hloc : ∀ d, I.deformationChartToBlowup U d = g (deformationChart (I.siteIdeal U) d) :=
    fun d ↦ rfl
  constructor
  · rintro ⟨d, hd⟩
    have hd' : d ∈ I.deformationSpaceToBlowup ⁻¹ᵁ
        (I.deformationCenterSheaf.blowupMap ⁻¹ᵁ (polynomialSpecChartOpen X U).1) := by
      rw [Scheme.Hom.mem_preimage]
      rw [hd, blowupMap_preimage]
      exact ⟨_, rfl⟩
    rw [preimage_deformationSpaceToBlowup_chart] at hd'
    obtain ⟨d', rfl⟩ := hd'
    refine ⟨d', g.isOpenEmbedding.injective ?_⟩
    rw [← hloc]
    exact (congr($(I.ι_deformationSpaceToBlowup U) d')).symm.trans hd
  · rintro ⟨d', rfl⟩
    refine ⟨colimit.ι (relativeGluingData I.coequifibered_toReesPresheaf).functor U d', ?_⟩
    exact (congr($(I.ι_deformationSpaceToBlowup U) d')).trans (hloc d')

/-- Blueprint `definition-deformation-normal-bundle`: Deformation space of a closed section. When
the strict transform of the zero section is the closure of its open locus (e.g. under the
quasi-compactness hypothesis below, which holds when `I` is of finite type by
`IdealSheafData.quasiCompact_strictTransformOpen_ι`), the image of `D_I X` in the blow-up model
is the complement of the strict transform. -/
theorem range_deformationSpaceToBlowup_eq_compl_strictTransform
    [QuasiCompact (strictTransformOpen X.polynomialSpecZeroSection
      I.deformationCenterSheaf.blowupMap I.deformationCenterSheaf.support.compl).ι] :
    Set.range I.deformationSpaceToBlowup =
      (Set.range (strictTransformMap X.polynomialSpecZeroSection
        I.deformationCenterSheaf.blowupMap I.deformationCenterSheaf.support.compl))ᶜ := by
  rw [range_strictTransformMap_eq_closure, range_deformationSpaceToBlowup]
  rfl

/-- Over the chart `U`, the locus of the blow-up model lying over the complement of the center
is the image of the locus of the affine blow-up over the complement of its center. -/
lemma preimage_compl_support_inter_chart (U : X.AffineZariskiSite) :
    I.deformationCenterSheaf.blowupMap ⁻¹'
        ((I.deformationCenterSheaf.support.compl : Set X.polynomialSpec) ∩
          (polynomialSpecChartOpen X U).1) =
      (I.chartBlowupHom U ≫ I.deformationCenterSheaf.blowupι (polynomialSpecChartOpen X U)) ''
        (toSpec (deformationCenter (I.siteIdeal U)) ⁻¹'
          (centerCompl (I.siteIdeal U) : Set (Spec (.of (Polynomial Γ(X, U.1)))))) := by
  set g := I.chartBlowupHom U ≫ I.deformationCenterSheaf.blowupι (polynomialSpecChartOpen X U)
  have hg : ∀ z, I.deformationCenterSheaf.blowupMap (g z) =
      colimit.ι (relativeGluingData X.coequifibered_toPolynomialPresheaf).functor U
        (toSpec (deformationCenter (I.siteIdeal U)) z) := by
    intro z
    have := congr($(I.chartBlowupHom_blowupι_blowupMap U) z)
    simp only [Scheme.Hom.comp_apply] at this
    exact this
  ext y
  constructor
  · rintro ⟨h0, h1⟩
    have hy : y ∈ I.deformationCenterSheaf.blowupMap ⁻¹ᵁ (polynomialSpecChartOpen X U).1 :=
      h1
    rw [blowupMap_preimage] at hy
    obtain ⟨y₁, rfl⟩ := hy
    obtain ⟨y', rfl⟩ : ∃ y', I.chartBlowupHom U y' = y₁ :=
      ⟨inv (I.chartBlowupHom U) y₁, by rw [← Scheme.Hom.comp_apply, IsIso.inv_hom_id]; rfl⟩
    refine ⟨y', ?_, (Scheme.Hom.comp_apply _ _ _).symm⟩
    have h0' : I.deformationCenterSheaf.blowupMap (g y') ∉ I.deformationCenterSheaf.support := by
      have : g y' = _ := Scheme.Hom.comp_apply _ _ _
      rw [this]; exact h0
    rw [hg, chart_mem_support_deformationCenterSheaf_iff] at h0'
    exact h0'
  · rintro ⟨z, hz, rfl⟩
    refine ⟨?_, ?_⟩
    · change I.deformationCenterSheaf.blowupMap (g z) ∉ I.deformationCenterSheaf.support
      rw [hg, chart_mem_support_deformationCenterSheaf_iff]
      exact hz
    · change I.deformationCenterSheaf.blowupMap (g z) ∈
        (relativeGluingData X.coequifibered_toPolynomialPresheaf).toBase ⁻¹ᵁ U.1
      rw [hg, toBase_preimage]
      exact ⟨_, rfl⟩


/-- For `I` of finite type, the inclusion of the locus of `(zero section) ×_{Spec_X 𝒪_X[t]}
Bl_{V(I) × 0}` lying off the center is quasi-compact. This is checked over the charts
`Spec Γ(U)[t]` of the base. -/
lemma quasiCompact_strictTransformOpen_ι (hI : I.ofFiniteType) :
    QuasiCompact (strictTransformOpen X.polynomialSpecZeroSection
      I.deformationCenterSheaf.blowupMap I.deformationCenterSheaf.support.compl).ι := by
  set f := X.polynomialSpecZeroSection
  set π := I.deformationCenterSheaf.blowupMap
  set W := strictTransformOpen f π I.deformationCenterSheaf.support.compl
  let V : X.AffineZariskiSite → (pullback f π).Opens :=
    fun U ↦ pullback.snd f π ⁻¹ᵁ (π ⁻¹ᵁ (polynomialSpecChartOpen X U).1)
  have hV : iSup V = ⊤ := by
    simp only [V, ← Scheme.Hom.preimage_iSup, iSup_polynomialSpecChartOpen,
      Scheme.Hom.preimage_top]
  refine IsZariskiLocalAtTarget.of_iSup_eq_top V hV fun U ↦ ?_
  have hJ : (deformationCenter (I.siteIdeal U)).FG :=
    deformationCenter_fg ((I.ofFiniteType_iff.mp hI) ⟨U.1, U.2⟩)
  have : IsProper (toSpec (deformationCenter (I.siteIdeal U))) := isProper_toSpec _ hJ
  set g := I.chartBlowupHom U ≫ I.deformationCenterSheaf.blowupι (polynomialSpecChartOpen X U)
  have hrange : Set.range ((V U).ι ≫ pullback.snd f π) ⊆ Set.range g := by
    rintro _ ⟨v, rfl⟩
    have hv : pullback.snd f π ((V U).ι v) ∈ π ⁻¹ᵁ (polynomialSpecChartOpen X U).1 := by
      have := v.2
      rwa [Scheme.Opens.ι_apply]
    rw [blowupMap_preimage] at hv
    obtain ⟨y₁, hy₁⟩ := hv
    refine ⟨inv (I.chartBlowupHom U) y₁, ?_⟩
    change _ = pullback.snd f π ((V U).ι v)
    rw [← hy₁, ← Scheme.Hom.comp_apply (inv (I.chartBlowupHom U))]
    simp only [g, IsIso.inv_hom_id_assoc]
  have : QuasiSeparatedSpace (AffineBlowup (deformationCenter (I.siteIdeal U))) :=
    quasiSeparatedSpace_of_quasiSeparated (toSpec (deformationCenter (I.siteIdeal U)))
  let h := IsOpenImmersion.lift g ((V U).ι ≫ pullback.snd f π) hrange
  have : QuasiSeparated (h ≫ g) := by
    rw [IsOpenImmersion.lift_fac]; infer_instance
  have : QuasiSeparated h := .of_comp h g
  have : QuasiSeparatedSpace (V U).toScheme := quasiSeparatedSpace_of_quasiSeparated h
  have hW : ((W : Set ↥(pullback f π)) ∩ (V U : Set ↥(pullback f π))) =
      pullback.snd f π ⁻¹' (π ⁻¹'
      ((I.deformationCenterSheaf.support.compl : Set X.polynomialSpec) ∩
        (polynomialSpecChartOpen X U).1)) := rfl
  have hcpt : IsCompact ((W : Set ↥(pullback f π)) ∩ (V U : Set ↥(pullback f π))) := by
    rw [hW, preimage_compl_support_inter_chart]
    refine QuasiCompact.isCompact_preimage (f := pullback.snd f π) _ ?_ ?_
    · rw [← preimage_compl_support_inter_chart]
      exact (π ⁻¹ᵁ (I.deformationCenterSheaf.support.compl ⊓
        (polynomialSpecChartOpen X U).1)).isOpen
    · refine IsCompact.image ?_ g.continuous
      exact (toSpec (deformationCenter (I.siteIdeal U))).isProperMap.isCompact_preimage
        (PrimeSpectrum.isCompact_isOpen_iff_ideal.mpr ⟨_, hJ, rfl⟩).1
  have : CompactSpace (W.ι ⁻¹ᵁ V U).toScheme := by
    refine isCompact_iff_compactSpace.mp ?_
    refine W.ι.isOpenEmbedding.isEmbedding.isCompact_iff.mpr ?_
    change IsCompact (W.ι '' (W.ι ⁻¹' (V U : Set ↥(pullback f π))))
    rwa [Set.image_preimage_eq_inter_range, Scheme.Opens.range_ι, Set.inter_comm]
  infer_instance

/-- Blueprint `definition-deformation-normal-bundle`: Deformation space of a closed section. For an
ideal sheaf `I` of finite type, the image of the Rees model `D_I X` in the blow-up model
`Bl_{V(I) × 0} (Spec_X 𝒪_X[t])` is the complement of the strict transform of the zero section
`X × 0`. -/
theorem range_deformationSpaceToBlowup_eq_compl_strictTransform_of_ofFiniteType
    (hI : I.ofFiniteType) :
    Set.range I.deformationSpaceToBlowup =
      (Set.range (strictTransformMap X.polynomialSpecZeroSection
        I.deformationCenterSheaf.blowupMap I.deformationCenterSheaf.support.compl))ᶜ :=
  have := I.quasiCompact_strictTransformOpen_ι hI
  I.range_deformationSpaceToBlowup_eq_compl_strictTransform

/-- The open complement of the closure of the locus over the zero section off the center in the
blow-up model; under the hypothesis of
`range_deformationSpaceToBlowup_eq_compl_strictTransform` it is the complement of the strict
transform of the zero section. -/
noncomputable def blowupModelOpen : I.deformationCenterSheaf.blowup.Opens :=
  ⟨(closure (I.deformationCenterSheaf.blowupMap ⁻¹'
      ((I.deformationCenterSheaf.support : Set X.polynomialSpec)ᶜ ∩
        Set.range X.polynomialSpecZeroSection)))ᶜ, isClosed_closure.isOpen_compl⟩

/-- Blueprint `definition-deformation-normal-bundle`: Deformation space of a closed section. The
Rees model `D_I X = Spec_X 𝒪_X[t, I t⁻¹]` is isomorphic to the open subscheme
`Bl_{V(I) × 0} (Spec_X 𝒪_X[t]) ∖ (closure of the locus over the zero section off the center)` of
the blow-up model, compatibly with the maps to `Spec_X 𝒪_X[t]`
(`deformationSpaceIsoBlowupModelOpen_hom_ι`, `deformationSpaceToBlowup_blowupMap`). -/
noncomputable def deformationSpaceIsoBlowupModelOpen :
    I.deformationSpace ≅ I.blowupModelOpen.toScheme :=
  IsOpenImmersion.isoOfRangeEq I.deformationSpaceToBlowup I.blowupModelOpen.ι (by
    rw [Scheme.Opens.range_ι, range_deformationSpaceToBlowup]
    rfl)

@[reassoc (attr := simp)]
lemma deformationSpaceIsoBlowupModelOpen_hom_ι :
    I.deformationSpaceIsoBlowupModelOpen.hom ≫ I.blowupModelOpen.ι = I.deformationSpaceToBlowup :=
  IsOpenImmersion.isoOfRangeEq_hom_fac _ _ _

end IdealSheafData

end AlgebraicGeometry.Scheme
