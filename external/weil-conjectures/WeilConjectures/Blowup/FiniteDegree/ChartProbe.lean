/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import WeilConjectures.Blowup.FiniteDegree.Algebra
public import WeilConjectures.Blowup.Gluing
public import WeilConjectures.Compactification.FiniteTypeExtension
public import WeilConjectures.Mathlib.AlgebraicGeometry.Scheme

/-!
# Chart probes of the blow-up and their pulled-back ideals

The charts of the blow-up of a scheme over an affine open of the base, as probes
`Spec A[I/a] ⟶ Bl`, and the ideals obtained by pulling back ideal sheaves along them. Also the
quasi-compactness of the blow-up map of a finite-type ideal sheaf
(`AlgebraicGeometry.Scheme.IdealSheafData.quasiCompact_blowupMap`).
-/

@[expose] public section

noncomputable section
universe u

open CategoryTheory Limits

namespace AlgebraicGeometry
section FiniteDegreeBlowup

/-! ### Chart probes of the blow-up and their pulled-back ideals

For the finite-degree approximation we probe the blow-up `Bl_I X` by the affine charts
over an affine open `V` of the base at the degree-one Rees elements `a·X`, `a ∈ I(V)`.
We compute the ideal of global sections of the pullback of an ideal sheaf along such a
probe, and along a probe precomposed with `Spec` of a ring map. -/

open HomogeneousLocalization

/-- Comparing two ideals through the pullback along a bijective ring homomorphism. -/
lemma _root_.Ideal.le_of_comap_le_comap_of_bijective {R S : Type u} [CommRing R]
    [CommRing S] {f : R →+* S} (hf : Function.Bijective f) {P Q : Ideal S}
    (h : P.comap f ≤ Q.comap f) : P ≤ Q := by
  intro x hx
  obtain ⟨y, rfl⟩ := hf.2 x
  exact h (Ideal.mem_comap.mpr hx)

variable {X : Scheme.{u}}

/-- The chart probe of the blow-up over an affine open `V` at a section `a ∈ I(V)`: the
affine chart of the affine blow-up at the degree-one Rees element `a·X`, embedded into
the blow-up. -/
noncomputable def _root_.AlgebraicGeometry.Scheme.IdealSheafData.blowupChart
    (I : X.IdealSheafData) (V : X.affineOpens) {a : Γ(X, V.1)} (ha : a ∈ I.ideal V) :
    Spec (.of (HomogeneousLocalization.Away (reesGrading (I.ideal V))
      (reesX (I.ideal V) a ha))) ⟶ I.blowup :=
  AffineBlowup.chart (I.ideal V) (reesX (I.ideal V) a ha)
    (reesX_mem (I.ideal V) a ha) ≫ I.blowupι V

instance (I : X.IdealSheafData) (V : X.affineOpens) {a : Γ(X, V.1)} (ha : a ∈ I.ideal V) :
    IsOpenImmersion (I.blowupChart V ha) := by
  unfold Scheme.IdealSheafData.blowupChart
  infer_instance

/-- The map on section rings induced by the chart probe of the blow-up. -/
noncomputable def _root_.AlgebraicGeometry.Scheme.IdealSheafData.blowupChartSection
    (I : X.IdealSheafData) (V : X.affineOpens) {a : Γ(X, V.1)} (ha : a ∈ I.ideal V) :
    Γ(X, V.1) ⟶ Γ(Spec (.of (HomogeneousLocalization.Away (reesGrading (I.ideal V))
      (reesX (I.ideal V) a ha))), ⊤) :=
  CommRingCat.ofHom (AffineBlowup.awayAlgebraMap (I.ideal V)
    (reesX (I.ideal V) a ha)) ≫ (Scheme.ΓSpecIso _).inv

/-- The chart probe composed with the blow-up map is the affine probe of the chart
ring. -/
lemma _root_.AlgebraicGeometry.Scheme.IdealSheafData.blowupChart_comp_blowupMap
    (I : X.IdealSheafData) (V : X.affineOpens) {a : Γ(X, V.1)} (ha : a ∈ I.ideal V) :
    I.blowupChart V ha ≫ I.blowupMap =
      Spec.map (CommRingCat.ofHom (AffineBlowup.awayAlgebraMap (I.ideal V)
        (reesX (I.ideal V) a ha))) ≫ V.2.fromSpec := by
  unfold Scheme.IdealSheafData.blowupChart
  rw [Category.assoc, Scheme.IdealSheafData.blowupι_blowupMap,
    Scheme.IdealSheafData.blowupNatTrans_app, Category.assoc,
    AffineBlowup.chart_toSpec_assoc, IsAffineOpen.isoSpec_inv_ι]

/-- The chart probe lies over the affine open `V`. Derived from the abstract-probe
form `top_le_preimage_specMap_fromSpec`, which keeps the chart ring out of the
rewrite motives. -/
lemma _root_.AlgebraicGeometry.Scheme.IdealSheafData.blowupChart_comp_blowupMap_preimage
    (I : X.IdealSheafData) (V : X.affineOpens) {a : Γ(X, V.1)} (ha : a ∈ I.ideal V) :
    (⊤ : (Spec (.of (HomogeneousLocalization.Away (reesGrading (I.ideal V))
        (reesX (I.ideal V) a ha)))).Opens) ≤
      (I.blowupChart V ha ≫ I.blowupMap) ⁻¹ᵁ V.1 :=
  le_of_le_of_eq (top_le_preimage_specMap_fromSpec V _)
    (congrArg (fun f : Spec _ ⟶ X ↦ f ⁻¹ᵁ V.1)
      (I.blowupChart_comp_blowupMap V ha)).symm

/-- The `appLE` of the chart probe over `V` is the chart section map. -/
lemma _root_.AlgebraicGeometry.Scheme.IdealSheafData.appLE_blowupChart_comp_blowupMap
    (I : X.IdealSheafData) (V : X.affineOpens) {a : Γ(X, V.1)} (ha : a ∈ I.ideal V)
    (h : (⊤ : (Spec (.of (HomogeneousLocalization.Away (reesGrading (I.ideal V))
        (reesX (I.ideal V) a ha)))).Opens) ≤ (I.blowupChart V ha ≫ I.blowupMap) ⁻¹ᵁ V.1) :
    (I.blowupChart V ha ≫ I.blowupMap).appLE V.1 ⊤ h = I.blowupChartSection V ha := by
  rw [Scheme.Hom.appLE_eq_of_eq (I.blowupChart_comp_blowupMap V ha)]
  exact appLE_top_specMap_fromSpec V (CommRingCat.ofHom (AffineBlowup.awayAlgebraMap
    (I.ideal V) (reesX (I.ideal V) a ha))) _

/-- **Pullback of an ideal sheaf along a precomposed affine probe**: precomposing a
probe `Spec S ⟶ Y` with `Spec` of a ring map `β` extends the pulled-back ideal of
global sections along the induced map of section rings. -/
lemma _root_.AlgebraicGeometry.Scheme.IdealSheafData.ideal_comap_specMap_comp
    {Y : Scheme.{u}} (K : Y.IdealSheafData) {S S' : CommRingCat.{u}} (q : Spec S ⟶ Y)
    (β : S ⟶ S') :
    (K.comap (Spec.map β ≫ q)).ideal ⟨⊤, isAffineOpen_top _⟩ =
      ((K.comap q).ideal ⟨⊤, isAffineOpen_top _⟩).map
        ((Scheme.ΓSpecIso S).hom ≫ β ≫ (Scheme.ΓSpecIso S').inv).hom := by
  have hfac : Spec.map β =
      Spec.map ((Scheme.ΓSpecIso S).hom ≫ β) ≫ (isAffineOpen_top (Spec S)).fromSpec := by
    rw [IsAffineOpen.fromSpec_top, Scheme.isoSpec_Spec_inv, ← Spec.map_comp]
    rw [show (Scheme.ΓSpecIso S).inv ≫ (Scheme.ΓSpecIso S).hom ≫ β = β from
      Iso.inv_hom_id_assoc _ _]
  rw [Scheme.IdealSheafData.comap_comp, hfac,
    Scheme.IdealSheafData.ideal_top_comap_specMap_fromSpec (K.comap q)
      ⟨⊤, isAffineOpen_top _⟩ ((Scheme.ΓSpecIso S).hom ≫ β),
    Ideal.map_map, ← CommRingCat.hom_comp, Category.assoc]

/-- The variant of `ideal_comap_specMap_comp` after transport to the affine section
rings: precomposition extends the pulled-back ideal along `β` itself. -/
lemma _root_.AlgebraicGeometry.Scheme.IdealSheafData.map_ideal_comap_specMap_comp
    {Y : Scheme.{u}} (K : Y.IdealSheafData) {S S' : CommRingCat.{u}} (q : Spec S ⟶ Y)
    (β : S ⟶ S') :
    ((K.comap (Spec.map β ≫ q)).ideal ⟨⊤, isAffineOpen_top _⟩).map
        (Scheme.ΓSpecIso S').hom.hom =
      (((K.comap q).ideal ⟨⊤, isAffineOpen_top _⟩).map
        (Scheme.ΓSpecIso S).hom.hom).map β.hom := by
  rw [K.ideal_comap_specMap_comp q β, Ideal.map_map, Ideal.map_map,
    ← CommRingCat.hom_comp, ← CommRingCat.hom_comp]
  congr 2
  simp

/-- **Pullback of an inverse image ideal sheaf along a probe of the blow-up** lying
over an affine probe of the base. The probe ring `S` is kept abstract: this makes the
lemma cheap to instantiate at the large `HomogeneousLocalization` chart rings of the
blow-up, where every unification involving the concrete ring is prohibitively slow. -/
lemma _root_.AlgebraicGeometry.Scheme.IdealSheafData.ideal_comap_comap_of_probe
    (I K : X.IdealSheafData) {S : CommRingCat.{u}} (c : Spec S ⟶ I.blowup)
    (V : X.affineOpens) (φ : Γ(X, V.1) ⟶ S)
    (hc : c ≫ I.blowupMap = Spec.map φ ≫ V.2.fromSpec) :
    ((K.comap I.blowupMap).comap c).ideal ⟨⊤, isAffineOpen_top _⟩ =
      (K.ideal V).map (φ ≫ (Scheme.ΓSpecIso S).inv).hom := by
  rw [← Scheme.IdealSheafData.comap_comp, hc,
    K.ideal_top_comap_specMap_fromSpec V φ, CommRingCat.hom_comp, ← Ideal.map_map]

/-- The principal case of `ideal_comap_comap_of_probe`: if the extension of `K(V)`
along `φ` is generated by the image of a section `b`, so is the pullback of the
inverse image of `K` along the probe. -/
lemma _root_.AlgebraicGeometry.Scheme.IdealSheafData.ideal_comap_comap_of_probe_span
    (I K : X.IdealSheafData) {S : CommRingCat.{u}} (c : Spec S ⟶ I.blowup)
    (V : X.affineOpens) (φ : Γ(X, V.1) ⟶ S)
    (hc : c ≫ I.blowupMap = Spec.map φ ≫ V.2.fromSpec) {b : Γ(X, V.1)}
    (hspan : (K.ideal V).map φ.hom = Ideal.span {φ.hom b}) :
    ((K.comap I.blowupMap).comap c).ideal ⟨⊤, isAffineOpen_top _⟩ =
      Ideal.span {(φ ≫ (Scheme.ΓSpecIso S).inv).hom b} := by
  rw [Scheme.IdealSheafData.ideal_comap_comap_of_probe I K c V φ hc,
    CommRingCat.hom_comp, RingHom.comp_apply, ← Ideal.map_map, hspan, Ideal.map_span,
    Set.image_singleton]

/-- Pullback of `I_E^d · J'` along an open-immersion probe of the blow-up, in terms of
the pullbacks of the two factors. As in `ideal_comap_comap_of_probe`, the probe ring is
kept abstract for performance. -/
lemma _root_.AlgebraicGeometry.Scheme.IdealSheafData.ideal_comap_pow_mul_comap_probe
    (I : X.IdealSheafData) (J' : I.blowup.IdealSheafData) (d : ℕ)
    {S : CommRingCat.{u}} (c : Spec S ⟶ I.blowup) [IsOpenImmersion c] :
    ((((I.comap I.blowupMap) ^ d) * J').comap c).ideal ⟨⊤, isAffineOpen_top _⟩ =
      ((I.comap I.blowupMap).comap c).ideal ⟨⊤, isAffineOpen_top _⟩ ^ d *
        (J'.comap c).ideal ⟨⊤, isAffineOpen_top _⟩ := by
  rw [Scheme.IdealSheafData.comap_mul_of_isOpenImmersion,
    Scheme.IdealSheafData.comap_pow_of_isOpenImmersion,
    Scheme.IdealSheafData.ideal_mul, Pi.mul_apply, Scheme.IdealSheafData.ideal_pow,
    Pi.pow_apply]

/-- The pullback of the extension of an ideal sheaf `K` on the base along a chart probe
of the blow-up: the extension of `K(V)` along the chart section map. Instantiates the
generic `ideal_comap_comap_of_probe`, which keeps the chart ring out of all rewrite
motives. -/
lemma _root_.AlgebraicGeometry.Scheme.IdealSheafData.ideal_comap_comap_blowupChart
    (I K : X.IdealSheafData) (V : X.affineOpens) {a : Γ(X, V.1)} (ha : a ∈ I.ideal V) :
    ((K.comap I.blowupMap).comap (I.blowupChart V ha)).ideal ⟨⊤, isAffineOpen_top _⟩ =
      (K.ideal V).map (I.blowupChartSection V ha).hom :=
  Scheme.IdealSheafData.ideal_comap_comap_of_probe I K (I.blowupChart V ha) V
    (CommRingCat.ofHom (AffineBlowup.awayAlgebraMap (I.ideal V)
      (reesX (I.ideal V) a ha)))
    (I.blowupChart_comp_blowupMap V ha)

/-- On the `a`-chart of the blow-up, the pullback of the extension of the center is
generated by (the image of) `a`. -/
lemma _root_.AlgebraicGeometry.Scheme.IdealSheafData.ideal_comap_comap_blowupChart_self
    (I : X.IdealSheafData) (V : X.affineOpens) {a : Γ(X, V.1)} (ha : a ∈ I.ideal V) :
    ((I.comap I.blowupMap).comap (I.blowupChart V ha)).ideal ⟨⊤, isAffineOpen_top _⟩ =
      Ideal.span {(I.blowupChartSection V ha).hom a} :=
  Scheme.IdealSheafData.ideal_comap_comap_of_probe_span I I (I.blowupChart V ha) V
    (CommRingCat.ofHom (AffineBlowup.awayAlgebraMap (I.ideal V)
      (reesX (I.ideal V) a ha)))
    (I.blowupChart_comp_blowupMap V ha)
    (AffineBlowup.map_awayAlgebraMap_reesX_eq_span_singleton (I.ideal V) a ha)

/-- On the `a`-chart of the blow-up, the pullback of `I_E^d · J` is
`(a)^d · (J`-chart ideal`)`. -/
lemma _root_.AlgebraicGeometry.Scheme.IdealSheafData.ideal_comap_pow_mul_comap_blowupChart
    (I : X.IdealSheafData) (J' : I.blowup.IdealSheafData) (d : ℕ) (V : X.affineOpens)
    {a : Γ(X, V.1)} (ha : a ∈ I.ideal V) :
    ((((I.comap I.blowupMap) ^ d) * J').comap (I.blowupChart V ha)).ideal
        ⟨⊤, isAffineOpen_top _⟩ =
      Ideal.span {(I.blowupChartSection V ha).hom a} ^ d *
        (J'.comap (I.blowupChart V ha)).ideal ⟨⊤, isAffineOpen_top _⟩ :=
  (Scheme.IdealSheafData.ideal_comap_pow_mul_comap_probe I J' d
      (I.blowupChart V ha)).trans
    (congrArg
      (· ^ d * (J'.comap (I.blowupChart V ha)).ideal ⟨⊤, isAffineOpen_top _⟩)
      (I.ideal_comap_comap_blowupChart_self V ha))

-- The chart rings of the blow-up are large `HomogeneousLocalization` types; unifying
-- them exceeds the default heartbeat limit.
/-- **The chart probes at a generating set cover the blow-up over `V`.** -/
lemma _root_.AlgebraicGeometry.Scheme.IdealSheafData.preimage_subset_iUnion_range_blowupChart
    (I : X.IdealSheafData) (V : X.affineOpens) {s : Finset Γ(X, V.1)}
    (hs : Ideal.span (s : Set Γ(X, V.1)) = I.ideal V) :
    (I.blowupMap ⁻¹ᵁ V.1 : Set I.blowup) ⊆
      ⋃ a : s, Set.range (I.blowupChart V (hs ▸ Ideal.subset_span a.2)) := by
  intro x hx
  have hx2 : x ∈ I.blowupMap ⁻¹ᵁ V.1 := hx
  rw [I.blowupMap_preimage V] at hx2
  obtain ⟨y, rfl⟩ := hx2
  have hy : y ∈ (⊤ : (AffineBlowup (I.ideal V)).Opens) := trivial
  rw [← AffineBlowup.iSup_basicOpen_reesX_eq_top_of_span hs] at hy
  obtain ⟨a, hy⟩ := TopologicalSpace.Opens.mem_iSup.mp hy
  rw [← AffineBlowup.opensRange_chart (I.ideal V)
    (reesX (I.ideal V) a.1 (hs ▸ Ideal.subset_span a.2))
    (reesX_mem (I.ideal V) a.1 (hs ▸ Ideal.subset_span a.2))] at hy
  obtain ⟨z, rfl⟩ := hy
  exact Set.mem_iUnion.mpr ⟨a, z, (Scheme.Hom.comp_apply _ _ _).symm⟩

/-- The `Opens`-level form of `preimage_subset_iUnion_range_blowupChart`. -/
lemma _root_.AlgebraicGeometry.Scheme.IdealSheafData.preimage_le_iSup_opensRange_blowupChart
    (I : X.IdealSheafData) (V : X.affineOpens) {s : Finset Γ(X, V.1)}
    (hs : Ideal.span (s : Set Γ(X, V.1)) = I.ideal V) :
    I.blowupMap ⁻¹ᵁ V.1 ≤
      ⨆ a : s, (I.blowupChart V (hs ▸ Ideal.subset_span a.2)).opensRange := by
  intro x hx
  obtain ⟨a, ha⟩ := Set.mem_iUnion.mp
    (I.preimage_subset_iUnion_range_blowupChart V hs hx)
  exact TopologicalSpace.Opens.mem_iSup.mpr ⟨a, ha⟩

-- The chart rings of the blow-up are large `HomogeneousLocalization` types; unifying
-- them exceeds the default heartbeat limit.
/-- Precomposing the `a`-chart of the blow-up over `V` with the localization
`B_a → B_{a·b}` gives the same probe as precomposing the `b`-chart with
`B_b → B_{a·b}`. -/
lemma _root_.AlgebraicGeometry.Scheme.IdealSheafData.specMap_awayMap_blowupChart
    (I : X.IdealSheafData) (V : X.affineOpens) {a b : Γ(X, V.1)} (ha : a ∈ I.ideal V)
    (hb : b ∈ I.ideal V) :
    Spec.map (CommRingCat.ofHom (HomogeneousLocalization.awayMap (reesGrading (I.ideal V))
        (reesX_mem (I.ideal V) b hb) (rfl : reesX (I.ideal V) a ha * reesX (I.ideal V) b hb
          = reesX (I.ideal V) a ha * reesX (I.ideal V) b hb))) ≫ I.blowupChart V ha =
      Spec.map (CommRingCat.ofHom (HomogeneousLocalization.awayMap (reesGrading (I.ideal V))
        (reesX_mem (I.ideal V) a ha)
        (mul_comm (reesX (I.ideal V) a ha) (reesX (I.ideal V) b hb)))) ≫
        I.blowupChart V hb := by
  unfold Scheme.IdealSheafData.blowupChart AffineBlowup.chart
  rw [Proj.SpecMap_awayMap_awayι_assoc, Proj.SpecMap_awayMap_awayι_assoc]

/-- Comparing the ideals of two ideal sheaves on the image of an affine probe through
the pullbacks of global sections. -/
lemma _root_.AlgebraicGeometry.Scheme.IdealSheafData.ideal_le_of_comap_probe
    {Y T' : Scheme.{u}} (q : T' ⟶ Y) [IsOpenImmersion q] [IsAffine T']
    {K₁ K₂ : Y.IdealSheafData}
    (h : (K₁.comap q).ideal ⟨⊤, isAffineOpen_top _⟩ ≤
      (K₂.comap q).ideal ⟨⊤, isAffineOpen_top _⟩) :
    K₁.ideal ⟨q ''ᵁ ⊤, (isAffineOpen_top T').image_of_isOpenImmersion q⟩ ≤
      K₂.ideal ⟨q ''ᵁ ⊤, (isAffineOpen_top T').image_of_isOpenImmersion q⟩ := by
  rw [Scheme.IdealSheafData.ideal_comap_of_isOpenImmersion,
    Scheme.IdealSheafData.ideal_comap_of_isOpenImmersion] at h
  exact Ideal.le_of_comap_le_comap_of_bijective
    (ConcreteCategory.bijective_of_isIso _) h

/-- Comparing two ideal sheaves on affine opens inside an open `O` through their
restrictions to `O`. -/
lemma _root_.AlgebraicGeometry.Scheme.IdealSheafData.ideal_le_ideal_of_comap_ι_le
    {Y : Scheme.{u}} {O : Y.Opens} {K₁ K₂ : Y.IdealSheafData}
    (h : K₁.comap O.ι ≤ K₂.comap O.ι) (W : Y.affineOpens) (hW : W.1 ≤ O) :
    K₁.ideal W ≤ K₂.ideal W := by
  have hle : W.1 ≤ O.ι.opensRange := by
    rw [Scheme.Opens.opensRange_ι]
    exact hW
  have hW' : IsAffineOpen (O.ι ⁻¹ᵁ W.1) := W.2.preimage_of_isOpenImmersion O.ι hle
  have h' := h ⟨O.ι ⁻¹ᵁ W.1, hW'⟩
  rw [Scheme.IdealSheafData.ideal_comap_eq_map_appLE O.ι K₁ W ⟨_, hW'⟩ le_rfl,
    Scheme.IdealSheafData.ideal_comap_eq_map_appLE O.ι K₂ W ⟨_, hW'⟩ le_rfl] at h'
  have : IsIso (O.ι.appLE W.1 (O.ι ⁻¹ᵁ W.1) le_rfl) := by
    rw [Scheme.Hom.appLE_eq_app]
    exact O.ι.isIso_app W.1 hle
  have hbij : Function.Bijective (O.ι.appLE W.1 (O.ι ⁻¹ᵁ W.1) le_rfl).hom :=
    ConcreteCategory.bijective_of_isIso _
  have h2 := Ideal.comap_mono (f := (O.ι.appLE W.1 (O.ι ⁻¹ᵁ W.1) le_rfl).hom) h'
  rwa [Ideal.comap_map_of_bijective _ hbij, Ideal.comap_map_of_bijective _ hbij] at h2


end FiniteDegreeBlowup

/-- **The affine blow-up of a finitely generated ideal is quasi-compact**: the charts at
the degree-one elements associated to a finite generating set already cover the
blow-up. -/
lemma AffineBlowup.compactSpace_of_fg {A : Type u} [CommRing A] {I : Ideal A}
    (hI : I.FG) : CompactSpace (AffineBlowup I) := by
  classical
  obtain ⟨s, hs⟩ := hI
  have hmem : ∀ a ∈ s, (a : A) ∈ I := fun a ha ↦ hs ▸ Ideal.subset_span ha
  have hcov : ⨆ a : s, Proj.basicOpen (reesGrading I) (reesX I a.1 (hmem a.1 a.2)) = ⊤ :=
    AffineBlowup.iSup_basicOpen_reesX_eq_top_of_span hs
  constructor
  change IsCompact (Set.univ : Set (Proj (reesGrading I)))
  have huniv : (Set.univ : Set (Proj (reesGrading I))) =
      ⋃ a : s, (Proj.basicOpen (reesGrading I) (reesX I a.1 (hmem a.1 a.2)) : Set _) := by
    rw [← TopologicalSpace.Opens.coe_top, ← hcov]
    simp
  rw [huniv]
  refine isCompact_iUnion fun a ↦ ?_
  rw [← AffineBlowup.opensRange_chart I (reesX I a.1 (hmem a.1 a.2))
    (reesX_mem I a.1 (hmem a.1 a.2))]
  have hSpec : IsCompact (Set.univ : Set (Spec (.of (HomogeneousLocalization.Away
      (reesGrading I) (reesX I a.1 (hmem a.1 a.2)))))) := by
    have h := (isAffineOpen_top (Spec (.of (HomogeneousLocalization.Away
      (reesGrading I) (reesX I a.1 (hmem a.1 a.2)))))).isCompact
    simpa using h
  have himg := hSpec.image (AffineBlowup.chart I (reesX I a.1 (hmem a.1 a.2))
    (reesX_mem I a.1 (hmem a.1 a.2))).continuous
  rwa [Set.image_univ] at himg

/-- **The blow-up map of a finite-type ideal sheaf is quasi-compact**: the preimage of
an affine open is the affine blow-up of a finitely generated ideal. -/
lemma Scheme.IdealSheafData.quasiCompact_blowupMap {X : Scheme.{u}}
    {K : X.IdealSheafData} (hK : K.ofFiniteType) : QuasiCompact K.blowupMap := by
  rw [quasiCompact_iff_forall_isAffineOpen]
  intro U hU
  have h1 : K.blowupMap ⁻¹ᵁ U = (K.blowupι ⟨U, hU⟩).opensRange := K.blowupMap_preimage ⟨U, hU⟩
  rw [show (K.blowupMap ⁻¹ᵁ U : Set K.blowup) =
    ((K.blowupι ⟨U, hU⟩).opensRange : Set K.blowup) from congrArg _ h1]
  have := AffineBlowup.compactSpace_of_fg (hK ⟨U, hU⟩ le_top)
  exact isCompact_range (K.blowupι ⟨U, hU⟩).continuous

end AlgebraicGeometry
