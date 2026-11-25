/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import WeilConjectures.Blowup.EliminationOfIndeterminacy.Slope
public import WeilConjectures.Mathlib.AlgebraicGeometry.AffineSpace

/-!
# Gluing the chart-local extensions to relative affine space

The chart-local extensions to relative affine space, given by slopes on the charts of the
blow-up, glue (`AlgebraicGeometry.Scheme.IdealSheafData.exists_hom_affineSpace_of_awaySlope`).
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory Limits HomogeneousLocalization

namespace AlgebraicGeometry
section Gluing

/-! ### Gluing the chart-local extensions to relative affine space -/

variable {A : Type u} [CommRing A] {I : Ideal A}

/-- The product of two slopes on the same chart depends only on the product of the
numerators. -/
lemma AffineBlowup.awaySlope_mul_awaySlope {a b b' d d' : A} (ha : a ∈ I) (hb : b ∈ I)
    (hb' : b' ∈ I) (hd : d ∈ I) (hd' : d' ∈ I) (h : b * b' = d * d') :
    AffineBlowup.awaySlope I ha hb * AffineBlowup.awaySlope I ha hb' =
      AffineBlowup.awaySlope I ha hd * AffineBlowup.awaySlope I ha hd' := by
  rw [HomogeneousLocalization.ext_iff_val, HomogeneousLocalization.val_mul,
    HomogeneousLocalization.val_mul, AffineBlowup.awaySlope, AffineBlowup.awaySlope,
    AffineBlowup.awaySlope, AffineBlowup.awaySlope, HomogeneousLocalization.Away.val_mk,
    HomogeneousLocalization.Away.val_mk, HomogeneousLocalization.Away.val_mk,
    HomogeneousLocalization.Away.val_mk, Localization.mk_mul, Localization.mk_mul,
    Localization.mk_eq_mk_iff, Localization.r_iff_exists]
  refine ⟨1, Subtype.ext ?_⟩
  simp [Polynomial.monomial_mul_monomial, h]

/-- The two chart transition maps exhibit `Spec` of the chart ring at a product of two
degree-one Rees elements as the intersection of the two charts. -/
lemma AffineBlowup.isPullback_chart {a b : A} (ha : a ∈ I) (hb : b ∈ I) :
    IsPullback
      (Spec.map (CommRingCat.ofHom (HomogeneousLocalization.awayMap (reesGrading I)
        (reesX_mem I b hb) (rfl : reesX I a ha * reesX I b hb = reesX I a ha * reesX I b hb))))
      (Spec.map (CommRingCat.ofHom (HomogeneousLocalization.awayMap (reesGrading I)
        (reesX_mem I a ha) (mul_comm (reesX I a ha) (reesX I b hb)))))
      (AffineBlowup.chart I (reesX I a ha) (reesX_mem I a ha))
      (AffineBlowup.chart I (reesX I b hb) (reesX_mem I b hb)) := by
  refine IsPullback.of_iso_pullback ⟨?_⟩
    (Proj.pullbackAwayιIso (reesGrading I) (reesX_mem I a ha) one_pos (reesX_mem I b hb)
      one_pos (rfl : reesX I a ha * reesX I b hb = reesX I a ha * reesX I b hb)).symm
    ?_ ?_
  · rw [AffineBlowup.chart, AffineBlowup.chart, Proj.SpecMap_awayMap_awayι,
      Proj.SpecMap_awayMap_awayι]
  · exact Proj.pullbackAwayιIso_inv_fst ..
  · exact Proj.pullbackAwayιIso_inv_snd (hx := rfl) ..

variable {X : Scheme.{u}}

/-- The chart of the blow-up at a product of two degree-one Rees elements is the
intersection of the two charts. -/
lemma Scheme.IdealSheafData.isPullback_blowupChart {X : Scheme.{u}} (K : X.IdealSheafData)
    (V : X.affineOpens) {a b : Γ(X, V.1)} (ha : a ∈ K.ideal V) (hb : b ∈ K.ideal V) :
    IsPullback
      (Spec.map (CommRingCat.ofHom (HomogeneousLocalization.awayMap (reesGrading (K.ideal V))
        (reesX_mem (K.ideal V) b hb) rfl)))
      (Spec.map (CommRingCat.ofHom (HomogeneousLocalization.awayMap (reesGrading (K.ideal V))
        (reesX_mem (K.ideal V) a ha)
        (mul_comm (reesX (K.ideal V) a ha) (reesX (K.ideal V) b hb)))))
      (K.blowupChart V ha) (K.blowupChart V hb) := by
  unfold Scheme.IdealSheafData.blowupChart
  rw [IsPullback.comp_mono_iff (K.blowupι V)]
  exact AffineBlowup.isPullback_chart _ _

/-- **The chart-local extensions agree on the overlap.** The exact relations
`b j * a' = b' j * a` between the numerators make the two degree-one slopes restrict to the
same section of the chart at `a · a'`. -/
lemma Scheme.IdealSheafData.homOfVector_awaySlope_compat {X : Scheme.{u}}
    (K : X.IdealSheafData) (V : X.affineOpens) {σ : Type u} {a a' : Γ(X, V.1)}
    (ha : a ∈ K.ideal V) (ha' : a' ∈ K.ideal V) {b b' : σ → Γ(X, V.1)}
    (hb : ∀ j, b j ∈ K.ideal V) (hb' : ∀ j, b' j ∈ K.ideal V)
    (hrel : ∀ j, b j * a' = b' j * a) :
    Spec.map (CommRingCat.ofHom (HomogeneousLocalization.awayMap (reesGrading (K.ideal V))
        (reesX_mem (K.ideal V) a' ha') rfl)) ≫
        AffineSpace.homOfVector (K.blowupChart V ha ≫ K.blowupMap)
          (fun j ↦ (Scheme.ΓSpecIso _).inv
            (AffineBlowup.awaySlope (K.ideal V) ha (hb j))) =
      Spec.map (CommRingCat.ofHom (HomogeneousLocalization.awayMap (reesGrading (K.ideal V))
        (reesX_mem (K.ideal V) a ha)
        (mul_comm (reesX (K.ideal V) a ha) (reesX (K.ideal V) a' ha')))) ≫
        AffineSpace.homOfVector (K.blowupChart V ha' ≫ K.blowupMap)
          (fun j ↦ (Scheme.ΓSpecIso _).inv
            (AffineBlowup.awaySlope (K.ideal V) ha' (hb' j))) := by
  refine AffineSpace.specMap_comp_homOfVector_eq _ _ (K.blowupChart V ha ≫ K.blowupMap)
    (K.blowupChart V ha' ≫ K.blowupMap) ?_ _ _ fun j ↦ ?_
  · rw [← Category.assoc, ← Category.assoc, K.specMap_awayMap_blowupChart V ha ha']
  · exact AffineBlowup.awayMap_awaySlope_eq ha ha' (hb j) (hb' j) (hrel j)

/-- Compatible morphisms over a base glue along any jointly surjective family of open
immersions. Keeping the chart schemes abstract avoids expanding their coordinate rings. -/
private lemma Scheme.exists_glued_hom_over {B Y Z : Scheme.{u}} {ι : Type u}
    {U : ι → Scheme.{u}} (c : ∀ i, U i ⟶ Z) [∀ i, IsOpenImmersion (c i)]
    (hc : ∀ x : Z, ∃ i y, c i y = x) (p : Y ⟶ B) (q : Z ⟶ B)
    (f : ∀ i, U i ⟶ Y)
    (hcompat : ∀ i i', pullback.fst (c i) (c i') ≫ f i =
      pullback.snd (c i) (c i') ≫ f i')
    (hf : ∀ i, f i ≫ p = c i ≫ q) :
    ∃ g : Z ⟶ Y, g ≫ p = q ∧ ∀ i, c i ≫ g = f i := by
  let 𝒰 : Z.OpenCover := Scheme.Cover.mkOfCovers ι U c hc
  refine ⟨𝒰.glueMorphisms f hcompat, ?_, 𝒰.ι_glueMorphisms f hcompat⟩
  apply 𝒰.hom_ext
  intro i
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (fun k ↦ k ≫ p) (𝒰.ι_glueMorphisms f hcompat i)).trans (hf i))

/-- **Gluing the chart-local extensions.** Let `a i` and `b i j` be sections of the centre
`K` over an affine open `V` satisfying the exact relations `b i j * a i' = b i' j * a i`.
On the chart of the blow-up at `a i` the degree-one slope `b i j / a i` extends the `j`-th
coordinate, and the relations make the chart transitions hold on the nose, so these local
morphisms to `𝔸(σ; X)` glue over the union `W` of the charts. -/
lemma Scheme.IdealSheafData.exists_hom_affineSpace_of_awaySlope {X : Scheme.{u}}
    (K : X.IdealSheafData) (V : X.affineOpens) {σ ι : Type u}
    {a : ι → Γ(X, V.1)} (ha : ∀ i, a i ∈ K.ideal V)
    {b : ι → σ → Γ(X, V.1)} (hb : ∀ i j, b i j ∈ K.ideal V)
    (hrel : ∀ i i' j, b i j * a i' = b i' j * a i)
    (W : K.blowup.Opens) (hW : W = ⨆ i, (K.blowupChart V (ha i)).opensRange)
    (ci : ∀ i : ι, Spec (.of (HomogeneousLocalization.Away (reesGrading (K.ideal V))
      (reesX (K.ideal V) (a i) (ha i)))) ⟶ W.toScheme)
    (hci : ∀ i, ci i ≫ W.ι = K.blowupChart V (ha i)) :
    ∃ g : W.toScheme ⟶ 𝔸(σ; X), g ≫ 𝔸(σ; X) ↘ X = W.ι ≫ K.blowupMap ∧
      ∀ i, ci i ≫ g = AffineSpace.homOfVector (K.blowupChart V (ha i) ≫ K.blowupMap)
        (fun j ↦ (Scheme.ΓSpecIso _).inv
          (AffineBlowup.awaySlope (K.ideal V) (ha i) (hb i j))) := by
  have : ∀ i, IsOpenImmersion (ci i) := by
    intro i
    have h1 : IsOpenImmersion (ci i ≫ W.ι) := by rw [hci i]; infer_instance
    exact IsOpenImmersion.of_comp _ W.ι
  have hcov : ∀ x : W.toScheme, ∃ i y, (ci i) y = x := by
    intro x
    have hx : (x.1 : K.blowup) ∈ ⨆ i : ι, (K.blowupChart V (ha i)).opensRange := by
      rw [← hW]; exact x.2
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp hx
    obtain ⟨y, hy⟩ := hi
    refine ⟨i, y, W.ι.isOpenEmbedding.injective ?_⟩
    rw [← Scheme.Hom.comp_apply, hci i, hy]
    rfl
  have hcompat : ∀ i i' : ι,
      pullback.fst (ci i) (ci i') ≫ AffineSpace.homOfVector
          (K.blowupChart V (ha i) ≫ K.blowupMap)
          (fun j ↦ (Scheme.ΓSpecIso _).inv
            (AffineBlowup.awaySlope (K.ideal V) (ha i) (hb i j))) =
        pullback.snd (ci i) (ci i') ≫ AffineSpace.homOfVector
          (K.blowupChart V (ha i') ≫ K.blowupMap)
          (fun j ↦ (Scheme.ΓSpecIso _).inv
            (AffineBlowup.awaySlope (K.ideal V) (ha i') (hb i' j))) := by
    intro i i'
    have hpb : IsPullback
        (Spec.map (CommRingCat.ofHom (HomogeneousLocalization.awayMap (reesGrading (K.ideal V))
          (reesX_mem (K.ideal V) (a i') (ha i')) rfl)))
        (Spec.map (CommRingCat.ofHom (HomogeneousLocalization.awayMap (reesGrading (K.ideal V))
          (reesX_mem (K.ideal V) (a i) (ha i))
          (mul_comm (reesX (K.ideal V) (a i) (ha i)) (reesX (K.ideal V) (a i') (ha i'))))))
        (ci i) (ci i') := by
      rw [← IsPullback.comp_mono_iff W.ι, hci i, hci i']
      exact K.isPullback_blowupChart V (ha i) (ha i')
    exact hpb.fst_comp_eq_snd_comp _ _
      (K.homOfVector_awaySlope_compat V (ha i) (ha i') (hb i) (hb i') (hrel i i'))
  refine Scheme.exists_glued_hom_over ci hcov (𝔸(σ; X) ↘ X) (W.ι ≫ K.blowupMap)
    _ hcompat fun i ↦ ?_
  exact (AffineSpace.homOfVector_over _ _).trans
    ((congrArg (fun k ↦ k ≫ K.blowupMap) (hci i).symm).trans (Category.assoc _ _ _))

/-- The global sections of the blow-up chart over an affine scheme pull sections of `X` back
through the structure map of the chart ring. -/
lemma Scheme.IdealSheafData.appTop_blowupChart_comp_blowupMap {X : Scheme.{u}} [IsAffine X]
    (K : X.IdealSheafData) {d : Γ(X, ⊤)} (hd : d ∈ K.ideal ⟨⊤, isAffineOpen_top X⟩)
    (r : Γ(X, ⊤)) :
    (K.blowupChart ⟨⊤, isAffineOpen_top X⟩ hd ≫ K.blowupMap).appTop r =
      (Scheme.ΓSpecIso _).inv (AffineBlowup.awayAlgebraMap
        (K.ideal ⟨⊤, isAffineOpen_top X⟩)
        (reesX (K.ideal ⟨⊤, isAffineOpen_top X⟩) d hd) r) := by
  have h := K.appLE_blowupChart_comp_blowupMap ⟨⊤, isAffineOpen_top X⟩ hd
    (K.blowupChart_comp_blowupMap_preimage ⟨⊤, isAffineOpen_top X⟩ hd)
  rw [Scheme.Hom.appLE_top_top] at h
  exact congrArg (fun φ ↦ φ r) h

/-- **The glued extension agrees with the partial map over a basic open of the centre.**
On the preimage of `D(d)` the blow-up is covered by a single chart `Spec R`, on which the
extension has coordinates `s j` with `φ d · s j = φ (b j)`; since `d` is invertible there,
this forces the extension to agree with any partial map whose coordinates satisfy
`coordⱼ · d = b j` on `D(d)`. -/
lemma Scheme.IdealSheafData.homOfLE_comp_eq_of_chart {X : Scheme.{u}} {σ : Type u}
    (K : X.IdealSheafData) {U : X.Opens} {W : K.blowup.Opens}
    (hWmem : K.blowupMap ⁻¹ᵁ U ≤ W) {f : U.toScheme ⟶ 𝔸(σ; X)}
    (hf : f ≫ 𝔸(σ; X) ↘ X = U.ι) (g : W.toScheme ⟶ 𝔸(σ; X))
    {R : CommRingCat.{u}} (chart : Spec R ⟶ K.blowup) [IsOpenImmersion chart]
    (φ : Γ(X, ⊤) ⟶ R)
    (hφ : ∀ r, (chart ≫ K.blowupMap).appTop r = (Scheme.ΓSpecIso R).inv (φ r))
    {d : Γ(X, ⊤)} {b : σ → Γ(X, ⊤)} (s : σ → R) (hs : ∀ j, φ d * s j = φ (b j))
    {D : X.Opens} (hD : X.basicOpen d = D) (hDU : D ≤ U)
    (hcoord : ∀ j, (X.homOfLE hDU ≫ f).appTop (AffineSpace.coord X j) * D.ι.appTop d =
      D.ι.appTop (b j))
    (ci : Spec R ⟶ W.toScheme) (hci : ci ≫ W.ι = chart)
    (hgi : ci ≫ g = AffineSpace.homOfVector (chart ≫ K.blowupMap)
      (fun j ↦ (Scheme.ΓSpecIso R).inv (s j)))
    (hDchart : K.blowupMap ⁻¹ᵁ D ≤ chart.opensRange) :
    K.blowup.homOfLE (K.blowupMap.preimage_mono hDU) ≫ K.blowup.homOfLE hWmem ≫ g =
      K.blowup.homOfLE (K.blowupMap.preimage_mono hDU) ≫ (K.blowupMap ∣_ U) ≫ f := by
  subst hD
  have hrange : Set.range (K.blowupMap ⁻¹ᵁ X.basicOpen d).ι.base ⊆
      Set.range chart.base := by
    intro z hz
    obtain ⟨z, rfl⟩ := hz
    exact hDchart z.2
  obtain ⟨θ, hθ⟩ : ∃ θ : (K.blowupMap ⁻¹ᵁ X.basicOpen d).toScheme ⟶ Spec R,
      θ ≫ chart = (K.blowupMap ⁻¹ᵁ X.basicOpen d).ι :=
    ⟨IsOpenImmersion.lift chart _ hrange, IsOpenImmersion.lift_fac _ _ _⟩
  have hleft : K.blowup.homOfLE (K.blowupMap.preimage_mono hDU) ≫
      K.blowup.homOfLE hWmem = θ ≫ ci := by
    rw [← cancel_mono W.ι, Category.assoc, Category.assoc, hci, Scheme.homOfLE_ι, hθ,
      Scheme.homOfLE_ι]
  rw [← Category.assoc, hleft, Category.assoc, hgi]
  have hres : K.blowup.homOfLE (K.blowupMap.preimage_mono hDU) ≫ (K.blowupMap ∣_ U) =
      (K.blowupMap ∣_ X.basicOpen d) ≫ X.homOfLE hDU := by
    rw [morphismRestrict_homOfLE]
  have hPι : (K.blowupMap ∣_ X.basicOpen d) ≫ (X.basicOpen d).ι =
      (K.blowupMap ⁻¹ᵁ X.basicOpen d).ι ≫ K.blowupMap := morphismRestrict_ι _ _
  have hunit : IsUnit (((K.blowupMap ⁻¹ᵁ X.basicOpen d).ι ≫ K.blowupMap).appTop d) := by
    refine Scheme.isUnit_of_le_basicOpen (le_of_eq ?_)
    rw [← Scheme.preimage_basicOpen_top]
    exact (Scheme.Opens.ι_preimage_self (K.blowupMap ⁻¹ᵁ X.basicOpen d)).symm
  have hθw : ∀ r : Γ(X, ⊤), ((K.blowupMap ⁻¹ᵁ X.basicOpen d).ι ≫ K.blowupMap).appTop r =
      θ.appTop ((chart ≫ K.blowupMap).appTop r) := by
    intro r
    rw [← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop, ← Category.assoc, hθ]
  have hρw : ∀ r : Γ(X, ⊤), ((K.blowupMap ⁻¹ᵁ X.basicOpen d).ι ≫ K.blowupMap).appTop r =
      (K.blowupMap ∣_ X.basicOpen d).appTop ((X.basicOpen d).ι.appTop r) := by
    intro r
    rw [← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop, hPι]
  refine AffineSpace.hom_ext_of_mul_unit ?_ hunit fun j ↦ ?_
  · simp only [Category.assoc, AffineSpace.homOfVector_over, hf, morphismRestrict_ι]
    rw [← Category.assoc, hθ, ← Category.assoc, Scheme.homOfLE_ι]
  · have hL : ((K.blowupMap ⁻¹ᵁ X.basicOpen d).ι ≫ K.blowupMap).appTop d *
        (θ ≫ AffineSpace.homOfVector (chart ≫ K.blowupMap)
          (fun j ↦ (Scheme.ΓSpecIso R).inv (s j))).appTop (AffineSpace.coord X j) =
        ((K.blowupMap ⁻¹ᵁ X.basicOpen d).ι ≫ K.blowupMap).appTop (b j) := by
      rw [AffineSpace.comp_homOfVector_appTop_coord, hθw d, hθw (b j), hφ d, hφ (b j),
        ← map_mul, ← map_mul, hs j]
    have hR : ((K.blowupMap ⁻¹ᵁ X.basicOpen d).ι ≫ K.blowupMap).appTop d *
        (K.blowup.homOfLE (K.blowupMap.preimage_mono hDU) ≫
          (K.blowupMap ∣_ U) ≫ f).appTop (AffineSpace.coord X j) =
        ((K.blowupMap ⁻¹ᵁ X.basicOpen d).ι ≫ K.blowupMap).appTop (b j) := by
      have hmul : (X.basicOpen d).ι.appTop d *
          (X.homOfLE hDU ≫ f).appTop (AffineSpace.coord X j) =
          (X.basicOpen d).ι.appTop (b j) := by
        rw [mul_comm]
        exact hcoord j
      rw [← Category.assoc, hres, Category.assoc, hρw d, hρw (b j),
        Scheme.Hom.comp_appTop, CommRingCat.comp_apply, ← map_mul, hmul]
    exact hL.trans hR.symm

end Gluing

end AlgebraicGeometry
