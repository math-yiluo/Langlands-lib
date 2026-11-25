/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import WeilConjectures.Blowup.EliminationOfIndeterminacy.ChartPreimage
public import WeilConjectures.Blowup.EliminationOfIndeterminacy.Gluing
public import WeilConjectures.Mathlib.AlgebraicGeometry.OpenImmersion

/-!
# The chart-local coordinate identities of the glued extension

On the overlap of two charts of the blow-up, the coordinates of the glued extension to relative
affine space are the expected fractions of slopes
(`AlgebraicGeometry.Scheme.IdealSheafData.mul_appTop_coord_awaySlope`).
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory Limits HomogeneousLocalization

namespace AlgebraicGeometry
section Closedness

variable {A : Type u} [CommRing A] {I : Ideal A}
variable {X : Scheme.{u}}

/-- **The chart-local coordinate identity for the graph of the extension.** On the overlap of
the `S`-chart with the `Ri`-chart, the `j`-th coordinate of the graph is the fraction
`wS / vS`, which is the coordinate `si j` of the `Ri`-chart. -/
lemma AffineSpace.mul_appTop_coord_eq_of_chartOverlap {σ : Type u} {X Bl : Scheme.{u}}
    (π : Bl ⟶ X) {W : Bl.Opens} (g : W.toScheme ⟶ 𝔸(σ; X))
    {S : CommRingCat.{u}} (chart : Spec S ⟶ Bl)
    (lam : (chart ⁻¹ᵁ W).toScheme ⟶ W.toScheme)
    (hlam : lam ≫ W.ι = (chart ⁻¹ᵁ W).ι ≫ chart)
    {Ri : CommRingCat.{u}} (charti : Spec Ri ⟶ Bl) (cii : Spec Ri ⟶ W.toScheme)
    (hcii : cii ≫ W.ι = charti) (si : σ → Ri)
    (hgii : cii ≫ g = AffineSpace.homOfVector (charti ≫ π)
      (fun j ↦ (Scheme.ΓSpecIso Ri).inv (si j)))
    {B : (Spec S).Opens} (hB : B ≤ chart ⁻¹ᵁ W)
    {T : CommRingCat.{u}} (m₁ : Spec T ⟶ Spec S) (m₂ : Spec T ⟶ Spec Ri)
    (hm : m₁ ≫ chart = m₂ ≫ charti)
    (m₁' : Spec T ⟶ B.toScheme) [IsIso m₁'] (hm₁' : m₁' ≫ B.ι = m₁)
    (vS wS : S) (j : σ)
    (hval : m₂.appTop ((Scheme.ΓSpecIso Ri).inv (si j)) *
      m₁.appTop ((Scheme.ΓSpecIso S).inv vS) = m₁.appTop ((Scheme.ΓSpecIso S).inv wS)) :
    ((Spec S).homOfLE hB ≫ AffineSpace.homOfVector (chart ⁻¹ᵁ W).ι
        (fun j ↦ (lam ≫ g).appTop (AffineSpace.coord X j))).appTop
        (AffineSpace.coord (Spec S) j) *
      ((Scheme.ΓSpecIso S).inv ≫ B.ι.appTop) vS =
      ((Scheme.ΓSpecIso S).inv ≫ B.ι.appTop) wS := by
  -- `m₁'` is an isomorphism, so its action on global sections is injective
  have hidcomp : m₁'.appTop ≫ (inv m₁').appTop = 𝟙 _ := by
    rw [← Scheme.Hom.comp_appTop]
    simp
  have hinj : Function.Injective (m₁'.appTop) := by
    intro x y hxy
    have h1 : (inv m₁').appTop (m₁'.appTop x) = (inv m₁').appTop (m₁'.appTop y) := by rw [hxy]
    rwa [← CommRingCat.comp_apply, ← CommRingCat.comp_apply, hidcomp,
      CommRingCat.id_apply, CommRingCat.id_apply] at h1
  -- the restriction maps of the overlap
  have hres : ∀ r : S, m₁'.appTop (((Scheme.ΓSpecIso S).inv ≫ B.ι.appTop) r) =
      m₁.appTop ((Scheme.ΓSpecIso S).inv r) := by
    intro r
    rw [CommRingCat.comp_apply, ← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop, hm₁']
  -- the overlap maps into the `Ri`-chart
  have hlift : m₁' ≫ (Spec S).homOfLE hB ≫ lam = m₂ ≫ cii := by
    rw [← cancel_mono W.ι]
    simp only [Category.assoc]
    rw [hlam, hcii, ← Category.assoc ((Spec S).homOfLE hB), Scheme.homOfLE_ι,
      ← Category.assoc, hm₁', hm]
  have hstep : ((Spec S).homOfLE hB ≫ AffineSpace.homOfVector (chart ⁻¹ᵁ W).ι
        (fun j ↦ (lam ≫ g).appTop (AffineSpace.coord X j))).appTop
        (AffineSpace.coord (Spec S) j) =
      ((Spec S).homOfLE hB ≫ lam ≫ g).appTop (AffineSpace.coord X j) := by
    rw [AffineSpace.comp_homOfVector_appTop_coord]
    simp only [Scheme.Hom.comp_appTop, CommRingCat.comp_apply]
  have hstep2 : m₁'.appTop (((Spec S).homOfLE hB ≫ lam ≫ g).appTop
      (AffineSpace.coord X j)) = m₂.appTop ((Scheme.ΓSpecIso Ri).inv (si j)) := by
    rw [← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop, reassoc_of% hlift, hgii,
      AffineSpace.comp_homOfVector_appTop_coord]
  apply hinj
  rw [map_mul, hres, hres, ← hval, hstep, hstep2]

/-- **The chart-local coordinate identity for the glued extension.** On the overlap of the
`c`-chart with the `d`-chart of the blow-up, the `j`-th coordinate of the extension is the
fraction `(b j / c) / (d / c)`. -/
lemma Scheme.IdealSheafData.mul_appTop_coord_awaySlope (K : X.IdealSheafData)
    (V : X.affineOpens) {σ : Type u} {W : K.blowup.Opens} (g : W.toScheme ⟶ 𝔸(σ; X))
    {c : Γ(X, V.1)} (hc : c ∈ K.ideal V)
    (lam : (K.blowupChart V hc ⁻¹ᵁ W).toScheme ⟶ W.toScheme)
    (hlam : lam ≫ W.ι = (K.blowupChart V hc ⁻¹ᵁ W).ι ≫ K.blowupChart V hc)
    {d : Γ(X, V.1)} (hd : d ∈ K.ideal V)
    {b : σ → Γ(X, V.1)} (hb : ∀ j, b j ∈ K.ideal V)
    (cid : Spec (.of (HomogeneousLocalization.Away (reesGrading (K.ideal V))
      (reesX (K.ideal V) d hd))) ⟶ W.toScheme)
    (hcid : cid ≫ W.ι = K.blowupChart V hd)
    (hgid : cid ≫ g = AffineSpace.homOfVector (K.blowupChart V hd ≫ K.blowupMap)
      (fun j ↦ (Scheme.ΓSpecIso _).inv (AffineBlowup.awaySlope (K.ideal V) hd (hb j))))
    {B : (Spec (.of (HomogeneousLocalization.Away (reesGrading (K.ideal V))
      (reesX (K.ideal V) c hc)))).Opens}
    (hBdef : B = PrimeSpectrum.basicOpen (AffineBlowup.awaySlope (K.ideal V) hc hd))
    (hBle : B ≤ K.blowupChart V hc ⁻¹ᵁ W) (j : σ) :
    ((Spec (.of (HomogeneousLocalization.Away (reesGrading (K.ideal V))
        (reesX (K.ideal V) c hc)))).homOfLE hBle ≫
        AffineSpace.homOfVector (K.blowupChart V hc ⁻¹ᵁ W).ι
          (fun j ↦ (lam ≫ g).appTop (AffineSpace.coord X j))).appTop
        (AffineSpace.coord (Spec (.of (HomogeneousLocalization.Away
          (reesGrading (K.ideal V)) (reesX (K.ideal V) c hc)))) j) *
      ((Scheme.ΓSpecIso _).inv ≫ B.ι.appTop)
        (AffineBlowup.awaySlope (K.ideal V) hc hd) =
      ((Scheme.ΓSpecIso _).inv ≫ B.ι.appTop)
        (AffineBlowup.awaySlope (K.ideal V) hc (hb j)) := by
  subst hBdef
  have hpbi := K.isPullback_blowupChart V hc hd
  -- Elaborating the lift before destructuring it avoids a slow unification.
  have hex := exists_isIso_lift_of_mem_iff _ hpbi.isOpenImmersion_fst
    (AffineBlowup.mem_range_specMap_awayMap_iff hc hd)
  obtain ⟨m₁', hm₁'iso, hm₁'⟩ := hex
  -- `Scheme.specMap_appTop_ΓSpecIso_inv_mul_eq` moves the identity to `Spec` over abstract rings,
  -- so that it is not checked on the concrete chart rings.
  exact AffineSpace.mul_appTop_coord_eq_of_chartOverlap K.blowupMap g
    (K.blowupChart V hc) lam hlam (K.blowupChart V hd) cid hcid _ hgid hBle _ _ hpbi.w
    m₁' hm₁' _ _ j (Scheme.specMap_appTop_ΓSpecIso_inv_mul_eq _ _ _ _ _
      (AffineBlowup.awayMap_awaySlope_mul hc hd (hb j)))

end Closedness

end AlgebraicGeometry
