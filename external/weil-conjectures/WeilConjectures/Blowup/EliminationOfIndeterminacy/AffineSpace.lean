/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import WeilConjectures.Blowup.AdmissibleBlowup
public import WeilConjectures.Blowup.EliminationOfIndeterminacy.Closedness
public import WeilConjectures.Blowup.EliminationOfIndeterminacy.CommonDenominator

/-!
# Elimination of indeterminacy for maps to relative affine space

Conrad's Theorem 2.4, Case 1, for a relative affine-space target over an affine base
(`AlgebraicGeometry.exists_isAdmissible_extend_affineSpace`).
(Blueprint: `lemma:nagata-conrad-affine-space-extension`.)
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory Limits HomogeneousLocalization

namespace AlgebraicGeometry
section Statement

/-! ### The main theorem -/

variable {X : Scheme.{u}}

/-- **Extension to relative affine space after one admissible blow-up** (Conrad,
Theorem 2.4, Case 1, the sub-case `Y = 𝔸ⁿ_X`; blueprint:
`lemma:nagata-conrad-affine-space-extension`).

Difference from the informal statement: "agrees with `f` over `U`" is expressed through
the identification of the preimage of `U` with `U` along `B.isIso_blowupMap_restrict`. -/
theorem exists_isAdmissible_extend_affineSpace [IsAffine X]
    {U : X.Opens} (hU : IsCompact (U : Set X)) {σ : Type u} [Finite σ]
    (f : U.toScheme ⟶ 𝔸(σ; X)) (hf : f ≫ 𝔸(σ; X) ↘ X = U.ι) :
    ∃ (B : IsAdmissible X U) (W : B.I.blowup.Opens) (hW : B.I.blowupMap ⁻¹ᵁ U ≤ W)
      (g : W.toScheme ⟶ 𝔸(σ; X)) (hg : g ≫ 𝔸(σ; X) ↘ X = W.ι ≫ B.I.blowupMap),
      B.I.blowup.homOfLE hW ≫ g = (B.I.blowupMap ∣_ U) ≫ f ∧
      IsClosed (Set.range (pullback.lift W.ι g hg.symm)) := by
  classical
  obtain ⟨ι, hιfin, u, hle, N, c, hUeq, hNpos, hrel, hcoord⟩ :=
    exists_uniform_denominator hU f
  -- the centre
  set gen : ι ⊕ ι × σ → Γ(X, ⊤) := Sum.elim (fun i ↦ u i ^ N) (fun p ↦ c p.1 p.2) with hgendef
  set I₀ : Ideal Γ(X, ⊤) := Ideal.span (Set.range gen) with hI₀def
  set V₀ : X.affineOpens := ⟨⊤, isAffineOpen_top X⟩ with hV₀def
  set K : X.IdealSheafData := Scheme.IdealSheafData.ofIdealTop I₀ with hKdef
  have hKV₀ : K.ideal V₀ = I₀ := by
    rw [hKdef, Scheme.IdealSheafData.ofIdealTop_ideal]
    have h1 : (homOfLE (le_top (a := V₀.1))).op = 𝟙 _ := rfl
    rw [h1, CategoryTheory.Functor.map_id, CommRingCat.hom_id, Ideal.map_id]
  have hgen : ∀ k, gen k ∈ K.ideal V₀ := fun k ↦ hKV₀ ▸ Ideal.subset_span ⟨k, rfl⟩
  have hspan : Ideal.span (Set.range gen) = K.ideal V₀ := hKV₀.symm
  have : Finite (ι ⊕ ι × σ) := by
    have := hιfin
    infer_instance
  have hFG : I₀.FG := by
    have := hιfin
    have : Fintype (ι ⊕ ι × σ) := Fintype.ofFinite _
    exact ⟨Finset.image gen Finset.univ, by rw [hI₀def]; congr 1; simp [Set.image_univ]⟩
  have hFT : K.ofFiniteType := by
    intro V _
    rw [hKdef, Scheme.IdealSheafData.ofIdealTop_ideal]
    exact hFG.map _
  have hdisj : Disjoint (U : Set X) (K.support : Set X) := by
    rw [Set.disjoint_left]
    intro x hxU hxs
    rw [hKdef, Scheme.IdealSheafData.coe_support_ofIdealTop, Scheme.mem_zeroLocus_iff] at hxs
    rw [hUeq] at hxU
    obtain ⟨i, hxi⟩ := TopologicalSpace.Opens.mem_iSup.mp hxU
    exact hxs (u i ^ N) (Ideal.subset_span ⟨Sum.inl i, rfl⟩)
      (by rwa [Scheme.basicOpen_pow _ _ hNpos])
  -- the charts at the `u i ^ N` cover the preimage of `U`
  have hPchart : ∀ i : ι, K.blowupMap ⁻¹ᵁ X.basicOpen (u i) ≤
      (K.blowupChart V₀ (hgen (Sum.inl i))).opensRange := by
    intro i x hx
    have hxtop : x ∈ K.blowupMap ⁻¹ᵁ V₀.1 := trivial
    obtain ⟨k, y, rfl⟩ := K.exists_mem_range_blowupChart_of_span V₀ hgen hspan hxtop
    have hxi : K.blowupMap (K.blowupChart V₀ (hgen k) y) ∈ X.basicOpen (u i) := hx
    rw [← Scheme.Hom.comp_apply, K.blowupChart_comp_blowupMap V₀ (hgen k),
      Scheme.Hom.comp_apply] at hxi
    have hy : y ∈ PrimeSpectrum.basicOpen (AffineBlowup.awayAlgebraMap (K.ideal V₀)
        (reesX (K.ideal V₀) (gen k) (hgen k)) (u i)) := by
      have h1 : Spec.map (CommRingCat.ofHom (AffineBlowup.awayAlgebraMap (K.ideal V₀)
          (reesX (K.ideal V₀) (gen k) (hgen k)))) y ∈
          V₀.2.fromSpec ⁻¹ᵁ X.basicOpen (u i) := hxi
      exact (V₀.2.fromSpec_preimage_basicOpen (u i)).le h1
    have hyN : y ∈ PrimeSpectrum.basicOpen (AffineBlowup.awayAlgebraMap (K.ideal V₀)
        (reesX (K.ideal V₀) (gen k) (hgen k)) (u i ^ N)) := by
      rw [map_pow, PrimeSpectrum.basicOpen_pow _ _ hNpos]
      exact hy
    obtain ⟨z, hz⟩ := AffineBlowup.mem_range_chart_of_mem_basicOpen (hgen k)
      (hgen (Sum.inl i)) y hyN
    refine ⟨z, ?_⟩
    rw [Scheme.IdealSheafData.blowupChart, Scheme.IdealSheafData.blowupChart,
      Scheme.Hom.comp_apply, Scheme.Hom.comp_apply, hz]
  -- the open `W`; it is only used through `hWdef`, so it is kept opaque (a `set` would also
  -- try to abstract the supremum in the goal and in all hypotheses)
  obtain ⟨W, hWdef⟩ : ∃ W : K.blowup.Opens,
      W = ⨆ i : ι, (K.blowupChart V₀ (hgen (Sum.inl i))).opensRange := ⟨_, rfl⟩
  have hWmem : K.blowupMap ⁻¹ᵁ U ≤ W := by
    intro x hx
    have hxU : K.blowupMap x ∈ ⨆ i : ι, X.basicOpen (u i) := by rw [← hUeq]; exact hx
    obtain ⟨i, hxi⟩ := TopologicalSpace.Opens.mem_iSup.mp hxU
    rw [hWdef]
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨i, hPchart i hxi⟩
  -- the chart cover of `W` and the glued extension
  have hsub : ∀ i : ι, Set.range (K.blowupChart V₀ (hgen (Sum.inl i))).base ⊆
      Set.range W.ι.base := by
    intro i z hz
    have h1 : (K.blowupChart V₀ (hgen (Sum.inl i))).opensRange ≤ W := by
      rw [hWdef]
      exact le_iSup (fun i : ι ↦ (K.blowupChart V₀ (hgen (Sum.inl i))).opensRange) i
    exact ⟨⟨z, h1 hz⟩, rfl⟩
  let ci : ∀ i : ι, Spec (.of (HomogeneousLocalization.Away (reesGrading (K.ideal V₀))
      (reesX (K.ideal V₀) (gen (Sum.inl i)) (hgen (Sum.inl i))))) ⟶ W.toScheme :=
    fun i ↦ IsOpenImmersion.lift W.ι (K.blowupChart V₀ (hgen (Sum.inl i))) (hsub i)
  have hci : ∀ i, ci i ≫ W.ι = K.blowupChart V₀ (hgen (Sum.inl i)) :=
    fun i ↦ IsOpenImmersion.lift_fac _ _ _
  obtain ⟨g, hg, hgi⟩ := K.exists_hom_affineSpace_of_awaySlope V₀
    (a := fun i ↦ gen (Sum.inl i)) (ha := fun i ↦ hgen (Sum.inl i))
    (b := fun i j ↦ gen (Sum.inr (i, j))) (hb := fun i j ↦ hgen (Sum.inr (i, j)))
    (fun i i' j ↦ hrel i i' j) W hWdef ci hci
  -- the extension agrees with `f` over `U`
  have hagree : K.blowup.homOfLE hWmem ≫ g = (K.blowupMap ∣_ U) ≫ f := by
    have hPle : ∀ i : ι, K.blowupMap ⁻¹ᵁ X.basicOpen (u i) ≤ K.blowupMap ⁻¹ᵁ U :=
      fun i ↦ K.blowupMap.preimage_mono (hle i)
    have hcov2 : ∀ x : (K.blowupMap ⁻¹ᵁ U).toScheme,
        ∃ i y, (K.blowup.homOfLE (hPle i)) y = x := by
      intro x
      have hxU : K.blowupMap x.1 ∈ ⨆ i : ι, X.basicOpen (u i) := by
        rw [← hUeq]; exact x.2
      obtain ⟨i, hxi⟩ := TopologicalSpace.Opens.mem_iSup.mp hxU
      refine ⟨i, ⟨x.1, hxi⟩, (K.blowupMap ⁻¹ᵁ U).ι.isOpenEmbedding.injective ?_⟩
      rw [← Scheme.Hom.comp_apply, Scheme.homOfLE_ι]
      rfl
    refine Scheme.Cover.hom_ext (Scheme.Cover.mkOfCovers ι _
      (fun i ↦ K.blowup.homOfLE (hPle i)) hcov2) _ _ fun i ↦ ?_
    have hfi : (Scheme.Cover.mkOfCovers ι _
      (fun i ↦ K.blowup.homOfLE (hPle i)) hcov2).f i = K.blowup.homOfLE (hPle i) := rfl
    rw [hfi]
    exact K.homOfLE_comp_eq_of_chart hWmem hf g (K.blowupChart V₀ (hgen (Sum.inl i)))
      (CommRingCat.ofHom (AffineBlowup.awayAlgebraMap (K.ideal V₀)
        (reesX (K.ideal V₀) (gen (Sum.inl i)) (hgen (Sum.inl i)))))
      (K.appTop_blowupChart_comp_blowupMap (hgen (Sum.inl i)))
      (fun j ↦ AffineBlowup.awaySlope (K.ideal V₀) (hgen (Sum.inl i))
        (hgen (Sum.inr (i, j))))
      (fun j ↦ by
        rw [mul_comm]
        exact AffineBlowup.awaySlope_mul_awayAlgebraMap (hgen (Sum.inl i))
          (hgen (Sum.inr (i, j))))
      (Scheme.basicOpen_pow (X := X) (f := u i) hNpos) (hle i)
      (hcoord i) (ci i) (hci i) (hgi i) (hPchart i)
  -- the graph of the extension is closed
  have hclosed : IsClosed (Set.range (pullback.lift W.ι g hg.symm)) :=
    K.isClosed_range_pullbackLift_of_awaySlope V₀ (fun i ↦ hgen (Sum.inl i))
      (fun i j ↦ hgen (Sum.inr (i, j))) (fun i i' j ↦ hrel i i' j) hspan
      (fun _ ↦ trivial) hWdef ci hci g hg hgi
  exact ⟨⟨K, hFT, hdisj⟩, W, hWmem, g, hg, hagree, hclosed⟩

end Statement

end AlgebraicGeometry
