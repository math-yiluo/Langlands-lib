import Langlands.Geometry.Analytic.SaturatedStrongQuasiIsomorphisms

/-! # Strong isomorphisms are full quasi-isomorphisms -/

noncomputable section

universe u v w

namespace Langlands.Analytic.SaturatedAtlasPresentation

open CategoryTheory Set PresentedAffinoidAlgebra IndexedAffinoidAtlas

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {A B : SaturatedAtlasPresentation.{u, v, w} K}

private theorem pullback_eq_of_eq {f g : A ⟶ B} (he : f = g)
    (i : A.presentation.atlas.Index) (j : B.presentation.atlas.Index)
    (hf : f.baseMap '' Set.range (A.presentation.atlas.chart i) ⊆
      Set.range (B.presentation.atlas.chart j))
    (hg : g.baseMap '' Set.range (A.presentation.atlas.chart i) ⊆
      Set.range (B.presentation.atlas.chart j)) :
    f.pullback i j hf = g.pullback i j hg := by
  cases he
  rfl

/-- Actual inverse strong maps imply the full affinoid-test
quasi-isomorphism property. -/
theorem isQuasiIso_of_inverse (f : A ⟶ B) (g : B ⟶ A)
    (hfg : f ≫ g = 𝟙 A) (hgf : g ≫ f = 𝟙 B) : f.IsQuasiIso := by
  have hfgx : ∀ x : A.presentation.space, g.baseMap (f.baseMap x) = x :=
    fun x => congrArg (fun m : A ⟶ A => m.baseMap x) hfg
  have hgfx : ∀ y : B.presentation.space, f.baseMap (g.baseMap y) = y :=
    fun y => congrArg (fun m : B ⟶ B => m.baseMap y) hgf
  let e : A.presentation.space ≃ₜ B.presentation.space :=
    { toFun := f.baseMap
      invFun := g.baseMap
      left_inv := hfgx
      right_inv := hgfx
      continuous_toFun := f.baseMap.continuous
      continuous_invFun := g.baseMap.continuous }
  refine ⟨e.isHomeomorph, ?_⟩
  intro i j hf
  obtain ⟨k, hg⟩ := g.target_exists j
  obtain ⟨l, hfl⟩ := f.target_exists k
  have hchainA := f.comp_admissible g i j k hf hg
  have hchainB := g.comp_admissible f j k l hg hfl
  have hik : Set.range (A.presentation.atlas.chart i) ⊆
      Set.range (A.presentation.atlas.chart k) := by
    intro x hx
    exact hfgx x ▸ hchainA ⟨x, hx, rfl⟩
  have hjl : Set.range (B.presentation.atlas.chart j) ⊆
      Set.range (B.presentation.atlas.chart l) := by
    intro y hy
    exact hgfx y ▸ hchainB ⟨y, hy, rfl⟩
  have hAid : (𝟙 A : A ⟶ A).baseMap '' Set.range (A.presentation.atlas.chart i) ⊆
      Set.range (A.presentation.atlas.chart k) := by
    simpa only [baseMap_id, ContinuousMap.coe_id, Set.image_id] using hik
  have hBid : (𝟙 B : B ⟶ B).baseMap '' Set.range (B.presentation.atlas.chart j) ⊆
      Set.range (B.presentation.atlas.chart l) := by
    simpa only [baseMap_id, ContinuousMap.coe_id, Set.image_id] using hjl
  have hA : (f.pullback i j hf).comp (g.pullback j k hg) =
      A.presentation.atlas.restriction i k hik := by
    exact (AffinoidAtlasPresentation.StrongHom.saturatedComp_pullback f g
      A.hasAllLocalDomains B.hasAllLocalDomains i j k hf hg hchainA).symm.trans
        (pullback_eq_of_eq hfg i k hchainA hAid)
  have hB : (g.pullback j k hg).comp (f.pullback k l hfl) =
      B.presentation.atlas.restriction j l hjl := by
    exact (AffinoidAtlasPresentation.StrongHom.saturatedComp_pullback g f
      B.hasAllLocalDomains A.hasAllLocalDomains j k l hg hfl hchainB).symm.trans
        (pullback_eq_of_eq hgf j l hchainB hBid)
  have hgepi : ∀ (R : PresentedAffinoidAlgebra K)
      (α β : BoundedAlgHom K (B.presentation.atlas.algebra j) R),
      α.comp (g.pullback j k hg) = β.comp (g.pullback j k hg) → α = β := by
    intro R α β hαβ
    apply (B.presentation.atlas.restriction_represents j l hjl).hom_ext R
    rw [← hB]
    change (α.comp (g.pullback j k hg)).comp (f.pullback k l hfl) =
      (β.comp (g.pullback j k hg)).comp (f.pullback k l hfl)
    exact congrArg (fun q => q.comp (f.pullback k l hfl)) hαβ
  refine ⟨f.isClosed_chartImageLocus i j hf, f.range_pullback i j hf, ?_⟩
  intro R φ hφ
  have hφg : HasImageIn K (φ.comp (g.pullback j k hg))
      (A.presentation.atlas.chart k ⁻¹' Set.range (A.presentation.atlas.chart i)) := by
    intro t
    change A.presentation.atlas.chart k
      (BanachSpectrum.comap (g.pullback j k hg).toBoundedRingHom
        (BanachSpectrum.comap φ.toBoundedRingHom t)) ∈
          Set.range (A.presentation.atlas.chart i)
    rw [g.chart_comm j k hg]
    have ht := hφ t
    change B.presentation.atlas.chart j (BanachSpectrum.comap φ.toBoundedRingHom t) ∈
      f.baseMap '' Set.range (A.presentation.atlas.chart i) at ht
    obtain ⟨x, hx, he⟩ := ht
    rw [← he, hfgx]
    exact hx
  obtain ⟨ψ, hψ, huniq⟩ :=
    (A.presentation.atlas.restriction_represents i k hik).2.2 R
      (φ.comp (g.pullback j k hg)) hφg
  refine ⟨ψ, ?_, ?_⟩
  · apply hgepi R
    change ψ.comp ((f.pullback i j hf).comp (g.pullback j k hg)) = _
    rw [hA]
    exact hψ
  · intro χ hχ
    apply huniq χ
    rw [← hA]
    change (χ.comp (f.pullback i j hf)).comp (g.pullback j k hg) = _
    rw [hχ]

/-- Every actual isomorphism of the saturated category is a full
quasi-isomorphism, independently of all three universes. -/
theorem isQuasiIso_of_isIso (f : A ⟶ B) [IsIso f] : f.IsQuasiIso :=
  isQuasiIso_of_inverse f (asIso f).inv (asIso f).hom_inv_id (asIso f).inv_hom_id

end Langlands.Analytic.SaturatedAtlasPresentation
