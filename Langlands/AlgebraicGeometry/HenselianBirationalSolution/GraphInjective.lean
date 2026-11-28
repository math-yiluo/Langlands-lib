import Langlands.AlgebraicGeometry.HenselianBirationalSolution.GraphContinuity

/-! # The projections of the closure of a graph are injective

Two points of the closure `Γ` of the graph of `σ⁻¹ ∘ τ` with the same first (or second)
coordinate coincide (BLR §5.3, proof of Lemma 3). Over a common point of the fibre product, a
common generic `w` puts both points into `omega`; `τ (x w) = σ (y w)` and `τ (x w) = σ (y' w)`
then give `y w = y' w`, hence `y = y'`.
-/

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Topology

noncomputable section

namespace Langlands.AlgebraicGeometry.HenselianBirationalSolution

variable {S Y : Scheme.{u}} {g : Y ⟶ S}

/-- `Y ×_S T₀` is the base change of `Y ×_S B ⟶ B` along `u : T₀ ⟶ B`. -/
theorem isPullback_map_snd {B T₀ : Scheme.{u}} (b : B ⟶ S) (u : T₀ ⟶ B) (c : T₀ ⟶ S)
    (hc : u ≫ b = c) :
    IsPullback (pullback.map g c g b (𝟙 Y) u (𝟙 S) (by simp) (by rw [Category.comp_id, hc]))
      (pullback.snd g c) (pullback.snd g b) u := by
  refine IsPullback.of_right (h₁₂ := pullback.fst g b) (h₂₂ := b) (v₁₃ := g) ?_ (by simp)
    (IsPullback.of_hasPullback g b)
  rw [pullback.lift_fst, Category.comp_id, hc]
  exact IsPullback.of_hasPullback g c

variable {m : BirationalGroupLaw g}

namespace Translation

variable (τ σ : Translation m)

theorem fibreGenerizationDense_omega (hs : IsStrictDomain m) :
    FibreGenerizationDense (pullback.snd g (baseΓ τ σ)) (omega τ σ : Set _) :=
  FibreGenerizationDense.inter
    (fibreGenerizationDense_pairFst _ _ (fibreGenerizationDense_leftIn hs τ.dom_dense))
    (fibreGenerizationDense_pairFst _ _ (fibreGenerizationDense_leftIn hs σ.dom_dense))
    ((isOpen_leftIn τ.dom).preimage (tripleXW τ σ).continuous)

/-- Over every point of `T₀`, two `T₀`-points of `Γ` with the same image in `S` admit a common
`w` putting both into `omega`. -/
theorem exists_common_omega [Surjective g] (hs : IsStrictDomain m) {T₀ : Scheme.{u}}
    (v v' : T₀ ⟶ graphImage τ σ) (h : v ≫ baseΓ τ σ = v' ≫ baseΓ τ σ) (t₀ : T₀) :
    ∃ e : ↥(pullback g (v ≫ baseΓ τ σ)), pullback.snd g _ e = t₀ ∧
      pullback.map g (v ≫ baseΓ τ σ) g (baseΓ τ σ) (𝟙 Y) v (𝟙 S) (by simp)
        (by rw [Category.comp_id]) e ∈ omega τ σ ∧
      pullback.map g (v ≫ baseΓ τ σ) g (baseΓ τ σ) (𝟙 Y) v' (𝟙 S) (by simp)
        (by rw [Category.comp_id, h]) e ∈ omega τ σ := by
  have h₁ := FibreGenerizationDense.preimage_of_isPullback
    (isPullback_map_snd (g := g) (baseΓ τ σ) v (v ≫ baseΓ τ σ) rfl)
    (fibreGenerizationDense_omega τ σ hs)
  have h₂ := FibreGenerizationDense.preimage_of_isPullback
    (isPullback_map_snd (g := g) (baseΓ τ σ) v' (v ≫ baseΓ τ σ) h.symm)
    (fibreGenerizationDense_omega τ σ hs)
  have h₃ := FibreGenerizationDense.inter h₁ h₂
    ((omega τ σ).isOpen.preimage (Scheme.Hom.continuous _))
  obtain ⟨y, hy⟩ := g.surjective ((v ≫ baseΓ τ σ) t₀)
  obtain ⟨x₀, -, hx₀⟩ := Scheme.Pullback.exists_preimage_pullback y t₀ hy
  obtain ⟨e, ⟨he₁, he₂⟩, hes⟩ := FibreGenerizationDense.exists_mem h₃ x₀
  exact ⟨e, hes.trans hx₀, he₁, he₂⟩

/-- A point `e` of a scheme `E` mapped into `omega` gives a point of `omega` with values in the
residue field of `e`. -/
theorem exists_omega_point {E : Scheme.{u}} (ψ : E ⟶ triples τ σ) (e : E)
    (he : ψ e ∈ omega τ σ) :
    ∃ ev : Spec (E.residueField e) ⟶ (omega τ σ).toScheme,
      ev ≫ (omega τ σ).ι = E.fromSpecResidueField e ≫ ψ := by
  have hr : Set.range (E.fromSpecResidueField e ≫ ψ) ⊆ Set.range (omega τ σ).ι := by
    rintro _ ⟨t, rfl⟩
    rw [Scheme.Opens.range_ι, Scheme.Hom.comp_apply, Scheme.fromSpecResidueField_apply]
    exact he
  exact ⟨IsOpenImmersion.lift (omega τ σ).ι _ hr, IsOpenImmersion.lift_fac _ _ _⟩

variable [IsReduced Y] [Smooth g] [IsSeparated g] [IsNoetherian Y] [Surjective g]

omit [Surjective g] in
/-- The values of `lam` and `rho` at a point of `omega`, and their equality. -/
theorem lam_rho_points (hs : IsStrictDomain m) {T : Scheme.{u}}
    (ev : T ⟶ (omega τ σ).toScheme) :
    ev ≫ lam τ σ = mulIn ((pairIn_xΩ τ σ).comp ev) ≫ τ.map ∧
      ev ≫ rho τ σ = mulIn ((pairIn_yΩ τ σ).comp ev) ≫ σ.map ∧
      ev ≫ lam τ σ = ev ≫ rho τ σ := by
  refine ⟨by rw [lam, ← Category.assoc, comp_mulIn], by rw [rho, ← Category.assoc, comp_mulIn],
    by rw [lam_eq_rho τ σ hs]⟩

/-- Two points of `Γ` with the same first coordinate have the same second coordinate after a
field extension. -/
theorem pr₂_eq_of_pr₁_eq (hs : IsStrictDomain m) {T₀ : Scheme.{u}}
    (v v' : T₀ ⟶ graphImage τ σ) (h1 : v ≫ pr₁ τ σ = v' ≫ pr₁ τ σ) (t₀ : T₀) :
    ∃ (T' : Scheme.{u}) (φ : T' ⟶ T₀) (t' : T'), φ t' = t₀ ∧
      φ ≫ v ≫ pr₂ τ σ = φ ≫ v' ≫ pr₂ τ σ := by
  have h : v ≫ baseΓ τ σ = v' ≫ baseΓ τ σ := by
    simp only [baseΓ, ← Category.assoc, h1]
  obtain ⟨e, he0, hev, hev'⟩ := exists_common_omega τ σ hs v v' h t₀
  obtain ⟨ev, hev₁⟩ := exists_omega_point τ σ _ e hev
  obtain ⟨ev', hev₁'⟩ := exists_omega_point τ σ _ e hev'
  set φ := (pullback g (v ≫ baseΓ τ σ)).fromSpecResidueField e ≫
    pullback.snd g (v ≫ baseΓ τ σ) with hφ
  have hx : ev ≫ xΩ τ σ = φ ≫ v ≫ pr₁ τ σ := by
    simp only [xΩ, reassoc_of% hev₁, hφ, Category.assoc, pullback.lift_snd_assoc]
  have hx' : ev' ≫ xΩ τ σ = φ ≫ v' ≫ pr₁ τ σ := by
    simp only [xΩ, reassoc_of% hev₁', hφ, Category.assoc, pullback.lift_snd_assoc]
  have hy : ev ≫ yΩ τ σ = φ ≫ v ≫ pr₂ τ σ := by
    simp only [yΩ, reassoc_of% hev₁, hφ, Category.assoc, pullback.lift_snd_assoc]
  have hy' : ev' ≫ yΩ τ σ = φ ≫ v' ≫ pr₂ τ σ := by
    simp only [yΩ, reassoc_of% hev₁', hφ, Category.assoc, pullback.lift_snd_assoc]
  have hw : ev ≫ wΩ τ σ = ev' ≫ wΩ τ σ := by
    simp only [wΩ, reassoc_of% hev₁, reassoc_of% hev₁', pullback.lift_fst, Category.comp_id]
  have hxx : ev ≫ xΩ τ σ = ev' ≫ xΩ τ σ := by rw [hx, hx', h1]
  obtain ⟨hl, hr, he⟩ := lam_rho_points τ σ hs ev
  obtain ⟨hl', hr', he'⟩ := lam_rho_points τ σ hs ev'
  have hlam : ev ≫ lam τ σ = ev' ≫ lam τ σ := by
    rw [hl, hl', mulIn_congr _ _ hxx hw]
  have hrho : mulIn ((pairIn_yΩ τ σ).comp ev) = mulIn ((pairIn_yΩ τ σ).comp ev') := by
    rw [← cancel_mono σ.map, ← hr, ← hr', ← he, ← he', hlam]
  have hmul := congrArg (· ≫ σ.dom.ι) hrho
  simp only [mulIn_ι] at hmul
  have hyy : ev ≫ yΩ τ σ = ev' ≫ yΩ τ σ := m.mulPt_right_cancel' hw hmul
  have hne : Nonempty ↥(Spec ((pullback g (v ≫ baseΓ τ σ)).residueField e)) :=
    inferInstanceAs (Nonempty (PrimeSpectrum _))
  obtain ⟨t'⟩ := hne
  refine ⟨Spec ((pullback g (v ≫ baseΓ τ σ)).residueField e), φ, t', ?_, ?_⟩
  · rw [hφ, Scheme.Hom.comp_apply, Scheme.fromSpecResidueField_apply]
    exact he0
  · rw [← hy, ← hy', hyy]

/-- Two points of `Γ` with the same second coordinate have the same first coordinate after a
field extension. -/
theorem pr₁_eq_of_pr₂_eq (hs : IsStrictDomain m) {T₀ : Scheme.{u}}
    (v v' : T₀ ⟶ graphImage τ σ) (h2 : v ≫ pr₂ τ σ = v' ≫ pr₂ τ σ) (t₀ : T₀) :
    ∃ (T' : Scheme.{u}) (φ : T' ⟶ T₀) (t' : T'), φ t' = t₀ ∧
      φ ≫ v ≫ pr₁ τ σ = φ ≫ v' ≫ pr₁ τ σ := by
  have h : v ≫ baseΓ τ σ = v' ≫ baseΓ τ σ := by
    rw [← pr₂_comp_g]
    simp only [← Category.assoc, h2]
  obtain ⟨e, he0, hev, hev'⟩ := exists_common_omega τ σ hs v v' h t₀
  obtain ⟨ev, hev₁⟩ := exists_omega_point τ σ _ e hev
  obtain ⟨ev', hev₁'⟩ := exists_omega_point τ σ _ e hev'
  set φ := (pullback g (v ≫ baseΓ τ σ)).fromSpecResidueField e ≫
    pullback.snd g (v ≫ baseΓ τ σ) with hφ
  have hx : ev ≫ xΩ τ σ = φ ≫ v ≫ pr₁ τ σ := by
    simp only [xΩ, reassoc_of% hev₁, hφ, Category.assoc, pullback.lift_snd_assoc]
  have hx' : ev' ≫ xΩ τ σ = φ ≫ v' ≫ pr₁ τ σ := by
    simp only [xΩ, reassoc_of% hev₁', hφ, Category.assoc, pullback.lift_snd_assoc]
  have hy : ev ≫ yΩ τ σ = φ ≫ v ≫ pr₂ τ σ := by
    simp only [yΩ, reassoc_of% hev₁, hφ, Category.assoc, pullback.lift_snd_assoc]
  have hy' : ev' ≫ yΩ τ σ = φ ≫ v' ≫ pr₂ τ σ := by
    simp only [yΩ, reassoc_of% hev₁', hφ, Category.assoc, pullback.lift_snd_assoc]
  have hw : ev ≫ wΩ τ σ = ev' ≫ wΩ τ σ := by
    simp only [wΩ, reassoc_of% hev₁, reassoc_of% hev₁', pullback.lift_fst, Category.comp_id]
  have hyy : ev ≫ yΩ τ σ = ev' ≫ yΩ τ σ := by rw [hy, hy', h2]
  obtain ⟨hl, hr, he⟩ := lam_rho_points τ σ hs ev
  obtain ⟨hl', hr', he'⟩ := lam_rho_points τ σ hs ev'
  have hrho : ev ≫ rho τ σ = ev' ≫ rho τ σ := by
    rw [hr, hr', mulIn_congr _ _ hyy hw]
  have hlam : mulIn ((pairIn_xΩ τ σ).comp ev) = mulIn ((pairIn_xΩ τ σ).comp ev') := by
    rw [← cancel_mono τ.map, ← hl, ← hl', he, he', hrho]
  have hmul := congrArg (· ≫ τ.dom.ι) hlam
  simp only [mulIn_ι] at hmul
  have hxx : ev ≫ xΩ τ σ = ev' ≫ xΩ τ σ := m.mulPt_right_cancel' hw hmul
  have hne : Nonempty ↥(Spec ((pullback g (v ≫ baseΓ τ σ)).residueField e)) :=
    inferInstanceAs (Nonempty (PrimeSpectrum _))
  obtain ⟨t'⟩ := hne
  refine ⟨Spec ((pullback g (v ≫ baseΓ τ σ)).residueField e), φ, t', ?_, ?_⟩
  · rw [hφ, Scheme.Hom.comp_apply, Scheme.fromSpecResidueField_apply]
    exact he0
  · rw [← hx, ← hx', hxx]

/-- **BLR §5.3 Lemma 3, injectivity.** The first projection of the closure of the graph is
injective. -/
theorem injective_pr₁ (hs : IsStrictDomain m) : Function.Injective (pr₁ τ σ) := by
  intro γ γ' hγ
  obtain ⟨ζ, hζ1, hζ2⟩ := Scheme.Pullback.exists_preimage_pullback (f := pr₁ τ σ)
    (g := pr₁ τ σ) γ γ' hγ
  obtain ⟨T', φ, t', hφt, hφ⟩ := pr₂_eq_of_pr₁_eq τ σ hs (pullback.fst (pr₁ τ σ) (pr₁ τ σ))
    (pullback.snd _ _) pullback.condition ζ
  have hc : φ ≫ pullback.fst (pr₁ τ σ) (pr₁ τ σ) = φ ≫ pullback.snd (pr₁ τ σ) (pr₁ τ σ) := by
    rw [← cancel_mono (graph τ σ).imageι]
    apply pullback.hom_ext
    · have := congrArg (φ ≫ ·) (pullback.condition (f := pr₁ τ σ) (g := pr₁ τ σ))
      simpa only [Category.assoc] using this
    · simpa only [Category.assoc] using hφ
  rw [← hζ1, ← hζ2, ← hφt, ← Scheme.Hom.comp_apply, hc, Scheme.Hom.comp_apply]

/-- **BLR §5.3 Lemma 3, injectivity.** The second projection of the closure of the graph is
injective. -/
theorem injective_pr₂ (hs : IsStrictDomain m) : Function.Injective (pr₂ τ σ) := by
  intro γ γ' hγ
  obtain ⟨ζ, hζ1, hζ2⟩ := Scheme.Pullback.exists_preimage_pullback (f := pr₂ τ σ)
    (g := pr₂ τ σ) γ γ' hγ
  obtain ⟨T', φ, t', hφt, hφ⟩ := pr₁_eq_of_pr₂_eq τ σ hs (pullback.fst (pr₂ τ σ) (pr₂ τ σ))
    (pullback.snd _ _) pullback.condition ζ
  have hc : φ ≫ pullback.fst (pr₂ τ σ) (pr₂ τ σ) = φ ≫ pullback.snd (pr₂ τ σ) (pr₂ τ σ) := by
    rw [← cancel_mono (graph τ σ).imageι]
    apply pullback.hom_ext
    · simpa only [Category.assoc] using hφ
    · have := congrArg (φ ≫ ·) (pullback.condition (f := pr₂ τ σ) (g := pr₂ τ σ))
      simpa only [Category.assoc] using this
  rw [← hζ1, ← hζ2, ← hφt, ← Scheme.Hom.comp_apply, hc, Scheme.Hom.comp_apply]

omit [IsReduced Y] [Smooth g] [IsSeparated g] [Surjective g] in
theorem dense_toImage_opensRange :
    Dense ((graph τ σ).toImage.opensRange : Set (graphImage τ σ)) :=
  (graph τ σ).toImage.denseRange

instance :
    IsOpenImmersion ((graph τ σ).toImage.opensRange.ι ≫ pr₁ τ σ) := by
  rw [← Scheme.Hom.isoOpensRange_inv_comp, Category.assoc, toImage_pr₁]
  infer_instance

instance isOpenImmersion_trans : IsOpenImmersion (trans τ σ) := by
  have : IsOpenImmersion (IsOpenImmersion.lift σ.map (overlapIncl τ σ ≫ τ.map)
      (range_overlapIncl_map τ σ)) := by
    have : IsOpenImmersion (IsOpenImmersion.lift σ.map (overlapIncl τ σ ≫ τ.map)
        (range_overlapIncl_map τ σ) ≫ σ.map) := by
      rw [trans_map]
      infer_instance
    exact IsOpenImmersion.of_comp _ σ.map
  rw [trans]
  infer_instance

instance :
    IsOpenImmersion ((graph τ σ).toImage.opensRange.ι ≫ pr₂ τ σ) := by
  rw [← Scheme.Hom.isoOpensRange_inv_comp, Category.assoc, toImage_pr₂]
  infer_instance

/-- **BLR §5.3 Lemma 3.** The first projection of the closure of the graph of `σ⁻¹ ∘ τ` is an
open immersion. -/
theorem isOpenImmersion_pr₁ [QuasiCompact g] (hs : IsStrictDomain m)
    (hY : ∀ y : Y, IsDomain (Y.presheaf.stalk y) ∧ IsIntegrallyClosed (Y.presheaf.stalk y)) :
    IsOpenImmersion (pr₁ τ σ) := by
  have : LocallyQuasiFinite (pr₁ τ σ) := LocallyQuasiFinite.of_injective (injective_pr₁ τ σ hs)
  have : IsReduced (graphImage τ σ) := isReduced_image _
  exact isOpenImmersion_of_birational (pr₁ τ σ) hY _ (dense_toImage_opensRange τ σ)

/-- **BLR §5.3 Lemma 3.** The second projection of the closure of the graph of `σ⁻¹ ∘ τ` is an
open immersion. -/
theorem isOpenImmersion_pr₂ [QuasiCompact g] (hs : IsStrictDomain m)
    (hY : ∀ y : Y, IsDomain (Y.presheaf.stalk y) ∧ IsIntegrallyClosed (Y.presheaf.stalk y)) :
    IsOpenImmersion (pr₂ τ σ) := by
  have : LocallyQuasiFinite (pr₂ τ σ) := LocallyQuasiFinite.of_injective (injective_pr₂ τ σ hs)
  have : IsReduced (graphImage τ σ) := isReduced_image _
  exact isOpenImmersion_of_birational (pr₂ τ σ) hY _ (dense_toImage_opensRange τ σ)

end Translation

end Langlands.AlgebraicGeometry.HenselianBirationalSolution
