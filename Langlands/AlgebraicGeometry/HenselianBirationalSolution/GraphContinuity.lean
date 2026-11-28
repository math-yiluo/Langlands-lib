import Langlands.AlgebraicGeometry.HenselianBirationalSolution.GraphClosure

/-! # Translations agree along the closure of the graph

For translations `τ`, `σ` and a point `(x, y)` of the closure `Γ` of the graph of `σ⁻¹ ∘ τ`,
`τ (x w) = σ (y w)` for all `w` such that both sides are defined (BLR §5.3 Lemma 2). This is an
equality of two morphisms `λ`, `ρ` on an open subscheme `Ω` of `Y ×_S Γ`; it holds on the dense
part lying over the graph itself by associativity, hence everywhere since `Ω` is reduced and `Y`
is separated over `S`.
-/

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Topology

noncomputable section

namespace Langlands.AlgebraicGeometry.HenselianBirationalSolution

/-- A map into an open subspace whose composite with the inclusion has dense range has dense
range. -/
theorem denseRange_of_comp_isOpenEmbedding {α β γ : Type*} [TopologicalSpace α]
    [TopologicalSpace β] [TopologicalSpace γ] {j : β → γ} (hj : IsOpenEmbedding j) {h : α → β}
    (hd : DenseRange (j ∘ h)) : DenseRange h := by
  rw [DenseRange, dense_iff_inter_open]
  intro N hN ⟨b, hb⟩
  obtain ⟨_, ⟨n, hnN, rfl⟩, ⟨t, ht⟩⟩ :=
    (dense_iff_inter_open.mp hd) (j '' N) (hj.isOpenMap _ hN) ⟨j b, b, hb, rfl⟩
  refine ⟨h t, ?_, t, rfl⟩
  have : h t = n := hj.injective ht
  rw [this]
  exact hnN

variable {S Y : Scheme.{u}} {g : Y ⟶ S} {m : BirationalGroupLaw g}

/-- Points `(x, w)` of the domain of `m` with `x w` in `D`, as a subset of `Y ×_S Y`. -/
abbrev leftIn (m : BirationalGroupLaw g) (D : Y.Opens) : Set ↥(pullback g g) :=
  leftPre m (pullback.snd g g ⁻¹' (D : Set Y))

theorem isOpen_leftIn (D : Y.Opens) : IsOpen (leftIn m D) :=
  isOpen_leftPre m (D.isOpen.preimage (pullback.snd g g).continuous)

theorem fibreGenerizationDense_leftIn (hs : IsStrictDomain m) {D : Y.Opens}
    (hD : FibreGenerizationDense g (D : Set Y)) :
    FibreGenerizationDense (pullback.fst g g) (leftIn m D) :=
  fibreGenerizationDense_leftPre m hs.domain_fst (fibreGenerizationDense_snd_preimage hD)

/-- If `(x, w)` lies in `leftIn m D` then `x w` lies in `D`. -/
theorem range_mulPt_subset {T : Scheme.{u}} {x w : T ⟶ Y} {h : x ≫ g = w ≫ g}
    {D : Y.Opens} (hA : PairIn x w h (leftIn m D)) :
    ∃ hd : m.Defined x w h, Set.range (m.mulPt x w h hd) ⊆ D := by
  have hd : m.Defined x w h := hA.mono (leftPre_subset m _)
  refine ⟨hd, ?_⟩
  rintro _ ⟨t, rfl⟩
  obtain ⟨d, hdA, hdt⟩ := hA ⟨t, rfl⟩
  have hl : m.liftDom x w h hd t = d := by
    apply m.domain.ι.isOpenEmbedding.injective
    rw [hdt, ← Scheme.Hom.comp_apply, BirationalGroupLaw.liftDom_ι]
  change (m.liftDom x w h hd ≫ m.mul) t ∈ D
  rw [Scheme.Hom.comp_apply, hl, ← m.leftT_snd, Scheme.Hom.comp_apply]
  exact hdA

/-- The product `x w`, as a point of `D`, for `(x, w)` in `leftIn m D`. -/
def mulIn {T : Scheme.{u}} {x w : T ⟶ Y} {h : x ≫ g = w ≫ g} {D : Y.Opens}
    (hA : PairIn x w h (leftIn m D)) : T ⟶ D.toScheme :=
  IsOpenImmersion.lift D.ι (m.mulPt x w h (hA.mono (leftPre_subset m _)))
    (by rw [Scheme.Opens.range_ι]; exact (range_mulPt_subset hA).2)

@[reassoc (attr := simp)]
theorem mulIn_ι {T : Scheme.{u}} {x w : T ⟶ Y} {h : x ≫ g = w ≫ g} {D : Y.Opens}
    (hA : PairIn x w h (leftIn m D)) :
    mulIn hA ≫ D.ι = m.mulPt x w h (hA.mono (leftPre_subset m _)) :=
  IsOpenImmersion.lift_fac _ _ _

theorem comp_mulIn {T T' : Scheme.{u}} {x w : T ⟶ Y} {h : x ≫ g = w ≫ g} {D : Y.Opens}
    (hA : PairIn x w h (leftIn m D)) (φ : T' ⟶ T) :
    φ ≫ mulIn hA = mulIn (hA.comp φ) := by
  rw [← cancel_mono D.ι, Category.assoc, mulIn_ι, mulIn_ι, m.comp_mulPt]

theorem mulIn_congr {T : Scheme.{u}} {x w x' w' : T ⟶ Y} {h : x ≫ g = w ≫ g}
    {h' : x' ≫ g = w' ≫ g} {D : Y.Opens} (hA : PairIn x w h (leftIn m D))
    (hA' : PairIn x' w' h' (leftIn m D)) (hx : x = x') (hw : w = w') :
    mulIn hA = mulIn hA' := by
  subst hx hw
  rfl

namespace Translation

variable (τ σ : Translation m)

/-- The structure morphism of the closure of the graph. -/
abbrev baseΓ : graphImage τ σ ⟶ S := pr₁ τ σ ≫ g

theorem pr₂_comp_g : pr₂ τ σ ≫ g = baseΓ τ σ := (pr₁_comp_g τ σ).symm

/-- The scheme `Y ×_S Γ` of triples `(x, y, w)` with `(x, y) ∈ Γ`. -/
abbrev triples : Scheme.{u} := pullback g (baseΓ τ σ)

/-- `(x, y, w) ↦ (x, w)`. -/
abbrev tripleXW : triples τ σ ⟶ pullback g g := pairFst (pr₁ τ σ) rfl

/-- `(x, y, w) ↦ (y, w)`. -/
abbrev tripleYW : triples τ σ ⟶ pullback g g := pairFst (pr₂ τ σ) (pr₂_comp_g τ σ)

/-- The open subscheme of triples `(x, y, w)` with `x w` defined in the domain of `τ` and `y w`
defined in the domain of `σ`. -/
def omega : (triples τ σ).Opens :=
  ⟨tripleXW τ σ ⁻¹' leftIn m τ.dom ∩ tripleYW τ σ ⁻¹' leftIn m σ.dom,
    ((isOpen_leftIn τ.dom).preimage (tripleXW τ σ).continuous).inter
      ((isOpen_leftIn σ.dom).preimage (tripleYW τ σ).continuous)⟩

/-- The coordinate `x` on `omega`. -/
abbrev xΩ : (omega τ σ).toScheme ⟶ Y := (omega τ σ).ι ≫ pullback.snd g _ ≫ pr₁ τ σ

/-- The coordinate `y` on `omega`. -/
abbrev yΩ : (omega τ σ).toScheme ⟶ Y := (omega τ σ).ι ≫ pullback.snd g _ ≫ pr₂ τ σ

/-- The coordinate `w` on `omega`. -/
abbrev wΩ : (omega τ σ).toScheme ⟶ Y := (omega τ σ).ι ≫ pullback.fst g _

theorem xΩ_g : xΩ τ σ ≫ g = wΩ τ σ ≫ g := by
  simp only [Category.assoc, pullback.condition]

theorem yΩ_g : yΩ τ σ ≫ g = wΩ τ σ ≫ g := by
  have h1 : pr₂ τ σ ≫ g = baseΓ τ σ := pr₂_comp_g τ σ
  calc yΩ τ σ ≫ g = (omega τ σ).ι ≫ pullback.snd g _ ≫ (pr₂ τ σ ≫ g) := by
        simp only [Category.assoc]
    _ = (omega τ σ).ι ≫ pullback.snd g _ ≫ baseΓ τ σ := by rw [h1]
    _ = wΩ τ σ ≫ g := by rw [← pullback.condition]; simp only [Category.assoc]

theorem pairIn_xΩ : PairIn (xΩ τ σ) (wΩ τ σ) (xΩ_g τ σ) (leftIn m τ.dom) := by
  have he : pullback.lift (xΩ τ σ) (wΩ τ σ) (xΩ_g τ σ) = (omega τ σ).ι ≫ tripleXW τ σ := by
    apply pullback.hom_ext <;> simp
  rintro _ ⟨t, rfl⟩
  rw [he, Scheme.Hom.comp_apply]
  exact (t.2 : _).1

theorem pairIn_yΩ : PairIn (yΩ τ σ) (wΩ τ σ) (yΩ_g τ σ) (leftIn m σ.dom) := by
  have he : pullback.lift (yΩ τ σ) (wΩ τ σ) (yΩ_g τ σ) = (omega τ σ).ι ≫ tripleYW τ σ := by
    apply pullback.hom_ext <;> simp
  rintro _ ⟨t, rfl⟩
  rw [he, Scheme.Hom.comp_apply]
  exact (t.2 : _).2

/-- `λ (x, y, w) = τ (x w)`. -/
def lam : (omega τ σ).toScheme ⟶ Y := mulIn (pairIn_xΩ τ σ) ≫ τ.map

/-- `ρ (x, y, w) = σ (y w)`. -/
def rho : (omega τ σ).toScheme ⟶ Y := mulIn (pairIn_yΩ τ σ) ≫ σ.map

theorem lam_comp_g : lam τ σ ≫ g = rho τ σ ≫ g := by
  rw [lam, rho, Category.assoc, Category.assoc, τ.map_comp, σ.map_comp, mulIn_ι_assoc,
    mulIn_ι_assoc, m.mulPt_comp_g, m.mulPt_comp_g, xΩ_g, yΩ_g]

/-- The structure morphism of the overlap. -/
abbrev baseO : (overlap τ σ).toScheme ⟶ S := (overlap τ σ).ι ≫ g

/-- Triples over the graph itself: `Y ×_S (overlap τ σ)`. -/
abbrev overTriples : Scheme.{u} := pullback g (baseO τ σ)

theorem toImage_baseΓ : (graph τ σ).toImage ≫ baseΓ τ σ = baseO τ σ := by
  rw [← Category.assoc, toImage_pr₁]

/-- The base change of `(graph τ σ).toImage` to triples. -/
def kappa : overTriples τ σ ⟶ triples τ σ :=
  pullback.map g (baseO τ σ) g (baseΓ τ σ) (𝟙 Y) (graph τ σ).toImage (𝟙 S) (by simp)
    (by rw [Category.comp_id, toImage_baseΓ])

@[reassoc (attr := simp)]
theorem kappa_fst : kappa τ σ ≫ pullback.fst g (baseΓ τ σ) = pullback.fst g (baseO τ σ) := by
  simp [kappa]

@[reassoc (attr := simp)]
theorem kappa_snd : kappa τ σ ≫ pullback.snd g (baseΓ τ σ) =
    pullback.snd g (baseO τ σ) ≫ (graph τ σ).toImage := by
  simp [kappa]

theorem isPullback_kappa : IsPullback (kappa τ σ) (pullback.snd g (baseO τ σ))
    (pullback.snd g (baseΓ τ σ)) (graph τ σ).toImage := by
  refine IsPullback.of_right (h₁₂ := pullback.fst g (baseΓ τ σ)) (h₂₂ := baseΓ τ σ) (v₁₃ := g)
    ?_ (kappa_snd τ σ) (IsPullback.of_hasPullback g (baseΓ τ σ))
  rw [kappa_fst, toImage_baseΓ]
  exact IsPullback.of_hasPullback g (baseO τ σ)

instance [IsNoetherian Y] : IsOpenImmersion (kappa τ σ) :=
  MorphismProperty.of_isPullback (isPullback_kappa τ σ).flip inferInstance

/-- `σ ∘ (σ⁻¹ ∘ τ) = τ` on the overlap, as a point. -/
abbrev vO : (overlap τ σ).toScheme ⟶ Y := overlapIncl τ σ ≫ τ.map

theorem vO_g : vO τ σ ≫ g = baseO τ σ := by
  rw [Category.assoc, τ.map_comp, Scheme.homOfLE_ι_assoc]

/-- `(x, w) ↦ (x, w)` over the overlap. -/
abbrev oXW : overTriples τ σ ⟶ pullback g g := pairFst (overlap τ σ).ι rfl

/-- `(x, w) ↦ ((σ⁻¹ ∘ τ) x, w)` over the overlap. -/
abbrev oYW : overTriples τ σ ⟶ pullback g g := pairFst (trans τ σ) (trans_comp_g τ σ)

/-- `(x, w) ↦ (τ x, w)` over the overlap. -/
abbrev oVW : overTriples τ σ ⟶ pullback g g := pairFst (vO τ σ) (vO_g τ σ)

/-- The triples over the graph where all products used below are defined. -/
def gOpen : (overTriples τ σ).Opens :=
  ⟨oXW τ σ ⁻¹' leftIn m τ.dom ∩ oYW τ σ ⁻¹' leftIn m σ.dom ∩ oVW τ σ ⁻¹' m.domain,
    (((isOpen_leftIn τ.dom).preimage (oXW τ σ).continuous).inter
      ((isOpen_leftIn σ.dom).preimage (oYW τ σ).continuous)).inter
      (m.domain.isOpen.preimage (oVW τ σ).continuous)⟩

theorem kappa_tripleXW : kappa τ σ ≫ tripleXW τ σ = oXW τ σ := by
  apply pullback.hom_ext
  · simp only [Category.assoc, pullback.lift_fst, kappa_snd_assoc, toImage_pr₁]
  · simp only [Category.assoc, pullback.lift_snd, kappa_fst]

theorem kappa_tripleYW : kappa τ σ ≫ tripleYW τ σ = oYW τ σ := by
  apply pullback.hom_ext
  · simp only [Category.assoc, pullback.lift_fst, kappa_snd_assoc, toImage_pr₂]
  · simp only [Category.assoc, pullback.lift_snd, kappa_fst]

theorem range_gOpen_kappa : Set.range ((gOpen τ σ).ι ≫ kappa τ σ) ⊆ Set.range (omega τ σ).ι := by
  rintro _ ⟨t, rfl⟩
  rw [Scheme.Opens.range_ι]
  have ht := (t.2 : _)
  have h1 : tripleXW τ σ (kappa τ σ ((gOpen τ σ).ι t)) ∈ leftIn m τ.dom := by
    rw [← Scheme.Hom.comp_apply, kappa_tripleXW]
    exact ht.1.1
  have h2 : tripleYW τ σ (kappa τ σ ((gOpen τ σ).ι t)) ∈ leftIn m σ.dom := by
    rw [← Scheme.Hom.comp_apply, kappa_tripleYW]
    exact ht.1.2
  rw [Scheme.Hom.comp_apply]
  exact ⟨h1, h2⟩

/-- The inclusion of the triples over the graph into `omega`. -/
def gToOmega : (gOpen τ σ).toScheme ⟶ (omega τ σ).toScheme :=
  IsOpenImmersion.lift (omega τ σ).ι ((gOpen τ σ).ι ≫ kappa τ σ) (range_gOpen_kappa τ σ)

@[reassoc (attr := simp)]
theorem gToOmega_ι : gToOmega τ σ ≫ (omega τ σ).ι = (gOpen τ σ).ι ≫ kappa τ σ :=
  IsOpenImmersion.lift_fac _ _ _

theorem fibreGenerizationDense_gOpen (hs : IsStrictDomain m) :
    FibreGenerizationDense (pullback.snd g (baseO τ σ)) (gOpen τ σ : Set _) := by
  refine FibreGenerizationDense.inter (FibreGenerizationDense.inter ?_ ?_ ?_)
    (fibreGenerizationDense_pairFst _ _ hs.domain_fst)
    (((isOpen_leftIn τ.dom).preimage (oXW τ σ).continuous).inter
      ((isOpen_leftIn σ.dom).preimage (oYW τ σ).continuous))
  · exact fibreGenerizationDense_pairFst _ _ (fibreGenerizationDense_leftIn hs τ.dom_dense)
  · exact fibreGenerizationDense_pairFst _ _ (fibreGenerizationDense_leftIn hs σ.dom_dense)
  · exact (isOpen_leftIn τ.dom).preimage (oXW τ σ).continuous

theorem denseRange_gToOmega [IsNoetherian Y] [Smooth g] (hs : IsStrictDomain m) :
    DenseRange (gToOmega τ σ) := by
  apply denseRange_of_comp_isOpenEmbedding (omega τ σ).ι.isOpenEmbedding
  have hfun : ⇑(omega τ σ).ι ∘ ⇑(gToOmega τ σ) = ⇑(kappa τ σ) ∘ ⇑(gOpen τ σ).ι := by
    ext t
    simp only [Function.comp_apply]
    rw [← Scheme.Hom.comp_apply, gToOmega_ι, Scheme.Hom.comp_apply]
  rw [hfun]
  have hκd : DenseRange (kappa τ σ) := by
    have himg := Scheme.image_preimage_eq_of_isPullback (isPullback_kappa τ σ).flip Set.univ
    rw [Set.preimage_univ, Set.image_univ, Set.image_univ] at himg
    rw [DenseRange, himg]
    exact (graph τ σ).toImage.denseRange.preimage (pullback.snd g (baseΓ τ σ)).isOpenMap
  have hGd : DenseRange (gOpen τ σ).ι := by
    rw [DenseRange, Scheme.Opens.range_ι]
    exact FibreGenerizationDense.dense (fibreGenerizationDense_gOpen τ σ hs)
  exact hκd.comp hGd (kappa τ σ).continuous

/-- **BLR §5.3 Lemma 2 for translations.** On `omega`, `τ (x w) = σ (y w)`. -/
theorem lam_eq_rho [IsReduced Y] [Smooth g] [IsSeparated g] [IsNoetherian Y]
    (hs : IsStrictDomain m) : lam τ σ = rho τ σ := by
  have : IsReduced (graphImage τ σ) := isReduced_image (graph τ σ)
  have : IsReduced (triples τ σ) :=
    SmoothReducedBase.isReduced_of_smooth_of_isReduced (pullback.snd g (baseΓ τ σ))
  have : IsDominant (gToOmega τ σ) := ⟨denseRange_gToOmega τ σ hs⟩
  refine ext_of_isDominant_of_isSeparated g (lam_comp_g τ σ) (gToOmega τ σ) ?_
  set qG := (gOpen τ σ).ι ≫ pullback.snd g (baseO τ σ) with hqG
  set wG := (gOpen τ σ).ι ≫ pullback.fst g (baseO τ σ) with hwG
  have hx : gToOmega τ σ ≫ xΩ τ σ = qG ≫ (overlap τ σ).ι := by
    simp only [xΩ, gToOmega_ι_assoc, kappa_snd_assoc, Scheme.Hom.toImage_imageι_assoc,
      graph_fst, hqG, Category.assoc]
  have hy : gToOmega τ σ ≫ yΩ τ σ = qG ≫ trans τ σ := by
    simp only [yΩ, gToOmega_ι_assoc, kappa_snd_assoc, Scheme.Hom.toImage_imageι_assoc,
      graph_snd, hqG, Category.assoc]
  have hw : gToOmega τ σ ≫ wΩ τ σ = wG := by
    simp only [wΩ, gToOmega_ι_assoc, kappa_fst, hwG]
  set a := qG ≫ overlapIncl τ σ with hadef
  have ha : a ≫ τ.dom.ι = qG ≫ (overlap τ σ).ι := by
    rw [hadef, Category.assoc, Scheme.homOfLE_ι]
  set ℓ := IsOpenImmersion.lift σ.map (overlapIncl τ σ ≫ τ.map) (range_overlapIncl_map τ σ)
    with hℓ
  set a' := qG ≫ ℓ with ha'def
  have ha' : a' ≫ σ.dom.ι = qG ≫ trans τ σ := by
    rw [ha'def, Category.assoc, trans]
  have ha'm : a' ≫ σ.map = a ≫ τ.map := by
    rw [ha'def, hadef, hℓ]
    simp only [Category.assoc, trans_map]
  have h₁ : (a ≫ τ.dom.ι) ≫ g = wG ≫ g := by
    calc (a ≫ τ.dom.ι) ≫ g = (gToOmega τ σ ≫ xΩ τ σ) ≫ g := by rw [ha, hx]
      _ = gToOmega τ σ ≫ (xΩ τ σ ≫ g) := Category.assoc _ _ _
      _ = gToOmega τ σ ≫ (wΩ τ σ ≫ g) := by rw [xΩ_g]
      _ = wG ≫ g := by rw [← Category.assoc, hw]
  have hvg : (a ≫ τ.map) ≫ g = wG ≫ g := by
    rw [Category.assoc, τ.map_comp, ← Category.assoc]
    exact h₁
  have hdv : m.Defined (a ≫ τ.map) wG hvg := by
    have he : pullback.lift (a ≫ τ.map) wG hvg = (gOpen τ σ).ι ≫ oVW τ σ := by
      apply pullback.hom_ext
      · simp only [pullback.lift_fst, Category.assoc, hadef, hqG, vO]
      · simp only [pullback.lift_snd, Category.assoc, hwG]
    rintro _ ⟨t, rfl⟩
    rw [he, Scheme.Hom.comp_apply]
    exact (t.2 : _).2
  have hL : gToOmega τ σ ≫ lam τ σ = m.mulPt (a ≫ τ.map) wG hvg hdv := by
    rw [lam, ← Category.assoc, comp_mulIn]
    have hA := (pairIn_xΩ τ σ).comp (gToOmega τ σ)
    have hd₁ : m.Defined (a ≫ τ.dom.ι) wG h₁ :=
      (hA.mono (leftPre_subset m _)).of_eq (by rw [hx, ha]) hw
    have hb : mulIn hA ≫ τ.dom.ι = m.mulPt (a ≫ τ.dom.ι) wG h₁ hd₁ := by
      rw [mulIn_ι]
      exact m.mulPt_congr (by rw [hx, ha]) hw
    exact τ.equivariant a (mulIn hA) wG h₁ hd₁ hb hvg hdv
  have hR : gToOmega τ σ ≫ rho τ σ = m.mulPt (a ≫ τ.map) wG hvg hdv := by
    rw [rho, ← Category.assoc, comp_mulIn]
    have hB := (pairIn_yΩ τ σ).comp (gToOmega τ σ)
    have h₁' : (a' ≫ σ.dom.ι) ≫ g = wG ≫ g := by
      rw [Category.assoc, ← σ.map_comp, ← Category.assoc, ha'm]
      exact hvg
    have hd₁' : m.Defined (a' ≫ σ.dom.ι) wG h₁' :=
      (hB.mono (leftPre_subset m _)).of_eq (by rw [hy, ha']) hw
    have hb' : mulIn hB ≫ σ.dom.ι = m.mulPt (a' ≫ σ.dom.ι) wG h₁' hd₁' := by
      rw [mulIn_ι]
      exact m.mulPt_congr (by rw [hy, ha']) hw
    have h₂' : (a' ≫ σ.map) ≫ g = wG ≫ g := by
      rw [ha'm]
      exact hvg
    have hd₂' : m.Defined (a' ≫ σ.map) wG h₂' := hdv.of_eq ha'm.symm rfl
    rw [σ.equivariant a' (mulIn hB) wG h₁' hd₁' hb' h₂' hd₂']
    exact m.mulPt_congr ha'm rfl
  rw [hL, hR]

end Translation

end Langlands.AlgebraicGeometry.HenselianBirationalSolution
