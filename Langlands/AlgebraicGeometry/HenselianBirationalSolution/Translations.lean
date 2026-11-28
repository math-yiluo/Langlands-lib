import Langlands.AlgebraicGeometry.HenselianBirationalSolution.StrictLaw

/-! # Base change of the projections of `Y ×_S Y` and translations

For `g : Y ⟶ S`, a scheme `B` over `S` and a `B`-valued point `x` of `Y`, the scheme
`Y ×_S B` is the base change of each projection `Y ×_S Y ⟶ Y` along `x`; fibrewise density
therefore pulls back. The module also proves that the universal left translation maps a
fibrewise dense open subset to a fibrewise dense one in the following sense: the points of the
domain whose image lies in a given fibrewise dense open set are fibrewise dense.
-/

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Topology

noncomputable section

namespace Langlands.AlgebraicGeometry.HenselianBirationalSolution

variable {S Y : Scheme.{u}} {g : Y ⟶ S}

/-- `Y ×_S B ⟶ Y ×_S Y`, `(w, β) ↦ (x β, w)`. -/
abbrev pairFst {B : Scheme.{u}} {b : B ⟶ S} (x : B ⟶ Y) (hx : x ≫ g = b) :
    pullback g b ⟶ pullback g g :=
  pullback.lift (pullback.snd g b ≫ x) (pullback.fst g b)
    (by rw [Category.assoc, hx, pullback.condition])

/-- `Y ×_S B ⟶ Y ×_S Y`, `(w, β) ↦ (w, x β)`. -/
abbrev pairSnd {B : Scheme.{u}} {b : B ⟶ S} (x : B ⟶ Y) (hx : x ≫ g = b) :
    pullback g b ⟶ pullback g g :=
  pullback.lift (pullback.fst g b) (pullback.snd g b ≫ x)
    (by rw [Category.assoc, hx, pullback.condition])

/-- `Y ×_S B` is the base change of the first projection of `Y ×_S Y` along `x`. -/
theorem isPullback_pairFst {B : Scheme.{u}} {b : B ⟶ S} (x : B ⟶ Y) (hx : x ≫ g = b) :
    IsPullback (pairFst x hx) (pullback.snd g b) (pullback.fst g g) x := by
  refine IsPullback.of_right (h₁₂ := pullback.snd g g) (h₂₂ := g) (v₁₃ := g) ?_
    (by simp) (IsPullback.of_hasPullback g g).flip
  rw [pullback.lift_snd, hx]
  exact IsPullback.of_hasPullback g b

/-- `Y ×_S B` is the base change of the second projection of `Y ×_S Y` along `x`. -/
theorem isPullback_pairSnd {B : Scheme.{u}} {b : B ⟶ S} (x : B ⟶ Y) (hx : x ≫ g = b) :
    IsPullback (pairSnd x hx) (pullback.snd g b) (pullback.snd g g) x := by
  refine IsPullback.of_right (h₁₂ := pullback.fst g g) (h₂₂ := g) (v₁₃ := g) ?_
    (by simp) (IsPullback.of_hasPullback g g)
  rw [pullback.lift_fst, hx]
  exact IsPullback.of_hasPullback g b

/-- Fibrewise density for the first projection pulls back along `pairFst`. -/
theorem fibreGenerizationDense_pairFst {B : Scheme.{u}} {b : B ⟶ S} (x : B ⟶ Y)
    (hx : x ≫ g = b) {A : Set ↥(pullback g g)}
    (hA : FibreGenerizationDense (pullback.fst g g) A) :
    FibreGenerizationDense (pullback.snd g b) (pairFst x hx ⁻¹' A) :=
  FibreGenerizationDense.preimage_of_isPullback (isPullback_pairFst x hx) hA

/-- Fibrewise density for the second projection pulls back along `pairSnd`. -/
theorem fibreGenerizationDense_pairSnd {B : Scheme.{u}} {b : B ⟶ S} (x : B ⟶ Y)
    (hx : x ≫ g = b) {A : Set ↥(pullback g g)}
    (hA : FibreGenerizationDense (pullback.snd g g) A) :
    FibreGenerizationDense (pullback.snd g b) (pairSnd x hx ⁻¹' A) :=
  FibreGenerizationDense.preimage_of_isPullback (isPullback_pairSnd x hx) hA

/-- Density over `S` pulls back to density in the fibres of `Y ×_S B ⟶ B`. -/
theorem fibreGenerizationDense_fst_preimage {B : Scheme.{u}} (b : B ⟶ S) {D : Set Y}
    (hD : FibreGenerizationDense g D) :
    FibreGenerizationDense (pullback.snd g b) (pullback.fst g b ⁻¹' D) :=
  fibreGenerizationDense_pullback_snd g b hD

/-- Density over `S` pulls back to density for the first projection, through the second
factor. -/
theorem fibreGenerizationDense_snd_preimage {D : Set Y} (hD : FibreGenerizationDense g D) :
    FibreGenerizationDense (pullback.fst g g) (pullback.snd g g ⁻¹' D) :=
  FibreGenerizationDense.preimage_of_isPullback (IsPullback.of_hasPullback g g).flip hD

/-- Density over `S` pulls back to density for the second projection, through the first
factor. -/
theorem fibreGenerizationDense_fst_preimage' {D : Set Y} (hD : FibreGenerizationDense g D) :
    FibreGenerizationDense (pullback.snd g g) (pullback.fst g g ⁻¹' D) :=
  FibreGenerizationDense.preimage_of_isPullback (IsPullback.of_hasPullback g g) hD

variable (m : BirationalGroupLaw g)

/-- The points of the domain of `m` whose left translate lies in `A`. -/
def leftPre (A : Set ↥(pullback g g)) : Set ↥(pullback g g) :=
  m.domain.ι '' (leftT m ⁻¹' A)

/-- The points of the domain of `m` whose right translate lies in `A`. -/
def rightPre (A : Set ↥(pullback g g)) : Set ↥(pullback g g) :=
  m.domain.ι '' (rightT m ⁻¹' A)

theorem leftPre_subset (A : Set ↥(pullback g g)) : leftPre m A ⊆ m.domain := by
  rintro _ ⟨d, -, rfl⟩
  exact d.2

theorem rightPre_subset (A : Set ↥(pullback g g)) : rightPre m A ⊆ m.domain := by
  rintro _ ⟨d, -, rfl⟩
  exact d.2

theorem isOpen_leftPre {A : Set ↥(pullback g g)} (hA : IsOpen A) : IsOpen (leftPre m A) :=
  m.domain.ι.isOpenEmbedding.isOpenMap _ (hA.preimage (leftT m).continuous)

theorem isOpen_rightPre {A : Set ↥(pullback g g)} (hA : IsOpen A) : IsOpen (rightPre m A) :=
  m.domain.ι.isOpenEmbedding.isOpenMap _ (hA.preimage (rightT m).continuous)

/-- If the domain is dense in the fibres of the first projection, so is the set of its points
whose left translate lies in an open set `A` dense in those fibres. -/
theorem fibreGenerizationDense_leftPre
    (hdom : FibreGenerizationDense (pullback.fst g g) (m.domain : Set ↥(pullback g g)))
    {A : Set ↥(pullback g g)}
    (hA : FibreGenerizationDense (pullback.fst g g) A) :
    FibreGenerizationDense (pullback.fst g g) (leftPre m A) := by
  intro p
  obtain ⟨p₁, hp₁, hfp₁, hp₁p⟩ := hdom p
  obtain ⟨d₁, rfl⟩ : p₁ ∈ Set.range m.domain.ι := by rwa [Scheme.Opens.range_ι]
  obtain ⟨c, hcA, hfc, hcd⟩ := hA (leftT m d₁)
  have hcr : c ∈ Set.range (leftT m) :=
    (leftT m).isOpenEmbedding.isOpen_range.stableUnderGeneralization hcd ⟨d₁, rfl⟩
  obtain ⟨d₂, rfl⟩ := hcr
  have hd₂ : d₂ ⤳ d₁ := (leftT m).isOpenEmbedding.toIsEmbedding.specializes_iff.mp hcd
  refine ⟨m.domain.ι d₂, ⟨d₂, hcA, rfl⟩, ?_, (hd₂.map m.domain.ι.continuous).trans hp₁p⟩
  rw [← hfp₁, ← Scheme.Hom.comp_apply, ← m.leftT_fst, Scheme.Hom.comp_apply, hfc,
    ← Scheme.Hom.comp_apply, m.leftT_fst, Scheme.Hom.comp_apply]

/-- If the domain is dense in the fibres of the second projection, so is the set of its points
whose right translate lies in an open set `A` dense in those fibres. -/
theorem fibreGenerizationDense_rightPre
    (hdom : FibreGenerizationDense (pullback.snd g g) (m.domain : Set ↥(pullback g g)))
    {A : Set ↥(pullback g g)}
    (hA : FibreGenerizationDense (pullback.snd g g) A) :
    FibreGenerizationDense (pullback.snd g g) (rightPre m A) := by
  intro p
  obtain ⟨p₁, hp₁, hfp₁, hp₁p⟩ := hdom p
  obtain ⟨d₁, rfl⟩ : p₁ ∈ Set.range m.domain.ι := by rwa [Scheme.Opens.range_ι]
  obtain ⟨c, hcA, hfc, hcd⟩ := hA (rightT m d₁)
  have hcr : c ∈ Set.range (rightT m) :=
    (rightT m).isOpenEmbedding.isOpen_range.stableUnderGeneralization hcd ⟨d₁, rfl⟩
  obtain ⟨d₂, rfl⟩ := hcr
  have hd₂ : d₂ ⤳ d₁ := (rightT m).isOpenEmbedding.toIsEmbedding.specializes_iff.mp hcd
  refine ⟨m.domain.ι d₂, ⟨d₂, hcA, rfl⟩, ?_, (hd₂.map m.domain.ι.continuous).trans hp₁p⟩
  rw [← hfp₁, ← Scheme.Hom.comp_apply, ← m.rightT_snd, Scheme.Hom.comp_apply, hfc,
    ← Scheme.Hom.comp_apply, m.rightT_snd, Scheme.Hom.comp_apply]

/-- A translation of `Y` compatible with `m`: an open immersion `τ : D ⟶ Y` over `S` of an open
`D` dense in the fibres over `S`, with image dense in the fibres, such that
`τ (x w) = τ (x) w` whenever both sides are defined. -/
structure Translation where
  /-- The domain. -/
  dom : Y.Opens
  /-- The translation. -/
  map : dom.toScheme ⟶ Y
  map_comp : map ≫ g = dom.ι ≫ g
  isOpenImmersion : IsOpenImmersion map
  dom_dense : FibreGenerizationDense g (dom : Set Y)
  range_dense : FibreGenerizationDense g (Set.range map)
  equivariant : ∀ {T : Scheme.{u}} (a b : T ⟶ dom.toScheme) (w : T ⟶ Y)
      (h₁ : (a ≫ dom.ι) ≫ g = w ≫ g) (hd₁ : m.Defined (a ≫ dom.ι) w h₁)
      (_hb : b ≫ dom.ι = m.mulPt (a ≫ dom.ι) w h₁ hd₁)
      (h₂ : (a ≫ map) ≫ g = w ≫ g) (hd₂ : m.Defined (a ≫ map) w h₂),
      b ≫ map = m.mulPt (a ≫ map) w h₂ hd₂

attribute [instance] Translation.isOpenImmersion

variable {m}

/-- The identity translation. -/
def Translation.id : Translation m where
  dom := ⊤
  map := (⊤ : Y.Opens).ι
  map_comp := rfl
  isOpenImmersion := inferInstance
  dom_dense := by
    simpa using fibreGenerizationDense_univ g
  range_dense := by
    rw [Scheme.Opens.range_ι]
    simpa using fibreGenerizationDense_univ g
  equivariant := by
    intro T a b w h₁ hd₁ hb h₂ hd₂
    rw [hb]

/-- The map `y ↦ (c (g y), y)` for a section `c`. -/
abbrev sectionPair (c : S ⟶ Y) (hc : c ≫ g = 𝟙 S) : Y ⟶ pullback g g :=
  pullback.lift (g ≫ c) (𝟙 Y) (by rw [Category.assoc, hc, Category.comp_id, Category.id_comp])

/-- `Y` is the base change of the first projection of `Y ×_S Y` along a section. -/
theorem isPullback_sectionPair (c : S ⟶ Y) (hc : c ≫ g = 𝟙 S) :
    IsPullback (sectionPair c hc) g (pullback.fst g g) c := by
  refine IsPullback.of_right (h₁₂ := pullback.snd g g) (h₂₂ := g) (v₁₃ := g) ?_
    (by simp) (IsPullback.of_hasPullback g g).flip
  rw [pullback.lift_snd, hc]
  exact IsPullback.of_horiz_isIso ⟨by simp⟩

variable (m) in
/-- Over the domain of `m`, the map `y ↦ (c, y)` followed by `m` is the base change of the
universal left translation along `y ↦ (c, y)`. -/
theorem isPullback_sectionPair_restrict (c : S ⟶ Y) (hc : c ≫ g = 𝟙 S) :
    IsPullback (sectionPair c hc ∣_ m.domain) ((sectionPair c hc ∣_ m.domain) ≫ m.mul) (leftT m)
      (sectionPair c hc) := by
  let σ := sectionPair c hc
  have hA : IsPullback σ g (pullback.fst g g) c := isPullback_sectionPair c hc
  have hσ1 : σ ≫ pullback.fst g g = g ≫ c := pullback.lift_fst _ _ _
  have hσ2 : σ ≫ pullback.snd g g = 𝟙 Y := pullback.lift_snd _ _ _
  have hres : (σ ∣_ m.domain) ≫ m.domain.ι = (σ ⁻¹ᵁ m.domain).ι ≫ σ := morphismRestrict_ι _ _
  have hmapg : ((σ ∣_ m.domain) ≫ m.mul) ≫ g = (σ ⁻¹ᵁ m.domain).ι ≫ g := by
    rw [Category.assoc, m.mul_comp, reassoc_of% hres, reassoc_of% hσ1, hc, Category.comp_id]
  have hout := (isPullback_morphismRestrict σ m.domain).paste_vert hA
  refine IsPullback.of_bot ?_ ?_ hA
  · convert hout using 1
    exact m.leftT_fst
  · apply pullback.hom_ext
    · rw [Category.assoc, m.leftT_fst, reassoc_of% hres, hσ1, Category.assoc, Category.assoc,
        hσ1, ← Category.assoc]
      have := congrArg (· ≫ c) hmapg
      simp only [Category.assoc] at this ⊢
      exact this.symm
    · rw [Category.assoc, m.leftT_snd, Category.assoc, hσ2, Category.comp_id]

/-- The map `y ↦ (y, c (g y))` for a section `c`. -/
abbrev sectionPairRight (c : S ⟶ Y) (hc : c ≫ g = 𝟙 S) : Y ⟶ pullback g g :=
  pullback.lift (𝟙 Y) (g ≫ c) (by rw [Category.assoc, hc, Category.comp_id, Category.id_comp])

/-- `Y` is the base change of the second projection of `Y ×_S Y` along a section. -/
theorem isPullback_sectionPairRight (c : S ⟶ Y) (hc : c ≫ g = 𝟙 S) :
    IsPullback (sectionPairRight c hc) g (pullback.snd g g) c := by
  refine IsPullback.of_right (h₁₂ := pullback.fst g g) (h₂₂ := g) (v₁₃ := g) ?_
    (by simp) (IsPullback.of_hasPullback g g)
  rw [pullback.lift_fst, hc]
  exact IsPullback.of_horiz_isIso ⟨by simp⟩

variable (m) in
/-- Over the domain of `m`, the map `y ↦ (y, c)` followed by `m` is the base change of the
universal right translation along `y ↦ (y, c)`. -/
theorem isPullback_sectionPairRight_restrict (c : S ⟶ Y) (hc : c ≫ g = 𝟙 S) :
    IsPullback (sectionPairRight c hc ∣_ m.domain)
      ((sectionPairRight c hc ∣_ m.domain) ≫ m.mul) (rightT m) (sectionPairRight c hc) := by
  let σ := sectionPairRight c hc
  have hA : IsPullback σ g (pullback.snd g g) c := isPullback_sectionPairRight c hc
  have hσ1 : σ ≫ pullback.snd g g = g ≫ c := pullback.lift_snd _ _ _
  have hσ2 : σ ≫ pullback.fst g g = 𝟙 Y := pullback.lift_fst _ _ _
  have hres : (σ ∣_ m.domain) ≫ m.domain.ι = (σ ⁻¹ᵁ m.domain).ι ≫ σ := morphismRestrict_ι _ _
  have hmapg : ((σ ∣_ m.domain) ≫ m.mul) ≫ g = (σ ⁻¹ᵁ m.domain).ι ≫ g := by
    rw [Category.assoc, m.mul_comp, reassoc_of% hres, reassoc_of% hσ2]
  have hout := (isPullback_morphismRestrict σ m.domain).paste_vert hA
  refine IsPullback.of_bot ?_ ?_ hA
  · convert hout using 1
    exact m.rightT_snd
  · apply pullback.hom_ext
    · rw [Category.assoc, m.rightT_fst, Category.assoc, hσ2, Category.comp_id]
    · rw [Category.assoc, m.rightT_snd, reassoc_of% hres, hσ1, Category.assoc, Category.assoc,
        hσ1, ← Category.assoc]
      have := congrArg (· ≫ c) hmapg
      simp only [Category.assoc] at this ⊢
      exact this.symm

variable (m) in
/-- Left translation by a section `c`, defined where `(c, y)` lies in the domain of `m`. -/
def Translation.ofSection (hstrict : IsStrictDomain m) (c : S ⟶ Y) (hc : c ≫ g = 𝟙 S) :
    Translation m := by
  let σ := sectionPair c hc
  have hA : IsPullback σ g (pullback.fst g g) c := isPullback_sectionPair c hc
  have hσ1 : σ ≫ pullback.fst g g = g ≫ c := pullback.lift_fst _ _ _
  have hσ2 : σ ≫ pullback.snd g g = 𝟙 Y := pullback.lift_snd _ _ _
  have hres : (σ ∣_ m.domain) ≫ m.domain.ι = (σ ⁻¹ᵁ m.domain).ι ≫ σ := morphismRestrict_ι _ _
  have hmapg : ((σ ∣_ m.domain) ≫ m.mul) ≫ g = (σ ⁻¹ᵁ m.domain).ι ≫ g := by
    rw [Category.assoc, m.mul_comp, reassoc_of% hres, reassoc_of% hσ1, hc, Category.comp_id]
  have hsq : IsPullback (σ ∣_ m.domain) ((σ ∣_ m.domain) ≫ m.mul) (leftT m) σ :=
    isPullback_sectionPair_restrict m c hc
  exact
  { dom := σ ⁻¹ᵁ m.domain
    map := (σ ∣_ m.domain) ≫ m.mul
    map_comp := hmapg
    isOpenImmersion := MorphismProperty.of_isPullback hsq inferInstance
    dom_dense := FibreGenerizationDense.preimage_of_isPullback hA hstrict.domain_fst
    range_dense := by
      have himg := Scheme.image_preimage_eq_of_isPullback hsq Set.univ
      rw [Set.preimage_univ, Set.image_univ, Set.image_univ] at himg
      rw [himg]
      exact FibreGenerizationDense.preimage_of_isPullback hA hstrict.left_fst
    equivariant := by
      intro T a b w h₁ hd₁ hb h₂ hd₂
      have key : ∀ e : T ⟶ (σ ⁻¹ᵁ m.domain).toScheme,
          ∃ (hg : ((e ≫ (σ ⁻¹ᵁ m.domain).ι) ≫ g ≫ c) ≫ g =
              (e ≫ (σ ⁻¹ᵁ m.domain).ι) ≫ g)
            (hd : m.Defined ((e ≫ (σ ⁻¹ᵁ m.domain).ι) ≫ g ≫ c) (e ≫ (σ ⁻¹ᵁ m.domain).ι) hg),
            e ≫ (σ ∣_ m.domain) ≫ m.mul =
              m.mulPt ((e ≫ (σ ⁻¹ᵁ m.domain).ι) ≫ g ≫ c) (e ≫ (σ ⁻¹ᵁ m.domain).ι) hg hd := by
        intro e
        have hg : ((e ≫ (σ ⁻¹ᵁ m.domain).ι) ≫ g ≫ c) ≫ g = (e ≫ (σ ⁻¹ᵁ m.domain).ι) ≫ g := by
          simp only [Category.assoc, hc, Category.comp_id]
        have hpair : pullback.lift ((e ≫ (σ ⁻¹ᵁ m.domain).ι) ≫ g ≫ c)
            (e ≫ (σ ⁻¹ᵁ m.domain).ι) hg = (e ≫ (σ ∣_ m.domain)) ≫ m.domain.ι := by
          apply pullback.hom_ext
          · rw [pullback.lift_fst]
            simp only [Category.assoc, reassoc_of% hres, hσ1]
          · rw [pullback.lift_snd]
            simp only [Category.assoc, reassoc_of% hres, hσ2, Category.comp_id]
        have hd := m.pairIn_domain_of_eq (e ≫ (σ ∣_ m.domain)) hpair
        refine ⟨hg, hd, ?_⟩
        rw [BirationalGroupLaw.mulPt, ← Category.assoc]
        congr 1
        apply m.liftDom_eq
        · simp only [Category.assoc, reassoc_of% hres, hσ1]
        · simp only [Category.assoc, reassoc_of% hres, hσ2, Category.comp_id]
      obtain ⟨hga, hda, ha⟩ := key a
      obtain ⟨hgb, hdb, hb'⟩ := key b
      have hBg : (b ≫ (σ ⁻¹ᵁ m.domain).ι) ≫ g ≫ c = (a ≫ (σ ⁻¹ᵁ m.domain).ι) ≫ g ≫ c := by
        rw [hb, ← Category.assoc, m.mulPt_comp_g, Category.assoc]
      have dr : m.Defined ((a ≫ (σ ⁻¹ᵁ m.domain).ι) ≫ g ≫ c) (m.mulPt _ w h₁ hd₁)
          (by rw [m.mulPt_comp_g]; exact hga) := hdb.of_eq hBg hb
      have dl : m.Defined (m.mulPt ((a ≫ (σ ⁻¹ᵁ m.domain).ι) ≫ g ≫ c) _ hga hda) w
          (by rw [m.mulPt_comp_g, hga]; exact h₁) := hd₂.of_eq ha rfl
      change b ≫ (σ ∣_ m.domain) ≫ m.mul = _
      rw [hb']
      calc _ = m.mulPt ((a ≫ (σ ⁻¹ᵁ m.domain).ι) ≫ g ≫ c) (m.mulPt _ w h₁ hd₁) _ dr :=
            m.mulPt_congr hBg hb
        _ = m.mulPt (m.mulPt ((a ≫ (σ ⁻¹ᵁ m.domain).ι) ≫ g ≫ c) _ hga hda) w _ dl :=
            (m.mulPt_assoc _ _ _ hga h₁ hda hd₁ dl dr).symm
        _ = _ := m.mulPt_congr ha.symm rfl }

end Langlands.AlgebraicGeometry.HenselianBirationalSolution
