import Langlands.Geometry.Analytic.ContinuousAnalyticAction
import Langlands.Geometry.Analytic.LocalizedPullbackDescent
import Langlands.Geometry.Analytic.FullRecognitionPairLocalCondition

/-! # Precomposition of Berkovich's test relations and common strong representatives -/

noncomputable section

universe u v w

namespace Langlands.Analytic.SaturatedAtlasPresentation

open CategoryTheory Topology

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]

section Charts

variable (T : SaturatedAtlasPresentation.{u, v, w} K)

/-- Every point lies in a chart. -/
theorem exists_chart_mem (y : T.presentation.space) :
    ∃ i, y ∈ Set.range (T.presentation.atlas.chart i) := by
  obtain ⟨σ, -, hσ, hy, hn⟩ := T.presentation.atlas.isNet_chartFamily.1 y
  have hne : σ.Nonempty := by
    by_contra h
    rw [Set.not_nonempty_iff_eq_empty] at h
    rw [h, Set.sUnion_empty] at hn
    exact (mem_of_mem_nhds hn : y ∈ (∅ : Set T.presentation.space))
  obtain ⟨V, hV⟩ := hne
  obtain ⟨i, rfl⟩ := hσ hV
  exact ⟨i, hy _ hV⟩

/-- A point of the intersection of two charts lies in a chart contained in both. -/
theorem exists_chart_mem_subset_inter (i j : T.presentation.atlas.Index)
    {z : T.presentation.space} (hi : z ∈ Set.range (T.presentation.atlas.chart i))
    (hj : z ∈ Set.range (T.presentation.atlas.chart j)) :
    ∃ l, z ∈ Set.range (T.presentation.atlas.chart l) ∧
      Set.range (T.presentation.atlas.chart l) ⊆
        Set.range (T.presentation.atlas.chart i) ∩ Set.range (T.presentation.atlas.chart j) := by
  obtain ⟨σ, -, hσ, hz, hn⟩ := T.presentation.atlas.isNet_chartFamily.2 _
    (Set.mem_range_self i) _ (Set.mem_range_self j) ⟨z, hi, hj⟩
  have hne : σ.Nonempty := by
    by_contra h
    rw [Set.not_nonempty_iff_eq_empty] at h
    rw [h, Set.sUnion_empty] at hn
    simpa using mem_of_mem_nhds hn
  obtain ⟨W, hW⟩ := hne
  obtain ⟨V, ⟨l, rfl⟩, hVsub, rfl⟩ := hσ hW
  exact ⟨l, hz _ hW, hVsub⟩

variable {T} {S : SaturatedAtlasPresentation.{u, v, w} K}

/-- A point of a source chart whose image lies in a target chart has a smaller source chart
around it mapped into that target chart. -/
theorem exists_subchart_image_subset (c : S ⟶ T) (k : S.presentation.atlas.Index)
    {y : S.presentation.space} (hy : y ∈ Set.range (S.presentation.atlas.chart k))
    (i : T.presentation.atlas.Index) (hi : c.baseMap y ∈ Set.range (T.presentation.atlas.chart i)) :
    ∃ k', y ∈ Set.range (S.presentation.atlas.chart k') ∧
      Set.range (S.presentation.atlas.chart k') ⊆ Set.range (S.presentation.atlas.chart k) ∧
      c.baseMap '' Set.range (S.presentation.atlas.chart k') ⊆
        Set.range (T.presentation.atlas.chart i) := by
  obtain ⟨j, hkj⟩ := c.target_exists k
  have hyj : c.baseMap y ∈ Set.range (T.presentation.atlas.chart j) := hkj ⟨y, hy, rfl⟩
  obtain ⟨l, hl, hlij⟩ := exists_chart_mem_subset_inter T i j hi hyj
  obtain ⟨k', hk'⟩ := AffinoidAtlasPresentation.StrongHom.exists_chart_inter_preimage c
    S.hasAllLocalDomains k j l hkj (fun _ h => (hlij h).2)
  refine ⟨k', ?_, ?_, ?_⟩
  · rw [hk']
    exact ⟨hy, hl⟩
  · rw [hk']
    exact Set.inter_subset_left
  · rintro _ ⟨x, hx, rfl⟩
    rw [hk'] at hx
    exact (hlij hx.2).1

/-- A point of a chart lying in a smaller chart comes from the spectrum of the smaller chart
through the restriction map. -/
theorem exists_restriction_comap_eq {k k' : S.presentation.atlas.Index}
    (h : Set.range (S.presentation.atlas.chart k') ⊆ Set.range (S.presentation.atlas.chart k))
    (p : BanachSpectrum (S.presentation.atlas.algebra k))
    (hp : S.presentation.atlas.chart k p ∈ Set.range (S.presentation.atlas.chart k')) :
    ∃ p' : BanachSpectrum (S.presentation.atlas.algebra k'),
      BanachSpectrum.comap (S.presentation.atlas.restriction k' k h).toBoundedRingHom p' = p := by
  have : p ∈ Set.range (BanachSpectrum.comap
      (S.presentation.atlas.restriction k' k h).toBoundedRingHom) := by
    rw [S.presentation.atlas.range_restriction k' k h]
    exact hp
  exact this

end Charts

section Precomposition

variable {S T B : SaturatedAtlasPresentation.{u, v, w} K}

/-- The pullback of a composite through an intermediate admissible chart. -/
theorem comp_pullback_eq (c : S ⟶ T) (a : T ⟶ B) (k : S.presentation.atlas.Index)
    (i : T.presentation.atlas.Index) (d : B.presentation.atlas.Index)
    (hc : c.baseMap '' Set.range (S.presentation.atlas.chart k) ⊆
      Set.range (T.presentation.atlas.chart i))
    (ha : a.baseMap '' Set.range (T.presentation.atlas.chart i) ⊆
      Set.range (B.presentation.atlas.chart d))
    (h : (c ≫ a).baseMap '' Set.range (S.presentation.atlas.chart k) ⊆
      Set.range (B.presentation.atlas.chart d)) :
    (c ≫ a).pullback k d h = (c.pullback k i hc).comp (a.pullback i d ha) :=
  AffinoidAtlasPresentation.StrongHom.saturatedComp_pullback c a S.hasAllLocalDomains
    T.hasAllLocalDomains k i d hc ha h

/-- Restricting a pullback to a smaller source chart. -/
theorem restriction_comp_pullback (f : S ⟶ B) {k k' : S.presentation.atlas.Index}
    (hk : Set.range (S.presentation.atlas.chart k') ⊆ Set.range (S.presentation.atlas.chart k))
    (d : B.presentation.atlas.Index)
    (h : f.baseMap '' Set.range (S.presentation.atlas.chart k) ⊆
      Set.range (B.presentation.atlas.chart d))
    (h' : f.baseMap '' Set.range (S.presentation.atlas.chart k') ⊆
      Set.range (B.presentation.atlas.chart d)) :
    (S.presentation.atlas.restriction k' k hk).comp (f.pullback k d h) = f.pullback k' d h' := by
  have := f.restriction_comm k' k d d hk subset_rfl h' h
  rwa [B.presentation.atlas.restriction_id, BoundedAlgHom.comp_id] at this

/-- **Precomposition of the test relation** with an arbitrary strong map. -/
theorem StrongNear.precomp {τ : TestTriple B} {a b : T ⟶ B} (hnear : StrongNear τ a b)
    (c : S ⟶ T) : StrongNear τ (c ≫ a) (c ≫ b) := by
  obtain ⟨hpre, hcov, hbound⟩ := hnear
  refine ⟨congrArg (c.baseMap ⁻¹' ·) hpre, fun y hy => ?_, fun k hk p => ?_⟩
  · obtain ⟨i, hi, hyi⟩ := hcov (c.baseMap y) hy
    obtain ⟨k₀, hk₀⟩ := exists_chart_mem S y
    obtain ⟨k, hyk, -, hki⟩ := exists_subchart_image_subset c k₀ hk₀ i hyi
    refine ⟨k, ⟨?_, ?_⟩, hyk⟩
    · rintro _ ⟨x, hx, rfl⟩
      exact hi.1 ⟨c.baseMap x, hki ⟨x, hx, rfl⟩, rfl⟩
    · rintro _ ⟨x, hx, rfl⟩
      exact hi.2 ⟨c.baseMap x, hki ⟨x, hx, rfl⟩, rfl⟩
  · set y := S.presentation.atlas.chart k p
    have hya : a.baseMap (c.baseMap y) ∈ τ.locus := hk.1 ⟨y, ⟨p, rfl⟩, rfl⟩
    obtain ⟨i, hi, hyi⟩ := hcov (c.baseMap y) hya
    obtain ⟨k', hyk', hk'k, hk'i⟩ := exists_subchart_image_subset c k ⟨p, rfl⟩ i hyi
    obtain ⟨p', rfl⟩ := exists_restriction_comap_eq hk'k p hyk'
    have ha' : (c ≫ a).baseMap '' Set.range (S.presentation.atlas.chart k') ⊆
        Set.range (B.presentation.atlas.chart τ.domain) :=
      (Set.image_mono hk'k).trans hk.1
    have hb' : (c ≫ b).baseMap '' Set.range (S.presentation.atlas.chart k') ⊆
        Set.range (B.presentation.atlas.chart τ.domain) :=
      (Set.image_mono hk'k).trans hk.2
    change p' ((S.presentation.atlas.restriction k' k hk'k)
      ((c ≫ a).pullback k τ.domain hk.1 τ.function -
        (c ≫ b).pullback k τ.domain hk.2 τ.function)) ≤ τ.bound
    rw [map_sub]
    change p' ((S.presentation.atlas.restriction k' k hk'k).comp
      ((c ≫ a).pullback k τ.domain hk.1) τ.function -
        (S.presentation.atlas.restriction k' k hk'k).comp
          ((c ≫ b).pullback k τ.domain hk.2) τ.function) ≤ τ.bound
    rw [restriction_comp_pullback (c ≫ a) hk'k τ.domain hk.1 ha',
      restriction_comp_pullback (c ≫ b) hk'k τ.domain hk.2 hb',
      comp_pullback_eq c a k' i τ.domain hk'i hi.1 ha',
      comp_pullback_eq c b k' i τ.domain hk'i hi.2 hb']
    change p' (c.pullback k' i hk'i (a.pullback i τ.domain hi.1 τ.function) -
      c.pullback k' i hk'i (b.pullback i τ.domain hi.2 τ.function)) ≤ τ.bound
    rw [← map_sub]
    exact hbound i hi (BanachSpectrum.comap (c.pullback k' i hk'i).toBoundedRingHom p')

end Precomposition

section Localized

/-! Lemmas about arrows between images of saturated presentations are stated for
`localizationFunctor.obj A`, where rewriting is syntactic; they apply to arbitrary objects `X`
through the definitional identification of `X` with `localizationFunctor.obj (presentationOf X)`. -/

variable {A B C : SaturatedAtlasPresentation.{u, v, w} K}

/-- A right fraction equation in numerator form. -/
theorem fraction_eq_iff {T : SaturatedAtlasPresentation.{u, v, w} K} (s : T ⟶ A)
    (hs : s.IsQuasiIso) (a : T ⟶ B)
    (φ : localizationFunctor.obj A ⟶ localizationFunctor.obj B) :
    φ = (localizedQuasiIso s hs).inv ≫ localizationFunctor.map a ↔
      localizationFunctor.map s ≫ φ = localizationFunctor.map a := by
  constructor
  · rintro rfl
    exact localizedQuasiIso_hom_inv_id_assoc s hs _
  · intro h
    rw [← h, localizedQuasiIso_inv_hom_id_assoc]

/-- `IsNear` in numerator form: after a quasi-isomorphic refinement of the source, both
morphisms are images of strong maps which are near. -/
theorem isNear_iff_numerators {X Y : LocalizedCategory.{u, v, w} (K := K)}
    (τ : TestTriple (presentationOf X)) (φ ψ : Y ⟶ X) :
    IsNear τ φ ψ ↔ ∃ (T : SaturatedAtlasPresentation.{u, v, w} K) (s : T ⟶ presentationOf Y)
      (_ : s.IsQuasiIso) (a b : T ⟶ presentationOf X),
      localizationFunctor.map s ≫ φ = localizationFunctor.map a ∧
      localizationFunctor.map s ≫ ψ = localizationFunctor.map b ∧ StrongNear τ a b := by
  constructor
  · rintro ⟨T, s, hs, a, b, hφ, hψ, h⟩
    exact ⟨T, s, hs, a, b, (fraction_eq_iff s hs a φ).1 hφ, (fraction_eq_iff s hs b ψ).1 hψ, h⟩
  · rintro ⟨T, s, hs, a, b, ha, hb, h⟩
    exact ⟨T, s, hs, a, b, (fraction_eq_iff s hs a φ).2 ha, (fraction_eq_iff s hs b ψ).2 hb, h⟩

/-- Ore refinement of a source arrow against an inverted quasi-isomorphism. -/
theorem exists_numerator_precomp {T : SaturatedAtlasPresentation.{u, v, w} K} (s : T ⟶ A)
    (hs : s.IsQuasiIso) (f : localizationFunctor.obj C ⟶ localizationFunctor.obj A) :
    ∃ (S : SaturatedAtlasPresentation.{u, v, w} K) (s' : S ⟶ C) (_ : s'.IsQuasiIso)
      (c : S ⟶ T), localizationFunctor.map s' ≫ f ≫ (localizedQuasiIso s hs).inv =
        localizationFunctor.map c := by
  obtain ⟨S, s', hs', c, -, hc, -⟩ :=
    exists_commonStrongNumerators (f ≫ (localizedQuasiIso s hs).inv) (𝟙 _)
  exact ⟨S, s', hs', c, hc⟩

theorem numerator_precomp {T S : SaturatedAtlasPresentation.{u, v, w} K} (s : T ⟶ A)
    (hs : s.IsQuasiIso) (a : T ⟶ B) (φ : localizationFunctor.obj A ⟶ localizationFunctor.obj B)
    (ha : localizationFunctor.map s ≫ φ = localizationFunctor.map a)
    (f : localizationFunctor.obj C ⟶ localizationFunctor.obj A) (s' : S ⟶ C) (c : S ⟶ T)
    (hc : localizationFunctor.map s' ≫ f ≫ (localizedQuasiIso s hs).inv =
      localizationFunctor.map c) :
    localizationFunctor.map s' ≫ f ≫ φ = localizationFunctor.map (c ≫ a) := by
  rw [Functor.map_comp, ← hc, ← ha]
  simp only [Category.assoc, localizedQuasiIso_inv_hom_id_assoc]

/-- **Precomposition of the test relation** in the localized category. -/
theorem IsNear.precomp {X Y W : LocalizedCategory.{u, v, w} (K := K)}
    {τ : TestTriple (presentationOf X)} {φ ψ : Y ⟶ X}
    (h : IsNear τ φ ψ) (f : W ⟶ Y) : IsNear τ (f ≫ φ) (f ≫ ψ) := by
  obtain ⟨T, s, hs, a, b, ha, hb, hab⟩ := (isNear_iff_numerators τ φ ψ).1 h
  obtain ⟨S, s', hs', c, hc⟩ := exists_numerator_precomp (C := presentationOf W) s hs f
  exact (isNear_iff_numerators τ _ _).2 ⟨S, s', hs', c ≫ a, c ≫ b,
    numerator_precomp s hs a φ ha f s' c hc, numerator_precomp s hs b ψ hb f s' c hc,
    hab.precomp c⟩

/-- Two quasi-isomorphisms to the same target have a common quasi-isomorphic refinement. -/
theorem exists_common_quasiIso_refinement {P T₁ T₂ : SaturatedAtlasPresentation.{u, v, w} K}
    (s₁ : T₁ ⟶ P) (hs₁ : s₁.IsQuasiIso) (s₂ : T₂ ⟶ P) (hs₂ : s₂.IsQuasiIso) :
    ∃ (S : SaturatedAtlasPresentation.{u, v, w} K) (u₁ : S ⟶ T₁) (u₂ : S ⟶ T₂),
      u₁ ≫ s₁ = u₂ ≫ s₂ ∧ (u₁ ≫ s₁).IsQuasiIso :=
  ⟨quasiIsoOreSource s₁ s₂ hs₂, quasiIsoOreInclusion s₁ s₂ hs₂, quasiIsoOreLift s₁ s₂ hs₂,
    (quasiIsoOre_square s₁ s₂ hs₂).symm,
    (quasiIsomorphisms (K := K)).comp_mem _ _ (isQuasiIso_quasiIsoOreInclusion s₁ s₂ hs₂) hs₁⟩

/-- Numerators of one localized morphism on comparable refinements agree. -/
theorem numerator_eq_comp {S T : SaturatedAtlasPresentation.{u, v, w} K}
    (ψ : localizationFunctor.obj A ⟶ localizationFunctor.obj B)
    (σ : S ⟶ A) (t : T ⟶ A) (q : S ⟶ T) (hq : σ = q ≫ t) (x : S ⟶ B) (a : T ⟶ B)
    (hx : localizationFunctor.map σ ≫ ψ = localizationFunctor.map x)
    (ha : localizationFunctor.map t ≫ ψ = localizationFunctor.map a) : x = q ≫ a := by
  apply localizationFunctor_map_injective
  change localizationFunctor.map x = localizationFunctor.map (q ≫ a)
  rw [Functor.map_comp, ← ha, ← hx, hq, Functor.map_comp, Category.assoc]

/-- Strong numerators of a localized arrow, with a test relation to those of another. -/
def NearNumerators (τ : TestTriple B)
    (ψ ψ₁ : localizationFunctor.obj A ⟶ localizationFunctor.obj B) : Prop :=
  ∃ (T : SaturatedAtlasPresentation.{u, v, w} K) (s : T ⟶ A) (_ : s.IsQuasiIso) (a b : T ⟶ B),
    localizationFunctor.map s ≫ ψ = localizationFunctor.map a ∧
    localizationFunctor.map s ≫ ψ₁ = localizationFunctor.map b ∧ StrongNear τ a b

/-- Merging, in the form for images of saturated presentations. -/
theorem exists_strongNear_numerators_aux (E : Finset (TestTriple B))
    (ψ ψ₁ ψ₂ : localizationFunctor.obj A ⟶ localizationFunctor.obj B)
    (h₁ : ∀ τ ∈ E, NearNumerators τ ψ ψ₁) (h₂ : ∀ τ ∈ E, NearNumerators τ ψ ψ₂) :
    ∃ (S : SaturatedAtlasPresentation.{u, v, w} K) (s : S ⟶ A)
      (_ : s.IsQuasiIso) (x₀ x₁ x₂ : S ⟶ B),
      localizationFunctor.map s ≫ ψ = localizationFunctor.map x₀ ∧
      localizationFunctor.map s ≫ ψ₁ = localizationFunctor.map x₁ ∧
      localizationFunctor.map s ≫ ψ₂ = localizationFunctor.map x₂ ∧
      ∀ τ ∈ E, StrongNear τ x₀ x₁ ∧ StrongNear τ x₀ x₂ := by
  classical
  induction E using Finset.induction_on with
  | empty =>
    obtain ⟨S, s, hs, x₀, x₁, h0, h1⟩ := exists_commonStrongNumerators ψ ψ₁
    obtain ⟨S', s', hs', x₂, -, h2, -⟩ :=
      exists_commonStrongNumerators (localizationFunctor.map s ≫ ψ₂) (𝟙 _)
    refine ⟨S', s' ≫ s, (quasiIsomorphisms (K := K)).comp_mem _ _ hs' hs, s' ≫ x₀, s' ≫ x₁,
      x₂, ?_, ?_, ?_, by simp⟩
    · rw [Functor.map_comp, Category.assoc, h0, Functor.map_comp]
    · rw [Functor.map_comp, Category.assoc, h1, Functor.map_comp]
    · rw [Functor.map_comp, Category.assoc, h2]
  | insert τ E hτ ih =>
    obtain ⟨S, s, hs, x₀, x₁, x₂, h0, h1, h2, hE⟩ :=
      ih (fun σ hσ => h₁ σ (Finset.mem_insert_of_mem hσ))
        (fun σ hσ => h₂ σ (Finset.mem_insert_of_mem hσ))
    obtain ⟨T₁, t₁, ht₁, a₁, b₁, ha₁, hb₁, hn₁⟩ := h₁ τ (Finset.mem_insert_self τ E)
    obtain ⟨T₂, t₂, ht₂, a₂, b₂, ha₂, hb₂, hn₂⟩ := h₂ τ (Finset.mem_insert_self τ E)
    obtain ⟨S₁, u, v, huv, hq₁⟩ := exists_common_quasiIso_refinement s hs t₁ ht₁
    obtain ⟨S₂, u', w', huw, hq₂⟩ := exists_common_quasiIso_refinement (u ≫ s) hq₁ t₂ ht₂
    have hcomp : ∀ (φ : localizationFunctor.obj A ⟶ localizationFunctor.obj B) (x : S ⟶ B),
        localizationFunctor.map s ≫ φ = localizationFunctor.map x →
          localizationFunctor.map (u' ≫ u ≫ s) ≫ φ = localizationFunctor.map (u' ≫ u ≫ x) := by
      intro φ x hx
      simp only [Functor.map_comp, Category.assoc, hx]
    have hcomp' : ∀ (φ : localizationFunctor.obj A ⟶ localizationFunctor.obj B) (x : S ⟶ B),
        localizationFunctor.map s ≫ φ = localizationFunctor.map x →
          localizationFunctor.map (u ≫ s) ≫ φ = localizationFunctor.map (u ≫ x) := by
      intro φ x hx
      simp only [Functor.map_comp, Category.assoc, hx]
    have hq₂' : (u' ≫ u ≫ s).IsQuasiIso := by
      have : u' ≫ u ≫ s = u' ≫ (u ≫ s) := rfl
      exact this ▸ hq₂
    refine ⟨S₂, u' ≫ u ≫ s, hq₂', u' ≫ u ≫ x₀, u' ≫ u ≫ x₁, u' ≫ u ≫ x₂,
      hcomp ψ x₀ h0, hcomp ψ₁ x₁ h1, hcomp ψ₂ x₂ h2, ?_⟩
    intro σ hσmem
    rcases Finset.mem_insert.mp hσmem with rfl | hσE
    · have hx₀ : u ≫ x₀ = v ≫ a₁ :=
        numerator_eq_comp ψ (u ≫ s) t₁ v huv _ a₁ (hcomp' ψ x₀ h0) ha₁
      have hx₁ : u ≫ x₁ = v ≫ b₁ :=
        numerator_eq_comp ψ₁ (u ≫ s) t₁ v huv _ b₁ (hcomp' ψ₁ x₁ h1) hb₁
      have hy₀ : u' ≫ u ≫ x₀ = w' ≫ a₂ :=
        numerator_eq_comp ψ (u' ≫ u ≫ s) t₂ w' huw _ a₂ (hcomp ψ x₀ h0) ha₂
      have hy₂ : u' ≫ u ≫ x₂ = w' ≫ b₂ :=
        numerator_eq_comp ψ₂ (u' ≫ u ≫ s) t₂ w' huw _ b₂ (hcomp ψ₂ x₂ h2) hb₂
      refine ⟨?_, ?_⟩
      · rw [hx₀, hx₁]
        exact (hn₁.precomp v).precomp u'
      · rw [hy₀, hy₂]
        exact hn₂.precomp w'
    · exact ⟨((hE σ hσE).1.precomp u).precomp u', ((hE σ hσE).2.precomp u).precomp u'⟩

/-- **Merging test witnesses.** Finitely many test relations between `ψ` and `ψ₁` and between
`ψ` and `ψ₂` are realized simultaneously by strong numerators on one common quasi-isomorphic
refinement of the source. -/
theorem exists_strongNear_numerators {X Y : LocalizedCategory.{u, v, w} (K := K)}
    (E : Finset (TestTriple (presentationOf X)))
    (ψ ψ₁ ψ₂ : Y ⟶ X) (h₁ : ∀ τ ∈ E, IsNear τ ψ ψ₁) (h₂ : ∀ τ ∈ E, IsNear τ ψ ψ₂) :
    ∃ (S : SaturatedAtlasPresentation.{u, v, w} K) (s : S ⟶ presentationOf Y)
      (_ : s.IsQuasiIso) (x₀ x₁ x₂ : S ⟶ presentationOf X),
      localizationFunctor.map s ≫ ψ = localizationFunctor.map x₀ ∧
      localizationFunctor.map s ≫ ψ₁ = localizationFunctor.map x₁ ∧
      localizationFunctor.map s ≫ ψ₂ = localizationFunctor.map x₂ ∧
      ∀ τ ∈ E, StrongNear τ x₀ x₁ ∧ StrongNear τ x₀ x₂ :=
  exists_strongNear_numerators_aux (A := presentationOf Y) (B := presentationOf X) E ψ ψ₁ ψ₂
    (fun τ hτ => (isNear_iff_numerators τ ψ ψ₁).1 (h₁ τ hτ))
    (fun τ hτ => (isNear_iff_numerators τ ψ ψ₂).1 (h₂ τ hτ))

end Localized

end Langlands.Analytic.SaturatedAtlasPresentation
