import Langlands.Geometry.Analytic.KeyLemma.LiftChartCover
import Langlands.Geometry.Analytic.QuasiEtaleRigidity.StrongNearPostcomposition

/-! # Berkovich's Proposition 6.1 for strong maps into a chart -/

noncomputable section

universe u v w

namespace Langlands.Analytic.SaturatedAtlasPresentation

open CategoryTheory Topology PresentedAffinoidAlgebra BanachSpectrum

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]

section Cover

variable {T : SaturatedAtlasPresentation.{u, v, w} K}

/-- In a Hausdorff space, the intersection of two charts is covered by finitely many charts
contained in both. -/
theorem exists_finset_charts_cover_inter [T2Space T.presentation.space]
    (d c : T.presentation.atlas.Index) :
    ∃ J : Finset T.presentation.atlas.Index,
      (∀ R ∈ J, Set.range (T.presentation.atlas.chart R) ⊆
          Set.range (T.presentation.atlas.chart d) ∧
        Set.range (T.presentation.atlas.chart R) ⊆ Set.range (T.presentation.atlas.chart c)) ∧
      Set.range (T.presentation.atlas.chart d) ∩ Set.range (T.presentation.atlas.chart c) ⊆
        ⋃ R ∈ J, Set.range (T.presentation.atlas.chart R) := by
  classical
  let ι := T.domainInclusion (T.chartDomain c)
  have hcpt : CompactSpace (T.domain (T.chartDomain c)).presentation.space :=
    isCompact_iff_compactSpace.mp (T.isCompactDomain_chartDomain c).1
  have hclosed : IsClosed (Set.range (T.presentation.atlas.chart d)) :=
    (T.isCompactDomain_chartDomain d).1.isClosed
  have hK : IsCompact (ι.baseMap ⁻¹' Set.range (T.presentation.atlas.chart d)) :=
    (hclosed.preimage ι.baseMap.continuous).isCompact
  obtain ⟨I, hI, hcov⟩ := exists_finite_charts_cover_preimage ι d hK
  refine ⟨I.image Subtype.val, ?_, ?_⟩
  · intro R hR
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hR
    refine ⟨?_, k.property⟩
    rintro _ ⟨q, rfl⟩
    exact hI k hk ⟨_, ⟨q, rfl⟩, rfl⟩
  · rintro z ⟨hzd, hzc⟩
    have hz : (⟨z, hzc⟩ : (T.chartDomain c).carrier) ∈
        ι.baseMap ⁻¹' Set.range (T.presentation.atlas.chart d) := hzd
    obtain ⟨k, hk, q, hq⟩ := Set.mem_iUnion₂.mp (hcov hz)
    exact Set.mem_iUnion₂.mpr ⟨k.val, Finset.mem_image_of_mem _ hk, q, congrArg Subtype.val hq⟩

end Cover

section Transfer

variable {T : SaturatedAtlasPresentation.{u, v, w} K}

/-- **Transfer through a subchart.** Let `R` be a chart contained in the charts `c` and `U`, and
let `f` be a function on `U`. Finitely many functions on `c` and a bound control strong maps
chartwise: if `a` sends a source chart `k` into `R`, `b` sends it into `c`, and the pullbacks of
these functions along `a` and `b` are uniformly close, then `b` also sends `k` into `R`, and the
pullbacks of the restriction of `f` to `R` differ by at most `t`. -/
theorem exists_subchart_transfer (c R U : T.presentation.atlas.Index)
    (hRc : Set.range (T.presentation.atlas.chart R) ⊆ Set.range (T.presentation.atlas.chart c))
    (hRU : Set.range (T.presentation.atlas.chart R) ⊆ Set.range (T.presentation.atlas.chart U))
    (f : T.presentation.atlas.algebra U) {t : ℝ} (ht : 0 < t) :
    ∃ (E : Finset (T.presentation.atlas.algebra c)) (δ : ℝ), 0 < δ ∧
      ∀ (S : SaturatedAtlasPresentation.{u, v, w} K) (a b : S ⟶ T)
        (k : S.presentation.atlas.Index)
        (hak : a.baseMap '' Set.range (S.presentation.atlas.chart k) ⊆
          Set.range (T.presentation.atlas.chart R))
        (hac : a.baseMap '' Set.range (S.presentation.atlas.chart k) ⊆
          Set.range (T.presentation.atlas.chart c))
        (hbc : b.baseMap '' Set.range (S.presentation.atlas.chart k) ⊆
          Set.range (T.presentation.atlas.chart c)),
        (∀ s ∈ E, SpectralBound (b.pullback k c hbc s - a.pullback k c hac s) δ) →
        ∃ hbk : b.baseMap '' Set.range (S.presentation.atlas.chart k) ⊆
            Set.range (T.presentation.atlas.chart R),
          SpectralBound (b.pullback k R hbk (T.presentation.atlas.restriction R U hRU f) -
            a.pullback k R hak (T.presentation.atlas.restriction R U hRU f)) t := by
  classical
  let dom := T.presentation.atlas.restrictionDomain R c hRc
  let ρ := T.presentation.atlas.restriction R c hRc
  obtain ⟨E, δ, hδ, hE⟩ :=
    dom.hasSpectralTestTransfer {T.presentation.atlas.restriction R U hRU f} t ht
  refine ⟨E, δ, hδ, fun S a b k hak hac hbc hclose => ?_⟩
  have hres : (a.pullback k R hak).comp ρ = a.pullback k c hac := by
    have h := a.restriction_comm k k R c subset_rfl hRc hak hac
    rw [S.presentation.atlas.restriction_id, BoundedAlgHom.id_comp] at h
    exact h.symm
  obtain ⟨b', hb', hnear⟩ := hE (S.presentation.atlas.algebra k) (a.pullback k R hak)
    (b.pullback k c hbc) fun s hs => by
      change SpectralBound ((b.pullback k c hbc) s - (a.pullback k R hak) (ρ s)) δ
      rw [show (a.pullback k R hak) (ρ s) = a.pullback k c hac s from
        congrArg (fun m : BoundedAlgHom K _ _ => m s) hres]
      exact hclose s hs
  have hbk : b.baseMap '' Set.range (S.presentation.atlas.chart k) ⊆
      Set.range (T.presentation.atlas.chart R) := by
    rintro _ ⟨_, ⟨q, rfl⟩, rfl⟩
    refine ⟨comap b'.toBoundedRingHom q, ?_⟩
    rw [← b.chart_comm k c hbc q, ← hb']
    exact (T.presentation.atlas.restriction_chart R c hRc _).symm
  refine ⟨hbk, ?_⟩
  have hb'eq : b.pullback k R hbk = b' := by
    apply Represents.hom_ext dom.represents
    change (b.pullback k R hbk).comp ρ = b'.comp ρ
    have h := b.restriction_comm k k R c subset_rfl hRc hbk hbc
    rw [S.presentation.atlas.restriction_id, BoundedAlgHom.id_comp] at h
    rw [← h]
    exact hb'.symm
  rw [hb'eq]
  exact hnear _ (Finset.mem_singleton_self _)

/-- **Berkovich's Proposition 6.1 for strong maps into a chart** (Berkovich 1994, Proposition
6.1). Let the space of `T` be Hausdorff, let `c` be a chart and `τ` a test triple. There are
finitely many functions on `c` and a bound such that two strong maps sending every source chart
into `c`, whose pullbacks of these functions are uniformly close on every source chart, satisfy
the test relation for `τ`. -/
theorem exists_chart_tests_strongNear [T2Space T.presentation.space]
    (c : T.presentation.atlas.Index) (τ : TestTriple T) :
    ∃ (F : Finset (T.presentation.atlas.algebra c)) (ε : ℝ), 0 < ε ∧
      ∀ (S : SaturatedAtlasPresentation.{u, v, w} K) (a b : S ⟶ T)
        (ha : ∀ k, a.baseMap '' Set.range (S.presentation.atlas.chart k) ⊆
          Set.range (T.presentation.atlas.chart c))
        (hb : ∀ k, b.baseMap '' Set.range (S.presentation.atlas.chart k) ⊆
          Set.range (T.presentation.atlas.chart c)),
        (∀ k, ∀ h ∈ F, SpectralBound (a.pullback k c (ha k) h - b.pullback k c (hb k) h) ε) →
        StrongNear τ a b := by
  classical
  obtain ⟨J, hJ, hJcov⟩ := exists_finset_charts_cover_inter (T := T) τ.domain c
  have key : ∀ R ∈ J, ∃ (E : Finset (T.presentation.atlas.algebra c)) (δ : ℝ), 0 < δ ∧
      ∀ (S : SaturatedAtlasPresentation.{u, v, w} K) (a b : S ⟶ T)
        (k : S.presentation.atlas.Index)
        (hak : a.baseMap '' Set.range (S.presentation.atlas.chart k) ⊆
          Set.range (T.presentation.atlas.chart R))
        (hac : a.baseMap '' Set.range (S.presentation.atlas.chart k) ⊆
          Set.range (T.presentation.atlas.chart c))
        (hbc : b.baseMap '' Set.range (S.presentation.atlas.chart k) ⊆
          Set.range (T.presentation.atlas.chart c)),
        (∀ s ∈ E, SpectralBound (b.pullback k c hbc s - a.pullback k c hac s) δ) →
        ∃ hbk : b.baseMap '' Set.range (S.presentation.atlas.chart k) ⊆
            Set.range (T.presentation.atlas.chart R),
          ∀ hRU : Set.range (T.presentation.atlas.chart R) ⊆
              Set.range (T.presentation.atlas.chart τ.domain),
          SpectralBound (b.pullback k R hbk
              (T.presentation.atlas.restriction R τ.domain hRU τ.function) -
            a.pullback k R hak (T.presentation.atlas.restriction R τ.domain hRU τ.function))
            τ.bound := by
    intro R hR
    obtain ⟨E, δ, hδ, hE⟩ :=
      exists_subchart_transfer c R τ.domain (hJ R hR).2 (hJ R hR).1 τ.function τ.bound_pos
    refine ⟨E, δ, hδ, fun S a b k hak hac hbc hclose => ?_⟩
    obtain ⟨hbk, hbound⟩ := hE S a b k hak hac hbc hclose
    exact ⟨hbk, fun _ => hbound⟩
  choose! E δ hδ hE using key
  let values : Finset ℝ := insert 1 (J.image δ)
  have hvalues : values.Nonempty := ⟨1, Finset.mem_insert_self _ _⟩
  let ε := values.inf' hvalues id
  have hε : 0 < ε := by
    apply (Finset.lt_inf'_iff _).mpr
    intro x hx
    rcases Finset.mem_insert.mp hx with rfl | hx
    · exact zero_lt_one
    · obtain ⟨R, hR, rfl⟩ := Finset.mem_image.mp hx
      exact hδ R hR
  have hεδ : ∀ R ∈ J, ε ≤ δ R := fun R hR =>
    Finset.inf'_le id (Finset.mem_insert_of_mem (Finset.mem_image_of_mem δ hR))
  refine ⟨J.biUnion E, ε, hε, ?_⟩
  -- The core estimate, for an ordered pair of maps.
  have core : ∀ (S : SaturatedAtlasPresentation.{u, v, w} K) (a b : S ⟶ T)
      (ha : ∀ k, a.baseMap '' Set.range (S.presentation.atlas.chart k) ⊆
        Set.range (T.presentation.atlas.chart c))
      (hb : ∀ k, b.baseMap '' Set.range (S.presentation.atlas.chart k) ⊆
        Set.range (T.presentation.atlas.chart c)),
      (∀ k, ∀ h ∈ J.biUnion E,
        SpectralBound (b.pullback k c (hb k) h - a.pullback k c (ha k) h) ε) →
      ∀ R ∈ J, ∀ (k : S.presentation.atlas.Index)
        (hak : a.baseMap '' Set.range (S.presentation.atlas.chart k) ⊆
          Set.range (T.presentation.atlas.chart R)),
        ∃ hbk : b.baseMap '' Set.range (S.presentation.atlas.chart k) ⊆
            Set.range (T.presentation.atlas.chart R),
          ∀ hRU : Set.range (T.presentation.atlas.chart R) ⊆
              Set.range (T.presentation.atlas.chart τ.domain),
          SpectralBound (b.pullback k R hbk
              (T.presentation.atlas.restriction R τ.domain hRU τ.function) -
            a.pullback k R hak (T.presentation.atlas.restriction R τ.domain hRU τ.function))
            τ.bound := by
    intro S a b ha hb hclose R hR k hak
    exact hE R hR S a b k hak (ha k) (hb k) fun s hs =>
      (hclose k s (Finset.mem_biUnion.mpr ⟨R, hR, hs⟩)).mono (hεδ R hR)
  intro S a b ha hb hclose
  have hclose' : ∀ k, ∀ h ∈ J.biUnion E,
      SpectralBound (b.pullback k c (hb k) h - a.pullback k c (ha k) h) ε := by
    intro k h hh
    have := (hclose k h hh).neg
    rwa [neg_sub] at this
  have coreab := core S a b ha hb hclose'
  have coreba := core S b a hb ha hclose
  -- Points sent into the domain of `τ` lie in a chart sent into some `R ∈ J`.
  have hpiece : ∀ (a' : S ⟶ T)
      (ha' : ∀ k, a'.baseMap '' Set.range (S.presentation.atlas.chart k) ⊆
        Set.range (T.presentation.atlas.chart c))
      (i : S.presentation.atlas.Index) {z : S.presentation.space}
      (hzi : z ∈ Set.range (S.presentation.atlas.chart i)), a'.baseMap z ∈ τ.locus →
      ∃ R ∈ J, ∃ k, z ∈ Set.range (S.presentation.atlas.chart k) ∧
        Set.range (S.presentation.atlas.chart k) ⊆ Set.range (S.presentation.atlas.chart i) ∧
        a'.baseMap '' Set.range (S.presentation.atlas.chart k) ⊆
          Set.range (T.presentation.atlas.chart R) := by
    intro a' ha' i z hzi hz
    have hzc : a'.baseMap z ∈ Set.range (T.presentation.atlas.chart c) :=
      ha' i ⟨z, hzi, rfl⟩
    obtain ⟨R, hR, hzR⟩ := Set.mem_iUnion₂.mp (hJcov ⟨hz, hzc⟩)
    obtain ⟨k, hzk, hki, hkR⟩ := exists_subchart_image_subset a' i hzi R hzR
    exact ⟨R, hR, k, hzk, hki, hkR⟩
  have hpre : ∀ (a' b' : S ⟶ T)
      (ha' : ∀ k, a'.baseMap '' Set.range (S.presentation.atlas.chart k) ⊆
        Set.range (T.presentation.atlas.chart c))
      (_ : ∀ R ∈ J, ∀ (k : S.presentation.atlas.Index)
        (_ : a'.baseMap '' Set.range (S.presentation.atlas.chart k) ⊆
          Set.range (T.presentation.atlas.chart R)),
        b'.baseMap '' Set.range (S.presentation.atlas.chart k) ⊆
          Set.range (T.presentation.atlas.chart R)),
      a'.baseMap ⁻¹' τ.locus ⊆ b'.baseMap ⁻¹' τ.locus := by
    intro a' b' ha' hab z hz
    obtain ⟨i, hzi⟩ := exists_chart_mem S z
    obtain ⟨R, hR, k, hzk, -, hkR⟩ := hpiece a' ha' i hzi hz
    exact (hJ R hR).1 (hab R hR k hkR ⟨z, hzk, rfl⟩)
  refine ⟨Set.Subset.antisymm
      (hpre a b ha fun R hR k hk => (coreab R hR k hk).1)
      (hpre b a hb fun R hR k hk => (coreba R hR k hk).1),
    fun z hz => ?_, fun i hi p => ?_⟩
  · obtain ⟨i, hzi⟩ := exists_chart_mem S z
    obtain ⟨R, hR, k, hzk, -, hkR⟩ := hpiece a ha i hzi hz
    obtain ⟨hbk, -⟩ := coreab R hR k hkR
    exact ⟨k, ⟨hkR.trans (hJ R hR).1, hbk.trans (hJ R hR).1⟩, hzk⟩
  · set z := S.presentation.atlas.chart i p
    have hzi : z ∈ Set.range (S.presentation.atlas.chart i) := ⟨p, rfl⟩
    obtain ⟨R, hR, k, hzk, hki, hkR⟩ := hpiece a ha i hzi (hi.1 ⟨z, hzi, rfl⟩)
    obtain ⟨hbk, hbound⟩ := coreab R hR k hkR
    obtain ⟨p', hp'⟩ := exists_restriction_comap_eq hki p hzk
    have hRU := (hJ R hR).1
    have hakU : a.baseMap '' Set.range (S.presentation.atlas.chart k) ⊆ τ.locus :=
      hkR.trans hRU
    have hbkU : b.baseMap '' Set.range (S.presentation.atlas.chart k) ⊆ τ.locus :=
      hbk.trans hRU
    have hrestr : ∀ (a' : S ⟶ T)
        (h₁ : a'.baseMap '' Set.range (S.presentation.atlas.chart i) ⊆ τ.locus)
        (h₂ : a'.baseMap '' Set.range (S.presentation.atlas.chart k) ⊆
          Set.range (T.presentation.atlas.chart R))
        (h₃ : a'.baseMap '' Set.range (S.presentation.atlas.chart k) ⊆ τ.locus),
        S.presentation.atlas.restriction k i hki (a'.pullback i τ.domain h₁ τ.function) =
          a'.pullback k R h₂ (T.presentation.atlas.restriction R τ.domain hRU τ.function) := by
      intro a' h₁ h₂ h₃
      have e₁ : S.presentation.atlas.restriction k i hki (a'.pullback i τ.domain h₁ τ.function) =
          a'.pullback k τ.domain h₃ τ.function :=
        congrArg (fun m : BoundedAlgHom K _ _ => m τ.function)
          (restriction_comp_pullback a' hki τ.domain h₁ h₃)
      have e₂ := a'.restriction_comm k k R τ.domain subset_rfl hRU h₂ h₃
      rw [S.presentation.atlas.restriction_id, BoundedAlgHom.id_comp] at e₂
      rw [e₁, e₂]
      rfl
    rw [← hp']
    change p' (S.presentation.atlas.restriction k i hki
      (a.pullback i τ.domain hi.1 τ.function - b.pullback i τ.domain hi.2 τ.function)) ≤ τ.bound
    rw [map_sub, hrestr a hi.1 hkR hakU, hrestr b hi.2 hbk hbkU, ← map_neg_eq_map, neg_sub]
    exact hbound hRU p'

/-- The tests of `exists_chart_tests_strongNear` for finitely many test triples at once. -/
theorem exists_chart_tests_strongNear_finset [T2Space T.presentation.space]
    (c : T.presentation.atlas.Index) (E : Finset (TestTriple T)) :
    ∃ (F : Finset (T.presentation.atlas.algebra c)) (ε : ℝ), 0 < ε ∧
      ∀ (S : SaturatedAtlasPresentation.{u, v, w} K) (a b : S ⟶ T)
        (ha : ∀ k, a.baseMap '' Set.range (S.presentation.atlas.chart k) ⊆
          Set.range (T.presentation.atlas.chart c))
        (hb : ∀ k, b.baseMap '' Set.range (S.presentation.atlas.chart k) ⊆
          Set.range (T.presentation.atlas.chart c)),
        (∀ k, ∀ h ∈ F, SpectralBound (a.pullback k c (ha k) h - b.pullback k c (hb k) h) ε) →
        ∀ τ ∈ E, StrongNear τ a b := by
  classical
  induction E using Finset.induction_on with
  | empty =>
    exact ⟨∅, 1, one_pos, fun _ _ _ _ _ _ τ hτ => absurd hτ (Finset.notMem_empty τ)⟩
  | insert τ E _ ih =>
    obtain ⟨F₁, ε₁, hε₁, H₁⟩ := ih
    obtain ⟨F₂, ε₂, hε₂, H₂⟩ := exists_chart_tests_strongNear c τ
    refine ⟨F₁ ∪ F₂, min ε₁ ε₂, lt_min hε₁ hε₂, fun S a b ha hb hclose σ hσ => ?_⟩
    rcases Finset.mem_insert.mp hσ with rfl | hσ
    · exact H₂ S a b ha hb fun k h hh =>
        (hclose k h (Finset.mem_union_right _ hh)).mono (min_le_right _ _)
    · exact H₁ S a b ha hb (fun k h hh =>
        (hclose k h (Finset.mem_union_left _ hh)).mono (min_le_left _ _)) σ hσ

/-- **Proposition 6.1 for sources with a global chart.** For a source whose chart `P` is the
whole space, closeness of the pullbacks at `P` alone gives the test relations. -/
theorem exists_globalChart_tests_strongNear [T2Space T.presentation.space]
    (c : T.presentation.atlas.Index) (E : Finset (TestTriple T)) :
    ∃ (F : Finset (T.presentation.atlas.algebra c)) (ε : ℝ), 0 < ε ∧
      ∀ (S : SaturatedAtlasPresentation.{u, v, w} K) (P : S.presentation.atlas.Index),
        Set.range (S.presentation.atlas.chart P) = Set.univ → ∀ (a b : S ⟶ T)
        (ha : a.baseMap '' Set.range (S.presentation.atlas.chart P) ⊆
          Set.range (T.presentation.atlas.chart c))
        (hb : b.baseMap '' Set.range (S.presentation.atlas.chart P) ⊆
          Set.range (T.presentation.atlas.chart c)),
        (∀ h ∈ F, SpectralBound (a.pullback P c ha h - b.pullback P c hb h) ε) →
        ∀ τ ∈ E, StrongNear τ a b := by
  obtain ⟨F, ε, hε, H⟩ := exists_chart_tests_strongNear_finset c E
  refine ⟨F, ε, hε, fun S P hP a b ha hb hclose => ?_⟩
  have hk : ∀ k, Set.range (S.presentation.atlas.chart k) ⊆
      Set.range (S.presentation.atlas.chart P) := fun k => hP ▸ Set.subset_univ _
  refine H S a b (fun k => (Set.image_mono (hk k)).trans ha)
    (fun k => (Set.image_mono (hk k)).trans hb) fun k h hh => ?_
  have e₁ := restriction_comp_pullback a (hk k) c ha ((Set.image_mono (hk k)).trans ha)
  have e₂ := restriction_comp_pullback b (hk k) c hb ((Set.image_mono (hk k)).trans hb)
  rw [← e₁, ← e₂]
  change SpectralBound (S.presentation.atlas.restriction k P (hk k) (a.pullback P c ha h) -
    S.presentation.atlas.restriction k P (hk k) (b.pullback P c hb h)) ε
  rw [← map_sub]
  exact (hclose h hh).map (S.presentation.atlas.restriction k P (hk k)).toBoundedRingHom

end Transfer

end Langlands.Analytic.SaturatedAtlasPresentation
