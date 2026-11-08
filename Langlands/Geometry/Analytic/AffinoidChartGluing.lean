import Langlands.Geometry.Analytic.GeneralizedAffinoid.DomainLocalization

/-! # Gluing affinoid spectra along affinoid domain inclusions -/

noncomputable section

universe u w

namespace Langlands.Analytic

open Set Topology PresentedAffinoidAlgebra

/-- A space covered by finitely many closed Hausdorff subspaces is Hausdorff. -/
theorem t2Space_of_finite_isClosed_cover {X : Type*} [TopologicalSpace X] {ι : Type*}
    [Finite ι] (C : ι → Set X) (hC : ∀ i, IsClosed (C i)) (hT : ∀ i, T2Space (C i))
    (hcov : ∀ x, ∃ i, x ∈ C i) : T2Space X := by
  classical
  refine ⟨fun a b hab => ?_⟩
  have key : ∀ i, a ∈ C i → b ∈ C i → ∃ O O' : Set X, IsOpen O ∧ IsOpen O' ∧ a ∈ O ∧
      b ∈ O' ∧ ∀ p ∈ C i, p ∈ O → p ∉ O' := by
    intro i ha hb
    obtain ⟨U, V, hU, hV, haU, hbV, hUV⟩ :=
      t2_separation (x := (⟨a, ha⟩ : C i)) (y := ⟨b, hb⟩) fun h => hab (congrArg Subtype.val h)
    obtain ⟨O, hO, rfl⟩ := isOpen_induced_iff.1 hU
    obtain ⟨O', hO', rfl⟩ := isOpen_induced_iff.1 hV
    refine ⟨O, O', hO, hO', haU, hbV, fun p hp hpO hpO' => ?_⟩
    exact Set.disjoint_left.1 hUV (show (⟨p, hp⟩ : C i) ∈ Subtype.val ⁻¹' O from hpO) hpO'
  choose! O O' hO hO' haO hbO' hOO' using key
  let U : Set X := ⋂ i, if a ∈ C i then (if b ∈ C i then O i ∪ (C i)ᶜ else Set.univ)
    else (C i)ᶜ
  let V : Set X := ⋂ i, if b ∈ C i then (if a ∈ C i then O' i ∪ (C i)ᶜ else Set.univ)
    else (C i)ᶜ
  refine ⟨U, V, isOpen_iInter_of_finite fun i => ?_, isOpen_iInter_of_finite fun i => ?_,
    Set.mem_iInter.2 fun i => ?_, Set.mem_iInter.2 fun i => ?_, Set.disjoint_left.2 ?_⟩
  · split_ifs with ha hb
    · exact (hO i ha hb).union (hC i).isOpen_compl
    · exact isOpen_univ
    · exact (hC i).isOpen_compl
  · split_ifs with hb ha
    · exact (hO' i ha hb).union (hC i).isOpen_compl
    · exact isOpen_univ
    · exact (hC i).isOpen_compl
  · split_ifs with ha hb
    · exact Or.inl (haO i ha hb)
    · trivial
    · exact ha
  · split_ifs with hb ha
    · exact Or.inl (hbO' i ha hb)
    · trivial
    · exact hb
  · intro p hpU hpV
    obtain ⟨i, hpi⟩ := hcov p
    have hU := Set.mem_iInter.1 hpU i
    have hV := Set.mem_iInter.1 hpV i
    by_cases ha : a ∈ C i
    · by_cases hb : b ∈ C i
      · simp only [ha, hb, ite_true] at hU hV
        have h1 : p ∈ O i := hU.resolve_right (not_not.2 hpi)
        have h2 : p ∈ O' i := hV.resolve_right (not_not.2 hpi)
        exact hOO' i ha hb p hpi h1 h2
      · simp only [hb, ite_false] at hV
        exact hV hpi
    · simp only [ha, ite_false] at hU
      exact hU hpi

variable (K : Type u) [NormedField K] [IsUltrametricDist K] [CompleteSpace K]

/-- A system of presented affinoid charts with a preorder of affinoid domain
inclusions. Each inclusion carries a bounded restriction map representing its
spectrum image, the restrictions are functorial, and two subdomains of a chart
through a common point have a common subdomain through that point. -/
structure AffinoidChartSystem where
  Index : Type w
  algebra : Index → PresentedAffinoidAlgebra K
  Sub : Index → Index → Prop
  restriction : ∀ i j, Sub i j → BoundedAlgHom K (algebra j) (algebra i)
  sub_refl : ∀ i, Sub i i
  sub_trans : ∀ {i j k}, Sub i j → Sub j k → Sub i k
  restriction_refl : ∀ i, restriction i i (sub_refl i) = BoundedAlgHom.id K (algebra i)
  restriction_trans : ∀ {i j k} (hij : Sub i j) (hjk : Sub j k),
    restriction i k (sub_trans hij hjk) = (restriction i j hij).comp (restriction j k hjk)
  represents : ∀ i j (h : Sub i j), Represents K (restriction i j h)
    (Set.range (BanachSpectrum.comap (restriction i j h).toBoundedRingHom))
  meet : ∀ {i j k} (hik : Sub i k) (hjk : Sub j k) (t : BanachSpectrum (algebra k)),
    t ∈ Set.range (BanachSpectrum.comap (restriction i k hik).toBoundedRingHom) →
      t ∈ Set.range (BanachSpectrum.comap (restriction j k hjk).toBoundedRingHom) →
        ∃ (l : Index) (hli : Sub l i), Sub l j ∧
          t ∈ Set.range (BanachSpectrum.comap
            (restriction l k (sub_trans hli hik)).toBoundedRingHom)

namespace AffinoidChartSystem

variable {K} (C : AffinoidChartSystem.{u, w} K)

/-- The pullback of points along an inclusion. -/
def pull {i j : C.Index} (h : C.Sub i j) :
    BanachSpectrum (C.algebra i) → BanachSpectrum (C.algebra j) :=
  BanachSpectrum.comap (C.restriction i j h).toBoundedRingHom

/-- The domain of an inclusion. -/
def toDomain {i j : C.Index} (h : C.Sub i j) : Domain K (C.algebra j) where
  algebra := C.algebra i
  baseMap := C.restriction i j h
  locus := Set.range (C.pull h)
  represents := C.represents i j h

theorem pull_injective {i j : C.Index} (h : C.Sub i j) : Function.Injective (C.pull h) :=
  (C.toDomain h).spectrumMap_injective

theorem continuous_pull {i j : C.Index} (h : C.Sub i j) : Continuous (C.pull h) :=
  (BanachSpectrum.comapContinuous (C.restriction i j h).toBoundedRingHom).continuous

theorem pull_refl (i : C.Index) (s : BanachSpectrum (C.algebra i)) : C.pull (C.sub_refl i) s = s := by
  apply BanachSpectrum.ext
  intro a
  change s (C.restriction i i (C.sub_refl i) a) = s a
  rw [C.restriction_refl]
  rfl

theorem pull_trans {i j k : C.Index} (hij : C.Sub i j) (hjk : C.Sub j k)
    (s : BanachSpectrum (C.algebra i)) :
    C.pull (C.sub_trans hij hjk) s = C.pull hjk (C.pull hij s) := by
  apply BanachSpectrum.ext
  intro a
  change s (C.restriction i k (C.sub_trans hij hjk) a) =
    s (C.restriction i j hij (C.restriction j k hjk a))
  rw [C.restriction_trans]
  rfl

/-- Two chart points are glued when they come from one point of a common
subdomain. -/
def Glued (i : C.Index) (s : BanachSpectrum (C.algebra i)) (j : C.Index)
    (t : BanachSpectrum (C.algebra j)) : Prop :=
  ∃ (k : C.Index) (hki : C.Sub k i) (hkj : C.Sub k j) (v : BanachSpectrum (C.algebra k)),
    C.pull hki v = s ∧ C.pull hkj v = t

theorem glued_refl (i : C.Index) (s : BanachSpectrum (C.algebra i)) : C.Glued i s i s :=
  ⟨i, C.sub_refl i, C.sub_refl i, s, C.pull_refl i s, C.pull_refl i s⟩

theorem glued_symm {i j : C.Index} {s : BanachSpectrum (C.algebra i)}
    {t : BanachSpectrum (C.algebra j)} (h : C.Glued i s j t) : C.Glued j t i s := by
  obtain ⟨k, hki, hkj, v, hv, hv'⟩ := h
  exact ⟨k, hkj, hki, v, hv', hv⟩

/-- Two subdomain points with the same image in a common chart come from one
point of a common smaller subdomain. -/
theorem exists_common {k k' j : C.Index} (hkj : C.Sub k j) (hk'j : C.Sub k' j)
    {v : BanachSpectrum (C.algebra k)} {v' : BanachSpectrum (C.algebra k')}
    (h : C.pull hkj v = C.pull hk'j v') :
    ∃ (m : C.Index) (hmk : C.Sub m k) (hmk' : C.Sub m k') (w : BanachSpectrum (C.algebra m)),
      C.pull hmk w = v ∧ C.pull hmk' w = v' := by
  obtain ⟨m, hmk, hmk', w, hw⟩ := C.meet hkj hk'j (C.pull hkj v) ⟨v, rfl⟩ ⟨v', h.symm⟩
  refine ⟨m, hmk, hmk', w, ?_, ?_⟩
  · apply C.pull_injective hkj
    rw [← C.pull_trans]
    exact hw
  · apply C.pull_injective hk'j
    rw [← C.pull_trans, ← h]
    exact hw

theorem glued_trans {i j l : C.Index} {s : BanachSpectrum (C.algebra i)}
    {t : BanachSpectrum (C.algebra j)} {r : BanachSpectrum (C.algebra l)}
    (h₁ : C.Glued i s j t) (h₂ : C.Glued j t l r) : C.Glued i s l r := by
  obtain ⟨k, hki, hkj, v, hvs, hvt⟩ := h₁
  obtain ⟨k', hk'j, hk'l, v', hv't, hv'r⟩ := h₂
  obtain ⟨m, hmk, hmk', w, hw, hw'⟩ := C.exists_common hkj hk'j (hvt.trans hv't.symm)
  refine ⟨m, C.sub_trans hmk hki, C.sub_trans hmk' hk'l, w, ?_, ?_⟩
  · rw [C.pull_trans hmk hki, hw, hvs]
  · rw [C.pull_trans hmk' hk'l, hw', hv'r]

/-- The gluing relation on the disjoint union of the chart spectra. -/
def setoid : Setoid ((i : C.Index) × BanachSpectrum (C.algebra i)) where
  r a b := C.Glued a.1 a.2 b.1 b.2
  iseqv := ⟨fun a => C.glued_refl a.1 a.2, fun h => C.glued_symm h,
    fun h₁ h₂ => C.glued_trans h₁ h₂⟩

/-- The glued space: the quotient of the disjoint union of the chart spectra by
the gluing relation, with the quotient topology. -/
abbrev Space : Type _ := Quotient C.setoid

/-- The chart of an index in the glued space. -/
def chart (i : C.Index) (s : BanachSpectrum (C.algebra i)) : C.Space :=
  Quotient.mk C.setoid ⟨i, s⟩

theorem chart_eq_iff {i j : C.Index} {s : BanachSpectrum (C.algebra i)}
    {t : BanachSpectrum (C.algebra j)} : C.chart i s = C.chart j t ↔ C.Glued i s j t :=
  Quotient.eq (r := C.setoid)

theorem continuous_chart (i : C.Index) : Continuous (C.chart i) :=
  continuous_quotient_mk'.comp continuous_sigmaMk

theorem chart_injective (i : C.Index) : Function.Injective (C.chart i) := by
  intro s s' h
  obtain ⟨k, hki, hki', v, hv, hv'⟩ := C.chart_eq_iff.1 h
  exact hv.symm.trans hv'

theorem chart_pull {i j : C.Index} (h : C.Sub i j) (s : BanachSpectrum (C.algebra i)) :
    C.chart j (C.pull h s) = C.chart i s :=
  C.chart_eq_iff.2 ⟨i, h, C.sub_refl i, s, rfl, C.pull_refl i s⟩

theorem exists_chart (z : C.Space) : ∃ i s, C.chart i s = z := by
  induction z using Quotient.inductionOn with
  | h a => exact ⟨a.1, a.2, rfl⟩

/-- Finite overlaps: the points glued between two charts come from finitely
many common subdomains. -/
def HasFiniteOverlaps : Prop :=
  ∀ i j : C.Index, ∃ S : Set {k : C.Index // C.Sub k i ∧ C.Sub k j}, S.Finite ∧
    ∀ (s : BanachSpectrum (C.algebra i)) (t : BanachSpectrum (C.algebra j)), C.Glued i s j t →
      ∃ p ∈ S, ∃ v : BanachSpectrum (C.algebra p.1), C.pull p.2.1 v = s ∧ C.pull p.2.2 v = t

/-- With finite overlaps, the preimage in one chart of the image of a closed set
of another chart is a finite union of compact sets, hence closed. -/
theorem isClosed_chart_preimage_image (hF : C.HasFiniteOverlaps) (i j : C.Index)
    {F : Set (BanachSpectrum (C.algebra i))} (hFc : IsClosed F) :
    IsClosed (C.chart j ⁻¹' (C.chart i '' F)) := by
  obtain ⟨S, hS, hSg⟩ := hF i j
  have heq : C.chart j ⁻¹' (C.chart i '' F) =
      ⋃ p ∈ S, C.pull p.2.2 '' (C.pull p.2.1 ⁻¹' F) := by
    ext t
    constructor
    · rintro ⟨s, hs, hst⟩
      obtain ⟨p, hp, v, hvs, hvt⟩ := hSg s t (C.chart_eq_iff.1 hst)
      exact Set.mem_biUnion hp ⟨v, show C.pull p.2.1 v ∈ F from hvs ▸ hs, hvt⟩
    · intro ht
      obtain ⟨p, -, v, hv, rfl⟩ := Set.mem_iUnion₂.1 ht
      exact ⟨C.pull p.2.1 v, hv, C.chart_eq_iff.2 ⟨p.1, p.2.1, p.2.2, v, rfl, rfl⟩⟩
  rw [heq]
  refine hS.isClosed_biUnion fun p _ => ?_
  exact ((hFc.preimage (C.continuous_pull p.2.1)).isCompact.image
    (C.continuous_pull p.2.2)).isClosed

/-- With finite overlaps, every chart is a closed embedding into the glued
space. -/
theorem isClosedEmbedding_chart (hF : C.HasFiniteOverlaps) (i : C.Index) :
    IsClosedEmbedding (C.chart i) := by
  refine IsClosedEmbedding.of_continuous_injective_isClosedMap (C.continuous_chart i)
    (C.chart_injective i) fun F hFc => ?_
  rw [← isQuotientMap_quotient_mk'.isClosed_preimage, isClosed_sigma_iff]
  intro j
  exact C.isClosed_chart_preimage_image hF i j hFc

/-- With finite overlaps, chart images are closed. -/
theorem isClosed_range_chart (hF : C.HasFiniteOverlaps) (i : C.Index) :
    IsClosed (Set.range (C.chart i)) :=
  (C.isClosedEmbedding_chart hF i).isClosed_range

end AffinoidChartSystem

end Langlands.Analytic
