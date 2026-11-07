import Langlands.Representation.Classification.OrderedSegmentHeadProductIndependence
import Langlands.Representation.Classification.AdjacentUnlinkedSegmentSocleSwapProof
import Langlands.Representation.Classification.SegmentSocleProductData
import Langlands.Representation.Classification.SegmentHeadDecreasingSocle
import Langlands.Representation.Classification.HeadTargetTransport

/-!
# Zelevinsky socles of one multisegment are isomorphic

Ordered products of segment socles depend, up to actual isomorphism, only on
their multisegment; the argument is that of
`orderedSegmentHeadProductIndependence`, with the proved adjacent socle swap.
Hence two Zelevinsky socles of one multisegment are isomorphic. The head and
socle relations of a multisegment are also transported along isomorphisms of
the representation.
-/

noncomputable section

namespace Langlands.Classification

open CategoryTheory PadicField.TopologicalData

universe uF uV

private theorem socleProduct_ofFn_eq_of_orderIso {α : Type*} {r s : ℕ}
    (f : Fin r → α) (g : Fin s → α) (a : Fin r ≃o Fin s)
    (h : ∀ i, f i = g (a i)) : List.ofFn f = List.ofFn g := by
  have hrs : r = s := by simpa using Fintype.card_congr a.toEquiv
  subst s
  have ha : a = OrderIso.refl (Fin r) := Subsingleton.elim _ _
  have hf : f = g := funext fun i => by
    simpa only [ha, OrderIso.refl_apply] using h i
  rw [hf]

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData)

/-- Same-list data with actual segment socles induce isomorphic products. -/
theorem nonempty_socleProduct_iso_of_segmentList_eq {n : ℕ}
    {d d' : T.SegmentProductDatum.{max uF uV, uF} n}
    (h : List.ofFn d.segments = List.ofFn d'.segments)
    (hd : d.HasSegmentSocles) (hd' : d'.HasSegmentSocles) :
    letI := T.topology; Nonempty (d.induced ≅ d'.induced) := by
  let := T.topology
  obtain ⟨r, Δ, hs, B⟩ := d
  obtain ⟨r', Δ', hs', B'⟩ := d'
  have hr : r = r' := by
    simpa only [List.length_ofFn] using congrArg List.length h
  subst r'
  have hΔ : Δ = Δ' := List.ofFn_injective h
  subst Δ'
  have e : ∀ i, B i ≅ B' i := fun i =>
    (hd i).nonempty_iso_segmentSocle.some ≪≫
      (hd' i).nonempty_iso_segmentSocle.some.symm
  exact ⟨(T.normalizedProductInductionFunctor _).mapIso (Pi.isoMk e)⟩

/-- Ordered products of supplied segment socles depend only on the multisegment. -/
theorem orderedSegmentSocleProductIndependence {n : ℕ}
    (d d' : T.SegmentProductDatum.{max uF uV, uF} n)
    (ho : d.IsPrecedenceOrdered) (ho' : d'.IsPrecedenceOrdered)
    (hd : d.HasSegmentSocles) (hd' : d'.HasSegmentSocles)
    (hm : d.multisegment = d'.multisegment) :
    letI := T.topology; Nonempty (d.induced ≅ d'.induced) := by
  classical
  let := T.topology
  obtain ⟨e, he⟩ :=
    Langlands.Combinatorics.exists_equiv_of_ofFn_multiset_eq d.segments d'.segments hm
  let x (i : Fin d.length) : ℝ := -((e i).val : ℝ)
  let P (σ : Equiv.Perm (Fin d.length)) : Prop :=
    (d.permute σ).IsPrecedenceOrdered ∧ Nonempty (d.induced ≅ (d.permute σ).induced)
  have hP0 : P (Equiv.refl _) := ⟨ho, ⟨Iso.refl _⟩⟩
  have hPstep : ∀ σ, P σ → ∀ j (h : j + 1 < d.length),
      x (σ ⟨j, by omega⟩) < x (σ ⟨j + 1, h⟩) →
      P ((Equiv.swap ⟨j, by omega⟩ ⟨j + 1, h⟩).trans σ) := by
    intro σ hP j h hlt
    let D := d.permute σ
    have hinv : e (σ ⟨j + 1, h⟩) < e (σ ⟨j, by omega⟩) := by
      dsimp only [x] at hlt
      exact_mod_cast (neg_lt_neg_iff.mp hlt)
    have hu : ¬ (D.segments ⟨j, by change j < d.length; omega⟩).IsLinked
        (D.segments ⟨j + 1, h⟩) := by
      intro hlink
      rcases hlink.precedes_or_precedes with hp | hp
      · exact hP.1 ⟨j, by change j < d.length; omega⟩ ⟨j + 1, h⟩ (by
          change j < j + 1
          omega) hp
      · apply ho' _ _ hinv
        change (d.segments (σ ⟨j + 1, h⟩)).Precedes
          (d.segments (σ ⟨j, by omega⟩)) at hp
        rwa [he, he] at hp
    have horder := hP.1.permute_adjacentSwap j h hu
    obtain ⟨e₁⟩ := hP.2
    obtain ⟨e₂⟩ := adjacentUnlinkedSegmentSocleSwap.{uF, uV} F T n D (hd.permute σ) j h hu
    exact ⟨horder, ⟨e₁ ≪≫ e₂⟩⟩
  obtain ⟨σ, hP, hanti⟩ := Combinatorics.finitePermutationSorting d.length x P hP0 hPstep
  have hmono : Monotone (σ.trans e) := by
    intro i j hij
    have h := hanti hij
    change -((e (σ j)).val : ℝ) ≤ -((e (σ i)).val : ℝ) at h
    exact_mod_cast (neg_le_neg_iff.mp h)
  have hstrict : StrictMono (σ.trans e) :=
    hmono.strictMono_of_injective (σ.trans e).injective
  let a : Fin d.length ≃o Fin d'.length :=
    { toEquiv := σ.trans e
      map_rel_iff' := hstrict.le_iff_le }
  have hlist : List.ofFn (d.permute σ).segments = List.ofFn d'.segments :=
    socleProduct_ofFn_eq_of_orderIso _ _ a (fun i => by
      change d.segments (σ i) = d'.segments (e (σ i))
      exact he (σ i))
  obtain ⟨E⟩ := nonempty_socleProduct_iso_of_segmentList_eq F T hlist (hd.permute σ) hd'
  obtain ⟨E₀⟩ := hP.2
  exact ⟨E₀ ≪≫ E⟩

variable {F T}

/-- Two Zelevinsky socles of one multisegment are isomorphic. -/
theorem nonempty_iso_of_isZelevinskySocle {n : ℕ} {a : T.Multisegment.{max uF uV, uF}}
    {π π' : letI := T.topology
      SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear n F.Carrier)}
    (h : a.IsZelevinskySocle π) (h' : a.IsZelevinskySocle π') :
    letI := T.topology; Nonempty (π ≅ π') := by
  let := T.topology
  obtain ⟨d, hd, ho, hs, hsoc⟩ := h
  obtain ⟨d', hd', ho', hs', hsoc'⟩ := h'
  obtain ⟨E⟩ := orderedSegmentSocleProductIndependence F T d d' ho ho' hs hs' (hd.trans hd'.symm)
  have hsoc'' : IsIrreducibleSocle d.induced.representation π'.representation :=
    hsoc'.of_equiv (SmoothRep.equivOfIso E).symm
  obtain ⟨hπ', j, hj, -⟩ := hsoc''
  obtain ⟨e⟩ := hsoc.nonempty_equiv_of_subrepresentation hπ' j hj
  exact ⟨(SmoothRep.mkIso e).symm⟩

/-- A Langlands head of a multisegment may be replaced by an isomorphic
representation. -/
theorem Multisegment.IsLanglandsHead.of_iso {n : ℕ} {a : T.Multisegment.{max uF uV, uF}}
    {π π' : letI := T.topology
      SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear n F.Carrier)}
    (h : a.IsLanglandsHead π) (e : letI := T.topology; π ≅ π') : a.IsLanglandsHead π' := by
  let := T.topology
  obtain ⟨d, hd, ho, hh, hhead⟩ := h
  exact ⟨d, hd, ho, hh, hhead.of_targetEquiv (SmoothRep.equivOfIso e)⟩

/-- A Zelevinsky socle of a multisegment may be replaced by an isomorphic
representation. -/
theorem Multisegment.IsZelevinskySocle.of_iso {n : ℕ} {a : T.Multisegment.{max uF uV, uF}}
    {π π' : letI := T.topology
      SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear n F.Carrier)}
    (h : a.IsZelevinskySocle π) (e : letI := T.topology; π ≅ π') :
    a.IsZelevinskySocle π' := by
  let := T.topology
  obtain ⟨d, hd, ho, hs, hsoc⟩ := h
  exact ⟨d, hd, ho, hs, hsoc.of_targetEquiv (SmoothRep.equivOfIso e)⟩

end Langlands.Classification
