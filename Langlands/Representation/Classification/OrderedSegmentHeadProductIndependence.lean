import Langlands.Representation.Classification.AdjacentUnlinkedSegmentSwapProof
import Langlands.Representation.Classification.SegmentLinkageOrientationProof
import Langlands.Representation.Classification.LanglandsQuotients
import Langlands.Representation.Classification.MultisegmentClassificationStatement
import Langlands.Representation.Classification.SquareIntegrableLanglandsClassificationReduction
import Langlands.Combinatorics.FinitePermutationSortingProof
import Batteries.Data.List.Perm
import Langlands.Combinatorics.FiniteOccurrenceMatching

/-! # Independence of ordered products of special segment heads

Sorting by prescribed occurrence positions uses only swaps of unlinked pairs.
The resulting actual product isomorphism has no classification premise.
-/

noncomputable section

namespace Langlands.Classification

open CategoryTheory PadicField.TopologicalData

universe uF uV

private theorem headProduct_ofFn_eq_of_orderIso {α : Type*} {r s : ℕ}
    (f : Fin r → α) (g : Fin s → α) (a : Fin r ≃o Fin s)
    (h : ∀ i, f i = g (a i)) : List.ofFn f = List.ofFn g := by
  have hrs : r = s := by simpa using Fintype.card_congr a.toEquiv
  subst s
  have ha : a = OrderIso.refl (Fin r) := Subsingleton.elim _ _
  have hf : f = g := funext fun i => by
    simpa only [ha, OrderIso.refl_apply] using h i
  rw [hf]

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData)

/-- Same-list data with actual special segment heads induce isomorphic products. -/
theorem nonempty_headProduct_iso_of_segmentList_eq {n : ℕ}
    {d d' : T.SegmentProductDatum.{max uF uV, uF} n}
    (h : List.ofFn d.segments = List.ofFn d'.segments)
    (hd : d.HasSegmentHeads) (hd' : d'.HasSegmentHeads) :
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
    (hd i).nonempty_iso_segmentHead.some ≪≫
      (hd' i).nonempty_iso_segmentHead.some.symm
  exact ⟨(T.normalizedProductInductionFunctor _).mapIso (Pi.isoMk e)⟩

/-- Ordered products of supplied special heads depend only on the multisegment,
including each repeated occurrence. This asserts an actual product isomorphism. -/
def OrderedSegmentHeadProductIndependence : Prop :=
  letI := T.topology
  ∀ (n : ℕ) (d d' : T.SegmentProductDatum.{max uF uV, uF} n),
    d.IsPrecedenceOrdered → d'.IsPrecedenceOrdered →
    d.HasSegmentHeads → d'.HasSegmentHeads →
    d.multisegment = d'.multisegment → Nonempty (d.induced ≅ d'.induced)

/-- Adjacent unlinked commutation proves independence of all permitted orderings
and all supplied actual special-head representatives. -/
theorem orderedSegmentHeadProductIndependence :
    OrderedSegmentHeadProductIndependence.{uF, uV} F T := by
  classical
  let := T.topology
  intro n d d' ho ho' hd hd' hm
  obtain ⟨e, he⟩ := Langlands.Combinatorics.exists_equiv_of_ofFn_multiset_eq d.segments d'.segments hm
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
    obtain ⟨e₂⟩ := adjacentUnlinkedSegmentSwap.{uF, uV} F T n D (hd.permute σ) j h hu
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
    headProduct_ofFn_eq_of_orderIso _ _ a (fun i => by
      change d.segments (σ i) = d'.segments (e (σ i))
      exact he (σ i))
  obtain ⟨E⟩ := nonempty_headProduct_iso_of_segmentList_eq F T hlist (hd.permute σ) hd'
  obtain ⟨E₀⟩ := hP.2
  exact ⟨E₀ ≪≫ E⟩

/-- Equality of segment multisets identifies any two weak quotients once
strong heads of the ordered products are known. No injectivity or other
classification premise is used in this implication. -/
theorem nonempty_langlandsQuotient_iso_of_multisegment_eq
    (hh : OrderedMultisegmentHeadExistence.{uF, uV} F T)
    {n : ℕ} {d d' : T.SegmentProductDatum.{max uF uV, uF} n}
    {π π' : letI := T.topology;
      SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear n F.Carrier)}
    (hπ : d.IsLanglandsQuotient π) (hπ' : d'.IsLanglandsQuotient π')
    (hm : d.multisegment = d'.multisegment) :
    letI := T.topology; Nonempty (π ≅ π') := by
  let := T.topology
  obtain ⟨E⟩ := orderedSegmentHeadProductIndependence F T n d d'
    hπ.1 hπ'.1 hπ.2.1 hπ'.2.1 hm
  obtain ⟨ρ, hρ⟩ := hh n d hπ.1 hπ.2.1
  exact nonempty_iso_of_isIrreducibleHead hρ.2.2 hπ.2.2
    (hπ'.2.2.of_equiv (SmoothRep.equivOfIso E).symm)

end Langlands.Classification
