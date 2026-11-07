import Langlands.Correspondence.AssemblyBijectiveReduction
import Langlands.Correspondence.AssemblySquareIntegrablePreimageReduction
import Langlands.Correspondence.RankOneComparison
import Langlands.Representation.Classification.SegmentUniverseLift
import Langlands.Representation.Classification.OrderedSegmentHeadProductIndependence
import Langlands.Representation.Classification.SquareIntegrableLanglandsClassificationReduction
import Langlands.WeilDeligne.DecompositionUniquenessProof

/-!
# Uniqueness of the assembly

Two automorphic classes assembled from the same parameter class by the same
supercuspidal map are equal. The published uniqueness of block decompositions
matches the two block decompositions, so the two multisegments are equal; the
published independence of ordered products of segment heads makes any two
Langlands heads of one multisegment isomorphic. No hypothesis is needed: this
is the uniqueness half of `AssemblyWellDefinedStatement`.
-/

noncomputable section

namespace Langlands.Correspondence

universe uF uP uA

open PadicField.TopologicalData

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

local instance assemblyUniquenessFieldTopology : TopologicalSpace F.Carrier :=
  F.canonicalTopologicalData.topology

local instance assemblyUniquenessGeneralLinearTopology (n : ℕ) :
    TopologicalSpace (GeneralLinear n F.Carrier) :=
  F.canonicalGeneralLinearTopology n

namespace AssemblyUniqueness

/-- Segments of equal length beginning at the images of equal underlying Weil
classes of equal rank are equal. -/
theorem segmentOf_eq_of (c0 : SupercuspidalMap.{uF, uP, uA} F) {d d' : ℕ}
    (σ : IrreducibleWeilClass.{uF, uP} F d.succPNat)
    (σ' : IrreducibleWeilClass.{uF, uP} F d'.succPNat) {m m' : ℕ} (hd : d = d')
    (hσ : weilClassForget F σ = weilClassForget F σ') (hm : m = m') :
    segmentOf F c0 σ m = segmentOf F c0 σ' m' := by
  subst hd hm
  rw [weilClassForget_injective F hσ]

/-- Families that differ by a reindexing list the same multiset. -/
theorem coe_ofFn_eq_of_equiv {X : Type*} {r r' : ℕ} (e : Fin r ≃ Fin r') (f : Fin r → X)
    (f' : Fin r' → X) (h : ∀ i, f i = f' (e i)) :
    ((List.ofFn f : List X) : Multiset X) = (List.ofFn f' : Multiset X) := by
  rw [← Fin.univ_val_map, ← Fin.univ_val_map, show f = f' ∘ e from funext h,
    ← Multiset.map_map, Multiset.map_univ_val_equiv]

variable {F} in
/-- Two Langlands heads of the same multisegment are isomorphic: by the published
independence of ordered products of segment heads, the two precedence-ordered
data have isomorphic induced representations, whose irreducible heads agree. -/
theorem nonempty_iso_of_isLanglandsHead {n : ℕ}
    {a : Multisegment.{max uF uA, uF} F.canonicalTopologicalData}
    {π π' : SmoothRep.{0, uF, max uF uA} ℂ (GeneralLinear n F.Carrier)}
    (hπ : a.IsLanglandsHead π) (hπ' : a.IsLanglandsHead π') : Nonempty (π ≅ π') := by
  obtain ⟨d, hd, ho, hh, hH⟩ := hπ
  obtain ⟨d', hd', ho', hh', hH'⟩ := hπ'
  obtain ⟨E⟩ := Classification.orderedSegmentHeadProductIndependence.{uF, uA} F
    F.canonicalTopologicalData n d d' ho ho' hh hh' (hd.trans hd'.symm)
  have hq := (show d.IsLanglandsHead π from ⟨ho, hh, hH⟩).isLanglandsQuotient.2.2
  have hq' := (show d'.IsLanglandsHead π' from ⟨ho', hh', hH'⟩).isLanglandsQuotient.2.2
  exact Classification.nonempty_iso_of_isIrreducibleHead hH hq
    (hq'.of_equiv (SmoothRep.equivOfIso E).symm)

end AssemblyUniqueness

open AssemblyUniqueness in
/-- Uniqueness of the assembly: two automorphic classes assembled from the same
parameter class by the same supercuspidal map are equal. -/
theorem isAssembledFrom_unique (c0 : SupercuspidalMap.{uF, uP, uA} F) {n : ℕ+}
    {D : WeilDeligneClass.{uF, uP} F n} {π π' : AutomorphicClass.{uF, uA} F n}
    (h : IsAssembledFrom F c0 D π) (h' : IsAssembledFrom F c0 D π') : π = π' := by
  obtain ⟨r, d, m, σ, ⟨B, A, hB, hA, ⟨eA⟩⟩, ⟨Aut, J, rfl, hJ, ⟨eJ⟩⟩⟩ := h
  obtain ⟨r', d', m', σ', ⟨B', A', hB', hA', ⟨eA'⟩⟩, ⟨Aut', J', rfl, hJ', ⟨eJ'⟩⟩⟩ := h'
  obtain ⟨f⟩ := (WeilDeligneRepresentation.classOf_eq_iff A A').mp (hA.trans hA'.symm)
  let bd : Fin r → WeilDeligneRepresentation.BlockDatum.{0, uF, uP} ℂ
      (Weil.Local.localWeilGroup F) := fun i => ⟨B i, m i + 1, Nat.succ_pos _⟩
  let bd' : Fin r' → WeilDeligneRepresentation.BlockDatum.{0, uF, uP} ℂ
      (Weil.Local.localWeilGroup F) := fun j => ⟨B' j, m' j + 1, Nat.succ_pos _⟩
  obtain ⟨e, he⟩ := (WeilDeligneRepresentation.Blocks.decompositionUniqueness.{uF, uP, uP}
    (Weil.Local.localWeilGroup F) (Weil.Local.localNormCharacter F).toMonoidHom r r' bd bd'
    (fun i => isIrreducible_of_classOf_eq F (B i) (σ i) (hB i))
    (fun j => isIrreducible_of_classOf_eq F (B' j) (σ' j) (hB' j))).mp
      ⟨(eA.trans f).trans eA'.symm⟩
  have hseg : ∀ i, segmentOf F c0 (σ i) (m i) = segmentOf F c0 (σ' (e i)) (m' (e i)) := by
    intro i
    obtain ⟨hlen, ⟨g⟩⟩ := he i
    have hlen' : m i + 1 = m' (e i) + 1 := hlen
    have hrank : (B i).rank = (B' (e i)).rank := FiniteRepresentation.rank_eq_of_equiv g
    rw [rank_eq_of_classOf_eq F (σ i) (hB i), rank_eq_of_classOf_eq F (σ' (e i)) (hB' (e i))]
      at hrank
    refine segmentOf_eq_of F c0 (σ i) (σ' (e i)) ?_ ?_ (by omega)
    · simpa using hrank
    · rw [← hB i, ← hB' (e i)]
      exact (FiniteRepresentation.classOf_eq_iff _ _).mpr ⟨g⟩
  have hms : multisegmentOf F c0 σ m = multisegmentOf F c0 σ' m' :=
    coe_ofFn_eq_of_equiv e _ _ hseg
  rw [← hms] at hJ'
  have hJl := (Multisegment.isLanglandsHead_universeLift_iff _ J).mpr hJ
  have hJl' := (Multisegment.isLanglandsHead_universeLift_iff _ J').mpr hJ'
  obtain ⟨iso⟩ := nonempty_iso_of_isLanglandsHead hJl hJl'
  exact (automorphicClassOf_eq_iff F Aut Aut').mpr
    ⟨(eJ.symm.trans (SmoothRep.equivOfIso iso)).trans eJ'⟩

end Langlands.Correspondence
