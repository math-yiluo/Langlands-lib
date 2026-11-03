import Langlands.Representation.Classification.SegmentHeadContragredient
import Langlands.Representation.Classification.SegmentHeadProductFiniteness
import Langlands.Representation.Classification.SegmentTruncationObstructionStatement

/-! Optional truncations and actual products under smooth duality. -/

noncomputable section

open CategoryTheory

namespace Langlands.PadicField.TopologicalData

open GeneralLinear Classification.CuspidalProductContragredient

universe uF uV

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p} {T : F.TopologicalData}

namespace Segment

/-- Optional segment duality carries support to its cuspidal-dual image. -/
theorem optionalSupport_dual (A : Option (T.Segment.{uV, uF})) :
    optionalSupport (A.map dual) = dualDatum '' optionalSupport A := by
  cases A with
  | none => simp only [Option.map_none, optionalSupport, Set.image_empty]
  | some E => exact dual_support E

/-- A terminal truncation becomes an initial truncation after endpoint reversal. -/
theorem IsTerminalTruncation.dual {A : Option (T.Segment.{uV, uF})}
    {Δ : T.Segment.{uV, uF}} (h : IsTerminalTruncation A Δ) :
    IsInitialTruncation (A.map Segment.dual) Δ.dual := by
  cases A with
  | none => trivial
  | some E =>
    change E.support ⊆ Δ.support ∧ Δ.last ∈ E.support at h
    change E.dual.support ⊆ Δ.dual.support ∧ Δ.dual.base ∈ E.dual.support
    rw [dual_support E, dual_support Δ]
    exact ⟨Set.image_mono h.1, Set.mem_image_of_mem dualDatum h.2⟩

/-- An initial truncation becomes a terminal truncation after endpoint reversal. -/
theorem IsInitialTruncation.dual {A : Option (T.Segment.{uV, uF})}
    {Δ : T.Segment.{uV, uF}} (h : IsInitialTruncation A Δ) :
    IsTerminalTruncation (A.map Segment.dual) Δ.dual := by
  cases A with
  | none => trivial
  | some E =>
    change E.support ⊆ Δ.support ∧ Δ.base ∈ E.support at h
    change E.dual.support ⊆ Δ.dual.support ∧ Δ.dual.last ∈ E.dual.support
    rw [dual_support E, dual_support Δ, dual_last Δ]
    exact ⟨Set.image_mono h.1, Set.mem_image_of_mem dualDatum h.2⟩

@[simp]
theorem optional_dual_dual (A : Option (T.Segment.{uV, uF})) :
    (A.map dual).map dual = A := by
  cases A <;> simp

/-- Duality gives both directions of the optional initial/terminal conversion. -/
theorem isInitialTruncation_dual_iff (A : Option (T.Segment.{uV, uF}))
    (Δ : T.Segment.{uV, uF}) :
    IsInitialTruncation (A.map dual) Δ.dual ↔ IsTerminalTruncation A Δ := by
  constructor
  · intro h
    simpa only [optional_dual_dual, dual_dual] using h.dual
  · exact IsTerminalTruncation.dual

theorem isTerminalTruncation_dual_iff (A : Option (T.Segment.{uV, uF}))
    (Δ : T.Segment.{uV, uF}) :
    IsTerminalTruncation (A.map dual) Δ.dual ↔ IsInitialTruncation A Δ := by
  constructor
  · intro h
    simpa only [optional_dual_dual, dual_dual] using h.dual
  · exact IsInitialTruncation.dual

/-- The same conversion respects indexed unions, including an empty family. -/
theorem iUnion_optionalSupport_dual {ι : Type*}
    (A : ι → Option (T.Segment.{uV, uF})) :
    (⋃ i, optionalSupport ((A i).map dual)) =
      dualDatum '' (⋃ i, optionalSupport (A i)) := by
  simp only [optionalSupport_dual, Set.image_iUnion]

end Segment

namespace SegmentProductDatum

variable {n : ℕ}

/-- Dualize the actual block at every original label and reverse each segment's
endpoints. The ordered block sizes and total rank are unchanged. -/
def dual (d : T.SegmentProductDatum.{uV, uF} n) :
    T.SegmentProductDatum.{uV, uF} n := by
  letI := T.topology
  letI : ∀ r : ℕ, IsTopologicalGroup (GeneralLinear r F.Carrier) :=
    fun r => T.generalLinearTopologicalGroup r
  exact {
    length := d.length
    segments := fun i => (d.segments i).dual
    degree_sum := d.degree_sum
    blocks := fun i => (d.blocks i).contragredient }

@[simp]
theorem dual_length (d : T.SegmentProductDatum.{uV, uF} n) :
    d.dual.length = d.length := rfl

@[simp]
theorem dual_segments (d : T.SegmentProductDatum.{uV, uF} n) (i : Fin d.length) :
    d.dual.segments i = (d.segments i).dual := rfl

@[simp]
theorem dual_shape (d : T.SegmentProductDatum.{uV, uF} n) :
    d.dual.shape = d.shape := rfl

/-- The dual datum has supplied special heads at the original labels. -/
theorem HasSegmentHeads.dual {d : T.SegmentProductDatum.{uV, uF} n}
    (hd : d.HasSegmentHeads) : d.dual.HasSegmentHeads := by
  intro i
  exact (hd i).contragredient

/-- The induced object of the dual datum has the original block shape. -/
theorem dual_induced (d : T.SegmentProductDatum.{uV, uF} n) :
    letI := T.topology
    letI : ∀ r : ℕ, IsTopologicalGroup (GeneralLinear r F.Carrier) :=
      fun r => T.generalLinearTopologicalGroup r
    d.dual.induced = (T.normalizedProductInductionFunctor d.shape).obj
      (fun i => (d.blocks i).contragredient) := rfl

/-- The actual smooth dual of a supplied head product is isomorphic to the
same ordered product of the dual heads. -/
def contragredientInducedIso (d : T.SegmentProductDatum.{uV, uF} n)
    (hd : d.HasSegmentHeads) :
    letI := T.topology
    letI := T.generalLinearTopologicalGroup n
    d.induced.contragredient ≅ d.dual.induced := by
  letI := T.topology
  letI : ∀ r : ℕ, IsTopologicalGroup (GeneralLinear r F.Carrier) :=
    fun r => T.generalLinearTopologicalGroup r
  let e := Classical.choice
    (nonempty_contragredient_productEquiv T d.shape
      (fun i => (d.blocks i).representation) (fun i => (hd i).isAdmissible))
  rw [dual_induced]
  exact SmoothRep.mkIso e

end SegmentProductDatum
end Langlands.PadicField.TopologicalData
