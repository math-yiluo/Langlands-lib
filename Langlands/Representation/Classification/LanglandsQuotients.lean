import Langlands.Representation.Classification.LanglandsData
import Langlands.Representation.Classification.CanonicalConstituents

/-!
# Canonical Langlands quotients and Zelevinsky subrepresentations for `GL_n`

The canonical head and socle constructors of `Classification/CanonicalConstituents`
applied to the induced representations of `Classification/Segments` and
`Classification/LanglandsData`: the Langlands quotient of each form of Langlands
data is the head of its induced representation, Zelevinsky's representation is the
socle, and the special representations attached to a segment are the head and the
socle of `i(ρ, νρ, …, ν^(m-1) ρ)` for a chosen supercuspidal representative `ρ`.

Each constructor is defined for every datum. It satisfies the corresponding
relation of `LanglandsData` or `Segments` exactly when some representation does, and
it is then isomorphic to every representation satisfying the relation. Existence
is not asserted.
-/

noncomputable section

open CategoryTheory

namespace Langlands

universe uV uF

namespace PadicField.TopologicalData

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p} (T : F.TopologicalData)

namespace CuspidalDatum

variable {T}

/-- A supercuspidal representative of a cuspidal datum, chosen from its class. -/
def representative (ρ : CuspidalDatum.{uV, uF} T) :
    letI := T.topology
    GeneralLinear.SupercuspidalRep.{uF, uV} (F := F.Carrier) (n := ρ.rank) :=
  letI := T.topology
  Quotient.out ρ.cls

theorem isRepresentedBy_representative (ρ : CuspidalDatum.{uV, uF} T) :
    ρ.IsRepresentedBy ρ.representative :=
  letI := T.topology
  Quotient.out_eq ρ.cls

end CuspidalDatum

section Segment

/-- The head of `i(ρ, νρ, …, ν^(m-1) ρ)` for the chosen representative `ρ` of the
beginning of `Δ`: the canonical candidate for `St(Δ)`, Kudla's `Q(Δ)`. -/
def segmentHead (Δ : Segment.{uV, uF} T) :
    letI := T.topology
    SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear Δ.degree F.Carrier) :=
  letI := T.topology
  (T.segmentInduced Δ.base.representative.obj Δ.length Δ.rank_pos).headQuotient

/-- The socle of `i(ρ, νρ, …, ν^(m-1) ρ)` for the chosen representative `ρ` of the
beginning of `Δ`: the canonical candidate for Zelevinsky's `⟨Δ⟩`. -/
def segmentSocle (Δ : Segment.{uV, uF} T) :
    letI := T.topology
    SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear Δ.degree F.Carrier) :=
  letI := T.topology
  (T.segmentInduced Δ.base.representative.obj Δ.length Δ.rank_pos).socleSubrepresentation

variable {T}

/-- Every segment head of `Δ` is isomorphic to `T.segmentHead Δ`. -/
theorem IsSegmentHead.nonempty_iso_segmentHead {Δ : Segment.{uV, uF} T}
    {π : letI := T.topology
      SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear Δ.degree F.Carrier)}
    (h : T.IsSegmentHead Δ π) : Nonempty (π ≅ T.segmentHead Δ) :=
  letI := T.topology
  SmoothRep.nonempty_iso_headQuotient
    ((T.isSegmentHead_iff Δ π _ Δ.base.isRepresentedBy_representative).mp h)

/-- Every segment socle of `Δ` is isomorphic to `T.segmentSocle Δ`. -/
theorem IsSegmentSocle.nonempty_iso_segmentSocle {Δ : Segment.{uV, uF} T}
    {π : letI := T.topology
      SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear Δ.degree F.Carrier)}
    (h : T.IsSegmentSocle Δ π) : Nonempty (π ≅ T.segmentSocle Δ) :=
  letI := T.topology
  SmoothRep.nonempty_iso_socleSubrepresentation
    ((T.isSegmentSocle_iff Δ π _ Δ.base.isRepresentedBy_representative).mp h)

/-- If `Δ` has a segment head, `T.segmentHead Δ` is one. -/
theorem IsSegmentHead.isSegmentHead_segmentHead {Δ : Segment.{uV, uF} T}
    {π : letI := T.topology
      SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear Δ.degree F.Carrier)}
    (h : T.IsSegmentHead Δ π) : T.IsSegmentHead Δ (T.segmentHead Δ) :=
  letI := T.topology
  (T.isSegmentHead_iff Δ _ _ Δ.base.isRepresentedBy_representative).mpr
    ((T.isSegmentHead_iff Δ π _ Δ.base.isRepresentedBy_representative).mp
      h).isIrreducibleHead_head

/-- If `Δ` has a segment socle, `T.segmentSocle Δ` is one. -/
theorem IsSegmentSocle.isSegmentSocle_segmentSocle {Δ : Segment.{uV, uF} T}
    {π : letI := T.topology
      SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear Δ.degree F.Carrier)}
    (h : T.IsSegmentSocle Δ π) : T.IsSegmentSocle Δ (T.segmentSocle Δ) :=
  letI := T.topology
  (T.isSegmentSocle_iff Δ _ _ Δ.base.isRepresentedBy_representative).mpr
    ((T.isSegmentSocle_iff Δ π _ Δ.base.isRepresentedBy_representative).mp
      h).isIrreducibleSocle_socleRepresentation

/-- `T.segmentHead Δ` is a segment head of `Δ` exactly when `Δ` has one. -/
theorem isSegmentHead_segmentHead_iff (Δ : Segment.{uV, uF} T) :
    T.IsSegmentHead Δ (T.segmentHead Δ) ↔
      ∃ π : letI := T.topology
        SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear Δ.degree F.Carrier),
        T.IsSegmentHead Δ π :=
  ⟨fun h => ⟨_, h⟩, fun ⟨_, h⟩ => h.isSegmentHead_segmentHead⟩

/-- `T.segmentSocle Δ` is a segment socle of `Δ` exactly when `Δ` has one. -/
theorem isSegmentSocle_segmentSocle_iff (Δ : Segment.{uV, uF} T) :
    T.IsSegmentSocle Δ (T.segmentSocle Δ) ↔
      ∃ π : letI := T.topology
        SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear Δ.degree F.Carrier),
        T.IsSegmentSocle Δ π :=
  ⟨fun h => ⟨_, h⟩, fun ⟨_, h⟩ => h.isSegmentSocle_segmentSocle⟩

end Segment

namespace TemperedLanglandsDatum

variable {T} {n : ℕ} (d : TemperedLanglandsDatum.{uV, uF} T n)

/-- The Langlands quotient `J(d)`: the head of the standard module. -/
def langlandsQuotient :
    letI := T.topology
    SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear n F.Carrier) :=
  letI := T.topology
  d.standardModule.headQuotient

/-- The canonical quotient map of the standard module onto `J(d)`. -/
def toLanglandsQuotient :
    letI := T.topology
    d.standardModule ⟶ d.langlandsQuotient :=
  letI := T.topology
  d.standardModule.toHeadQuotient

theorem toLanglandsQuotient_surjective :
    letI := T.topology
    Function.Surjective (SmoothRep.hom d.toLanglandsQuotient) :=
  letI := T.topology
  SmoothRep.toHeadQuotient_surjective _

variable {d}

/-- Every Langlands head of `d` is isomorphic to `J(d)`. -/
theorem IsLanglandsHead.nonempty_iso_langlandsQuotient
    {π : letI := T.topology
      SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear n F.Carrier)}
    (h : d.IsLanglandsHead π) : Nonempty (π ≅ d.langlandsQuotient) :=
  letI := T.topology
  SmoothRep.nonempty_iso_headQuotient h

/-- If `d` has a Langlands head, `J(d)` is one. -/
theorem IsLanglandsHead.isLanglandsHead_langlandsQuotient
    {π : letI := T.topology
      SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear n F.Carrier)}
    (h : d.IsLanglandsHead π) : d.IsLanglandsHead d.langlandsQuotient :=
  letI := T.topology
  Classification.IsIrreducibleHead.isIrreducibleHead_head h

variable (d)

/-- `J(d)` is a Langlands head of `d` exactly when `d` has one. -/
theorem isLanglandsHead_langlandsQuotient_iff :
    d.IsLanglandsHead d.langlandsQuotient ↔
      ∃ π : letI := T.topology
        SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear n F.Carrier),
        d.IsLanglandsHead π :=
  ⟨fun h => ⟨_, h⟩, fun ⟨_, h⟩ => h.isLanglandsHead_langlandsQuotient⟩

end TemperedLanglandsDatum

namespace SquareIntegrableLanglandsDatum

variable {T} {n : ℕ} (d : SquareIntegrableLanglandsDatum.{uV, uF} T n)

/-- Henniart's `J(π_1, …, π_r)`: the head of `i(π_1, …, π_r)`. -/
def langlandsQuotient :
    letI := T.topology
    SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear n F.Carrier) :=
  letI := T.topology
  d.induced.headQuotient

/-- The canonical quotient map of `i(π_1, …, π_r)` onto `J(π_1, …, π_r)`. -/
def toLanglandsQuotient :
    letI := T.topology
    d.induced ⟶ d.langlandsQuotient :=
  letI := T.topology
  d.induced.toHeadQuotient

theorem toLanglandsQuotient_surjective :
    letI := T.topology
    Function.Surjective (SmoothRep.hom d.toLanglandsQuotient) :=
  letI := T.topology
  SmoothRep.toHeadQuotient_surjective _

variable {d}

/-- Every Langlands head of `d` is isomorphic to `J(π_1, …, π_r)`. -/
theorem IsLanglandsHead.nonempty_iso_langlandsQuotient
    {π : letI := T.topology
      SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear n F.Carrier)}
    (h : d.IsLanglandsHead π) : Nonempty (π ≅ d.langlandsQuotient) :=
  letI := T.topology
  SmoothRep.nonempty_iso_headQuotient h

/-- If `d` has a Langlands head, `J(π_1, …, π_r)` is one. -/
theorem IsLanglandsHead.isLanglandsHead_langlandsQuotient
    {π : letI := T.topology
      SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear n F.Carrier)}
    (h : d.IsLanglandsHead π) : d.IsLanglandsHead d.langlandsQuotient :=
  letI := T.topology
  Classification.IsIrreducibleHead.isIrreducibleHead_head h

variable (d)

/-- `J(π_1, …, π_r)` is a Langlands head of `d` exactly when `d` has one. -/
theorem isLanglandsHead_langlandsQuotient_iff :
    d.IsLanglandsHead d.langlandsQuotient ↔
      ∃ π : letI := T.topology
        SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear n F.Carrier),
        d.IsLanglandsHead π :=
  ⟨fun h => ⟨_, h⟩, fun ⟨_, h⟩ => h.isLanglandsHead_langlandsQuotient⟩

end SquareIntegrableLanglandsDatum

/-- The segment family `Δ_1, …, Δ_r` with the blocks `T.segmentHead Δ_i`. -/
def segmentHeadDatum {r : ℕ} (Δ : Fin r → Segment.{uV, uF} T) {n : ℕ}
    (h : ∑ i, (Δ i).degree = n) : SegmentProductDatum.{uV, uF} T n where
  length := r
  segments := Δ
  degree_sum := h
  blocks i := T.segmentHead (Δ i)

/-- The segment family `Δ_1, …, Δ_r` with the blocks `T.segmentSocle Δ_i`. -/
def segmentSocleDatum {r : ℕ} (Δ : Fin r → Segment.{uV, uF} T) {n : ℕ}
    (h : ∑ i, (Δ i).degree = n) : SegmentProductDatum.{uV, uF} T n where
  length := r
  segments := Δ
  degree_sum := h
  blocks i := T.segmentSocle (Δ i)

/-- The blocks of `T.segmentHeadDatum Δ h` are segment heads exactly when every
segment has one. -/
theorem hasSegmentHeads_segmentHeadDatum_iff {r : ℕ} (Δ : Fin r → Segment.{uV, uF} T)
    {n : ℕ} (h : ∑ i, (Δ i).degree = n) :
    (T.segmentHeadDatum Δ h).HasSegmentHeads ↔
      ∀ i, ∃ π : letI := T.topology
        SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear (Δ i).degree F.Carrier),
        T.IsSegmentHead (Δ i) π :=
  forall_congr' fun i => T.isSegmentHead_segmentHead_iff (Δ i)

/-- The blocks of `T.segmentSocleDatum Δ h` are segment socles exactly when every
segment has one. -/
theorem hasSegmentSocles_segmentSocleDatum_iff {r : ℕ} (Δ : Fin r → Segment.{uV, uF} T)
    {n : ℕ} (h : ∑ i, (Δ i).degree = n) :
    (T.segmentSocleDatum Δ h).HasSegmentSocles ↔
      ∀ i, ∃ π : letI := T.topology
        SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear (Δ i).degree F.Carrier),
        T.IsSegmentSocle (Δ i) π :=
  forall_congr' fun i => T.isSegmentSocle_segmentSocle_iff (Δ i)

namespace SegmentProductDatum

variable {T} {n : ℕ} (d : SegmentProductDatum.{uV, uF} T n)

/-- The segment form of the Langlands quotient: the head of `i(π_1, …, π_r)`. -/
def langlandsQuotient :
    letI := T.topology
    SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear n F.Carrier) :=
  letI := T.topology
  d.induced.headQuotient

/-- The canonical quotient map of `i(π_1, …, π_r)` onto its head. -/
def toLanglandsQuotient :
    letI := T.topology
    d.induced ⟶ d.langlandsQuotient :=
  letI := T.topology
  d.induced.toHeadQuotient

theorem toLanglandsQuotient_surjective :
    letI := T.topology
    Function.Surjective (SmoothRep.hom d.toLanglandsQuotient) :=
  letI := T.topology
  SmoothRep.toHeadQuotient_surjective _

/-- Zelevinsky's form: the socle of `i(π_1, …, π_r)`. -/
def zelevinskySubrepresentation :
    letI := T.topology
    SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear n F.Carrier) :=
  letI := T.topology
  d.induced.socleSubrepresentation

/-- The canonical inclusion of the socle into `i(π_1, …, π_r)`. -/
def ofZelevinskySubrepresentation :
    letI := T.topology
    d.zelevinskySubrepresentation ⟶ d.induced :=
  letI := T.topology
  d.induced.ofSocleSubrepresentation

theorem ofZelevinskySubrepresentation_injective :
    letI := T.topology
    Function.Injective (SmoothRep.hom d.ofZelevinskySubrepresentation) :=
  letI := T.topology
  SmoothRep.ofSocleSubrepresentation_injective _

variable {d}

/-- Every Langlands head of `d` is isomorphic to the head of `i(π_1, …, π_r)`. -/
theorem IsLanglandsHead.nonempty_iso_langlandsQuotient
    {π : letI := T.topology
      SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear n F.Carrier)}
    (h : d.IsLanglandsHead π) : Nonempty (π ≅ d.langlandsQuotient) :=
  letI := T.topology
  SmoothRep.nonempty_iso_headQuotient h.2.2

/-- If `d` has a Langlands head, the head of `i(π_1, …, π_r)` is one. -/
theorem IsLanglandsHead.isLanglandsHead_langlandsQuotient
    {π : letI := T.topology
      SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear n F.Carrier)}
    (h : d.IsLanglandsHead π) : d.IsLanglandsHead d.langlandsQuotient :=
  letI := T.topology
  ⟨h.1, h.2.1, Classification.IsIrreducibleHead.isIrreducibleHead_head h.2.2⟩

/-- Every Zelevinsky socle of `d` is isomorphic to the socle of `i(π_1, …, π_r)`. -/
theorem IsZelevinskySocle.nonempty_iso_zelevinskySubrepresentation
    {π : letI := T.topology
      SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear n F.Carrier)}
    (h : d.IsZelevinskySocle π) : Nonempty (π ≅ d.zelevinskySubrepresentation) :=
  letI := T.topology
  SmoothRep.nonempty_iso_socleSubrepresentation h.2.2

/-- If `d` has a Zelevinsky socle, the socle of `i(π_1, …, π_r)` is one. -/
theorem IsZelevinskySocle.isZelevinskySocle_zelevinskySubrepresentation
    {π : letI := T.topology
      SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear n F.Carrier)}
    (h : d.IsZelevinskySocle π) : d.IsZelevinskySocle d.zelevinskySubrepresentation :=
  letI := T.topology
  ⟨h.1, h.2.1,
    Classification.IsIrreducibleSocle.isIrreducibleSocle_socleRepresentation h.2.2⟩

variable (d)

/-- The head of `i(π_1, …, π_r)` is a Langlands head of `d` exactly when `d` has
one. -/
theorem isLanglandsHead_langlandsQuotient_iff :
    d.IsLanglandsHead d.langlandsQuotient ↔
      ∃ π : letI := T.topology
        SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear n F.Carrier),
        d.IsLanglandsHead π :=
  ⟨fun h => ⟨_, h⟩, fun ⟨_, h⟩ => h.isLanglandsHead_langlandsQuotient⟩

/-- The socle of `i(π_1, …, π_r)` is a Zelevinsky socle of `d` exactly when `d` has
one. -/
theorem isZelevinskySocle_zelevinskySubrepresentation_iff :
    d.IsZelevinskySocle d.zelevinskySubrepresentation ↔
      ∃ π : letI := T.topology
        SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear n F.Carrier),
        d.IsZelevinskySocle π :=
  ⟨fun h => ⟨_, h⟩, fun ⟨_, h⟩ => h.isZelevinskySocle_zelevinskySubrepresentation⟩

end SegmentProductDatum

end PadicField.TopologicalData

end Langlands
