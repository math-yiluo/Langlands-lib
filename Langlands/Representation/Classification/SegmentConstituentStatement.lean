import Langlands.Representation.Classification.Segments

/-!
# The two irreducible constituents attached to a segment

For a segment `Δ = [ρ, ν^(m-1) ρ]` of irreducible supercuspidal classes, Ze80
attaches two irreducible representations of `GL_{mr}(F)`:

* Zelevinsky's `⟨Δ⟩` (Ze80 §3.1), the unique irreducible subrepresentation of
  the increasing product `ρ × νρ × ⋯ × ν^(m-1) ρ` and the unique irreducible
  quotient of the decreasing product `ν^(m-1) ρ × ⋯ × νρ × ρ`;
* the special representation `⟨Δ⟩^t` (Ze80 §9.1), the unique irreducible
  quotient of the increasing product and the unique irreducible subrepresentation
  of the decreasing product.

Both are existence-and-uniqueness assertions about actual subobjects and
quotient objects; no constituent is chosen. For segments of length at least two
the two constituents are not isomorphic, and for characters of `GL_1(F)` the
constituent `⟨Δ⟩` is the character `ν^((m-1)/2) χ ∘ det`.
-/

namespace Langlands.Classification

open CategoryTheory GeneralLinear

universe uF uV

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData)

/-- Ze80 §3.1 (via Proposition 2.10): for every segment `Δ` some irreducible
`π` is the unique irreducible subrepresentation of `ρ × νρ × ⋯ × ν^(m-1) ρ`
(as a subobject) and, for every actual representative `ρ` of the beginning,
the unique irreducible quotient of `ν^(m-1) ρ × ⋯ × νρ × ρ` (as a quotient
object). -/
def SegmentZelevinskyConstituentExistence : Prop :=
  letI := T.topology
  ∀ Δ : T.Segment.{uV, uF},
    ∃ π : SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear Δ.degree F.Carrier),
      T.IsSegmentSocle Δ π ∧
        ∀ A : SupercuspidalRep.{uF, uV} (F := F.Carrier) (n := Δ.rank),
          Δ.base.IsRepresentedBy A →
            IsIrreducibleHead
              (T.segmentInducedDown A.obj Δ.length Δ.rank_pos).representation
              π.representation

/-- Ze80 §3.1: any two irreducible subrepresentations of
`ρ × νρ × ⋯ × ν^(m-1) ρ` are isomorphic. -/
def SegmentZelevinskyConstituentUniqueness : Prop :=
  letI := T.topology
  ∀ (Δ : T.Segment.{uV, uF})
    (π π' : SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear Δ.degree F.Carrier)),
    T.IsSegmentSubrepresentation Δ π → T.IsSegmentSubrepresentation Δ π' →
      Nonempty (π ≅ π')

/-- Ze80 §9.1 (via Proposition 2.10): for every segment `Δ` some irreducible
`π` is the unique irreducible quotient of `ρ × νρ × ⋯ × ν^(m-1) ρ` (as a
quotient object) and, for every actual representative `ρ` of the beginning,
the unique irreducible subrepresentation of `ν^(m-1) ρ × ⋯ × νρ × ρ` (as a
subobject). -/
def SegmentSpecialConstituentExistence : Prop :=
  letI := T.topology
  ∀ Δ : T.Segment.{uV, uF},
    ∃ π : SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear Δ.degree F.Carrier),
      T.IsSegmentHead Δ π ∧
        ∀ A : SupercuspidalRep.{uF, uV} (F := F.Carrier) (n := Δ.rank),
          Δ.base.IsRepresentedBy A →
            IsIrreducibleSocle
              (T.segmentInducedDown A.obj Δ.length Δ.rank_pos).representation
              π.representation

/-- Ze80 §9.1: any two irreducible quotients of `ρ × νρ × ⋯ × ν^(m-1) ρ` are
isomorphic. -/
def SegmentSpecialConstituentUniqueness : Prop :=
  letI := T.topology
  ∀ (Δ : T.Segment.{uV, uF})
    (π π' : SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear Δ.degree F.Carrier)),
    T.IsSegmentQuotient Δ π → T.IsSegmentQuotient Δ π' →
      Nonempty (π ≅ π')

/-- Ze80 Theorem 2.2 with §§3.1 and 9.1: for a segment with at least two
elements, no irreducible subrepresentation of `ρ × νρ × ⋯ × ν^(m-1) ρ` is
isomorphic to an irreducible quotient of it. -/
def SegmentConstituentsDistinct : Prop :=
  letI := T.topology
  ∀ (Δ : T.Segment.{uV, uF}), 2 ≤ Δ.length →
    ∀ π π' : SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear Δ.degree F.Carrier),
      T.IsSegmentSubrepresentation Δ π → T.IsSegmentQuotient Δ π' →
        IsEmpty (π ≅ π')

/-- Ze80 Example 3.2: if the beginning of `Δ` is represented by a character
`χ ∘ det` of `GL_1(F)`, every irreducible subrepresentation of
`χ × νχ × ⋯ × ν^(m-1) χ` acts by the character `ν^((m-1)/2) χ ∘ det` of
`GL_m(F)`. -/
def SegmentRankOneZelevinskyCharacter : Prop :=
  letI := T.topology
  ∀ (Δ : T.Segment.{uV, uF}) (χ : F.Carrierˣ →* ℂˣ)
    (A : SupercuspidalRep.{uF, uV} (F := F.Carrier) (n := Δ.rank)),
    Δ.rank = 1 → Δ.base.IsRepresentedBy A →
    HasScalarCharacter A.obj.representation (MonoidHom.id _)
      (χ.comp determinant) →
    ∀ π : SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear Δ.degree F.Carrier),
      T.IsSegmentSubrepresentation Δ π →
        HasScalarCharacter π.representation (MonoidHom.id _)
          (T.determinantPowerCharacter Δ.degree (((Δ.length : ℝ) - 1) / 2) *
            χ.comp determinant)

/-- All statements of this module for one p-adic field and topological
realization. -/
def SegmentConstituentTheorems : Prop :=
  SegmentZelevinskyConstituentExistence.{uF, uV} F T ∧
    SegmentZelevinskyConstituentUniqueness.{uF, uV} F T ∧
    SegmentSpecialConstituentExistence.{uF, uV} F T ∧
    SegmentSpecialConstituentUniqueness.{uF, uV} F T ∧
    SegmentConstituentsDistinct.{uF, uV} F T ∧
    SegmentRankOneZelevinskyCharacter.{uF, uV} F T

/-- The segment-constituent statements over every prime, every actual finite
p-adic extension and every compatible topological realization. -/
def PadicSegmentConstituentTheorems : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData),
    SegmentConstituentTheorems.{uF, uV} F T

end Langlands.Classification
