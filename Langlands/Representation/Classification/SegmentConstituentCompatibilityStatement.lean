import Langlands.Representation.Classification.Segments
import Langlands.Representation.Smooth.Contragredient.Definitions

/-!
# Twists, contragredients and central characters of segment constituents

For a segment `Δ = [ρ, ν^(m-1) ρ]` these proposition definitions state how
Zelevinsky's `⟨Δ⟩` (the irreducible subrepresentation of
`ρ × νρ × ⋯ × ν^(m-1) ρ`) and the special representation `⟨Δ⟩^t` (its
irreducible quotient) behave under

* a common twist by a character of the determinant (BZ77 Proposition 1.9(f)),
* the smooth contragredient (Ze80 Propositions 3.3 and 9.4), and
* restriction to the scalar matrices (central characters).

The statements are relational: no constituent, dual segment or central
character is chosen.
-/

namespace Langlands.Classification

open CategoryTheory GeneralLinear

universe uF uV

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData)

/-- BZ77 Proposition 1.9(f) with Ze80 §§3.1 and 9.1: twisting by `ν^s` carries
the segment relations for `Δ` to those for `ν^s Δ = [ν^s ρ, ν^(s+m-1) ρ]`. -/
def SegmentConstituentRealTwistCompatibility : Prop :=
  letI := T.topology
  ∀ (Δ : T.Segment.{uV, uF}) (s : ℝ)
    (π : SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear Δ.degree F.Carrier)),
    (T.IsSegmentSocle Δ π ↔
        T.IsSegmentSocle (Δ.twist s)
          (π.twist (T.determinantPowerCharacter Δ.degree s)
            (T.isOpen_ker_determinantPowerCharacter Δ.degree s))) ∧
      (T.IsSegmentHead Δ π ↔
        T.IsSegmentHead (Δ.twist s)
          (π.twist (T.determinantPowerCharacter Δ.degree s)
            (T.isOpen_ker_determinantPowerCharacter Δ.degree s))) ∧
      (T.IsSegmentSubrepresentation Δ π ↔
        T.IsSegmentSubrepresentation (Δ.twist s)
          (π.twist (T.determinantPowerCharacter Δ.degree s)
            (T.isOpen_ker_determinantPowerCharacter Δ.degree s))) ∧
      (T.IsSegmentQuotient Δ π ↔
        T.IsSegmentQuotient (Δ.twist s)
          (π.twist (T.determinantPowerCharacter Δ.degree s)
            (T.isOpen_ker_determinantPowerCharacter Δ.degree s)))

/-- BZ77 Proposition 1.9(f) with Ze80 §§3.1 and 9.1: for a character `χ` of
`F^×` whose composite with the determinant has open kernel, twisting by
`χ ∘ det` carries the segment relations for `Δ` to those for the segment
`χΔ = [χρ, ν^(m-1) χρ]` of the same length. -/
def SegmentConstituentCharacterTwistCompatibility : Prop :=
  letI := T.topology
  ∀ (Δ : T.Segment.{uV, uF}) (χ : F.Carrierˣ →* ℂˣ)
    (hr : IsOpen ((χ.comp (determinant : GeneralLinear Δ.rank F.Carrier →* F.Carrierˣ)).ker :
      Set (GeneralLinear Δ.rank F.Carrier)))
    (hd : IsOpen ((χ.comp (determinant : GeneralLinear Δ.degree F.Carrier →* F.Carrierˣ)).ker :
      Set (GeneralLinear Δ.degree F.Carrier)))
    (π : SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear Δ.degree F.Carrier)),
    let Δχ : T.Segment.{uV, uF} :=
      { base :=
          { rank := Δ.rank
            rank_pos := Δ.rank_pos
            cls := SupercuspidalClass.twist
              (χ.comp (determinant : GeneralLinear Δ.rank F.Carrier →* F.Carrierˣ)) hr
              (ker_determinant_le_ker_comp χ) Δ.base.cls }
        length := Δ.length
        length_pos := Δ.length_pos }
    let πχ :=
      π.twist (χ.comp (determinant : GeneralLinear Δ.degree F.Carrier →* F.Carrierˣ)) hd
    (T.IsSegmentSocle Δ π ↔ T.IsSegmentSocle Δχ πχ) ∧
      (T.IsSegmentHead Δ π ↔ T.IsSegmentHead Δχ πχ) ∧
      (T.IsSegmentSubrepresentation Δ π ↔ T.IsSegmentSubrepresentation Δχ πχ) ∧
      (T.IsSegmentQuotient Δ π ↔ T.IsSegmentQuotient Δχ πχ)

/-- Ze80 Propositions 3.3 and 9.4: let `B` represent the end `ρ' = ν^(m-1) ρ`
of `Δ` and let `B'` be isomorphic to the smooth contragredient of `B`. The
segment `Δ^∨ = [ρ'^∨, ρ^∨]` begins at the class of `B'` and has the same
length. Every representation isomorphic to the smooth contragredient of an
irreducible subrepresentation (resp. quotient) of
`ρ × νρ × ⋯ × ν^(m-1) ρ` is the unique irreducible subobject (resp. quotient
object) of the corresponding product for `Δ^∨`. -/
def SegmentConstituentContragredientCompatibility : Prop :=
  letI := T.topology
  ∀ (Δ : T.Segment.{uV, uF}),
    letI := T.generalLinearTopologicalGroup Δ.rank
    letI := T.generalLinearTopologicalGroup Δ.degree
    ∀ (B B' : SupercuspidalRep.{uF, uV} (F := F.Carrier) (n := Δ.rank)),
      Δ.last.IsRepresentedBy B →
      Nonempty (B'.obj.representation.Equiv
        (smoothContragredient B.obj.representation)) →
      let Δv : T.Segment.{uV, uF} :=
        { base :=
            { rank := Δ.rank
              rank_pos := Δ.rank_pos
              cls := B'.isoClass }
          length := Δ.length
          length_pos := Δ.length_pos }
      ∀ π π' : SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear Δ.degree F.Carrier),
        Nonempty (π'.representation.Equiv
          (smoothContragredient π.representation)) →
        (T.IsSegmentSubrepresentation Δ π → T.IsSegmentSocle Δv π') ∧
          (T.IsSegmentQuotient Δ π → T.IsSegmentHead Δv π')

/-- Central characters: if the representative `A` of `ρ` has central character
`ω`, then the scalar matrix `z` acts on `ρ × νρ × ⋯ × ν^(m-1) ρ`, on
`ν^(m-1) ρ × ⋯ × ρ`, and on every irreducible subrepresentation or quotient of
the increasing product, by `ω(z)^m · ν^((m-1)/2)(z)`, where
`ν^((m-1)/2)(z) = |z|^(m r (m-1) / 2)` on `GL_{mr}(F)`. -/
def SegmentConstituentCentralCharacter : Prop :=
  letI := T.topology
  ∀ (Δ : T.Segment.{uV, uF}) (ω : F.Carrierˣ →* ℂˣ)
    (A : SupercuspidalRep.{uF, uV} (F := F.Carrier) (n := Δ.rank)),
    Δ.base.IsRepresentedBy A →
    HasScalarCharacter A.obj.representation GeneralLinear.scalar ω →
    let ωΔ : F.Carrierˣ →* ℂˣ :=
      ω ^ Δ.length *
        (T.determinantPowerCharacter Δ.degree (((Δ.length : ℝ) - 1) / 2)).comp
          GeneralLinear.scalar
    HasScalarCharacter (T.segmentInduced A.obj Δ.length Δ.rank_pos).representation
        GeneralLinear.scalar ωΔ ∧
      HasScalarCharacter (T.segmentInducedDown A.obj Δ.length Δ.rank_pos).representation
        GeneralLinear.scalar ωΔ ∧
      ∀ π : SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear Δ.degree F.Carrier),
        (T.IsSegmentSubrepresentation Δ π ∨ T.IsSegmentQuotient Δ π) →
          HasScalarCharacter π.representation GeneralLinear.scalar ωΔ

/-- All statements of this module for one p-adic field and topological
realization. -/
def SegmentConstituentCompatibilityTheorems : Prop :=
  SegmentConstituentRealTwistCompatibility.{uF, uV} F T ∧
    SegmentConstituentCharacterTwistCompatibility.{uF, uV} F T ∧
    SegmentConstituentContragredientCompatibility.{uF, uV} F T ∧
    SegmentConstituentCentralCharacter.{uF, uV} F T

/-- The segment-constituent compatibilities over every prime, every actual
finite p-adic extension and every compatible topological realization. -/
def PadicSegmentConstituentCompatibilityTheorems : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData),
    SegmentConstituentCompatibilityTheorems.{uF, uV} F T

end Langlands.Classification
