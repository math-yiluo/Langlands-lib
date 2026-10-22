import Langlands.Representation.Classification.LanglandsData
import Langlands.Representation.Classification.SegmentConstituentCompatibilityStatement
import Langlands.Representation.Classification.ConstituentCompatibility
import Langlands.Representation.Smooth.Contragredient.LawsProof
import Langlands.Group.GL.ReverseBlocks

/-!
# Compatibility of multisegment socles and Langlands heads

Proposition definitions for twists, the smooth contragredient and the product
of segment central characters. All constituents are the actual relations from
`LanglandsData`. No classification or compatibility assertion is proved here.
-/

noncomputable section

namespace Langlands.Classification

open CategoryTheory GeneralLinear PadicField.TopologicalData

universe uF uV

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData)

/-- Common real norm twists preserve and reflect the actual multisegment
socle and head relations (Ta86 §§1.8 and 5.6). -/
def MultisegmentConstituentRealTwistCompatibility : Prop :=
  letI := T.topology
  ∀ (n : ℕ), 0 < n →
  ∀ (a : T.Multisegment.{uV, uF}) (s : ℝ)
    (π : SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear n F.Carrier)),
    let πs := π.twist (T.determinantPowerCharacter n s)
      (T.isOpen_ker_determinantPowerCharacter n s)
    (a.IsZelevinskySocle π ↔ (a.twist s).IsZelevinskySocle πs) ∧
      (a.IsLanglandsHead π ↔ (a.twist s).IsLanglandsHead πs)

/-- BZ77 Proposition 1.9(f) applied to the multisegment relations: a smooth
character of `Fˣ` twists every cuspidal base and the final representation by
the actual determinant character. Openness on every matrix group is proved
by pulling back the given open kernel along the continuous determinant. -/
def MultisegmentConstituentCharacterTwistCompatibility : Prop :=
  letI := T.topology
  ∀ (χ : F.Carrierˣ →* ℂˣ) (hχ : IsOpen (χ.ker : Set F.Carrierˣ)),
    let hdet : ∀ k : ℕ,
        IsOpen ((χ.comp (determinant : GeneralLinear k F.Carrier →* F.Carrierˣ)).ker :
          Set (GeneralLinear k F.Carrier)) :=
      fun k => hχ.preimage (T.generalLinearDeterminant k).continuous
    let twistSegment : T.Segment.{uV, uF} → T.Segment.{uV, uF} := fun Δ =>
      { base :=
          { rank := Δ.rank
            rank_pos := Δ.rank_pos
            cls := SupercuspidalClass.twist
              (χ.comp (determinant : GeneralLinear Δ.rank F.Carrier →* F.Carrierˣ))
              (hdet Δ.rank) (ker_determinant_le_ker_comp χ) Δ.base.cls }
        length := Δ.length
        length_pos := Δ.length_pos }
    ∀ (n : ℕ), 0 < n →
    ∀ (a : T.Multisegment.{uV, uF})
      (π : SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear n F.Carrier)),
      let aχ : T.Multisegment.{uV, uF} := a.map twistSegment
      let πχ := π.twist (χ.comp (determinant : GeneralLinear n F.Carrier →* F.Carrierˣ))
        (hdet n)
      (a.IsZelevinskySocle π ↔ aχ.IsZelevinskySocle πχ) ∧
        (a.IsLanglandsHead π ↔ aχ.IsLanglandsHead πχ)

/-- Ze80 Theorem 7.10 and Ta86 Proposition 5.6(iii): dualize each segment
`[ρ, ρ']` to `[ρ'ᵛ, ρᵛ]`. Supercuspidal representatives of the end-duals
are asserted to exist, with genuine equivalences to the actual smooth duals.
The resulting multiset is constructed explicitly and works for all candidates.
No duality or compatibility theorem is an input to this proposition. -/
def MultisegmentConstituentContragredientCompatibility : Prop :=
  letI := T.topology
  ∀ (r : ℕ) (Δ : Fin r → T.Segment.{uV, uF})
    (B : ∀ i, SupercuspidalRep.{uF, uV} (F := F.Carrier) (n := (Δ i).rank)),
    (∀ i, (Δ i).last.IsRepresentedBy (B i)) →
    ∃ Bv : ∀ i, SupercuspidalRep.{uF, uV} (F := F.Carrier) (n := (Δ i).rank),
      (∀ i, letI := T.generalLinearTopologicalGroup (Δ i).rank
        Nonempty ((Bv i).obj.representation.Equiv
          (smoothContragredient (B i).obj.representation))) ∧
      let Δv : Fin r → T.Segment.{uV, uF} := fun i =>
        { base :=
            { rank := (Δ i).rank
              rank_pos := (Δ i).rank_pos
              cls := (Bv i).isoClass }
          length := (Δ i).length
          length_pos := (Δ i).length_pos }
      let a : T.Multisegment.{uV, uF} := (List.ofFn Δ : Multiset (T.Segment.{uV, uF}))
      let av : T.Multisegment.{uV, uF} := (List.ofFn Δv : Multiset (T.Segment.{uV, uF}))
      ∀ (n : ℕ), 0 < n →
        letI := T.generalLinearTopologicalGroup n
        ∀ (π : SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear n F.Carrier)),
          let πv := SmoothRep.of (smoothContragredient π.representation)
            (isSmooth_smoothContragredient π.representation)
          (a.IsZelevinskySocle π → av.IsZelevinskySocle πv) ∧
            (a.IsLanglandsHead π → av.IsLanglandsHead πv)

/-- Henniart 2002 §2.8: the actual smooth dual of a square-integrable-form
Langlands head is the irreducible head of the actual normalized induction of
the smooth dual blocks in reverse order. -/
def SquareIntegrableLanglandsHeadContragredientCompatibility : Prop :=
  letI := T.topology
  ∀ (n : ℕ), 0 < n →
    letI := T.generalLinearTopologicalGroup n
    ∀ (d : T.SquareIntegrableLanglandsDatum.{uV, uF} n)
      (π : SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear n F.Carrier)),
      let dualBlocks : ∀ i : Fin d.shape.reverse.length,
          SmoothRep.{0, uF, uV} ℂ (GeneralLinear (d.shape.reverse.size i) F.Carrier) :=
        fun i =>
          letI := T.generalLinearTopologicalGroup (d.shape.size i.rev)
          SmoothRep.of (smoothContragredient (d.blocks i.rev).representation)
            (isSmooth_smoothContragredient (d.blocks i.rev).representation)
      let reversedDualProduct :=
        (T.normalizedProductInductionFunctor d.shape.reverse).obj dualBlocks
      d.IsLanglandsHead π →
        IsIrreducibleHead reversedDualProduct.representation
          (smoothContragredient π.representation)

/-- The central character of either multisegment constituent is the product
of the segment characters, with the full cuspidal-rank and segment-length
factors. This is derived from scalar covariance in BZ77 §1.8 and the published
segment central-character formula; it is not claimed as part of Ta86 §5.6. -/
def MultisegmentConstituentCentralCharacter : Prop :=
  letI := T.topology
  ∀ (r : ℕ) (Δ : Fin r → T.Segment.{uV, uF})
    (A : ∀ i, SupercuspidalRep.{uF, uV} (F := F.Carrier) (n := (Δ i).rank))
    (ω : Fin r → (F.Carrierˣ →* ℂˣ)),
    (∀ i, (Δ i).base.IsRepresentedBy (A i)) →
    (∀ i, HasScalarCharacter (A i).obj.representation GeneralLinear.scalar (ω i)) →
    let ωΔ : Fin r → (F.Carrierˣ →* ℂˣ) := fun i =>
      ω i ^ (Δ i).length *
        (T.determinantPowerCharacter (Δ i).degree ((((Δ i).length : ℝ) - 1) / 2)).comp
          GeneralLinear.scalar
    let a : T.Multisegment.{uV, uF} := (List.ofFn Δ : Multiset (T.Segment.{uV, uF}))
    ∀ (n : ℕ), 0 < n →
    ∀ (π : SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear n F.Carrier)),
      (a.IsZelevinskySocle π ∨ a.IsLanglandsHead π) →
        HasScalarCharacter π.representation GeneralLinear.scalar (∏ i, ωΔ i)

/-- The five focused multisegment and Langlands-head compatibility assertions
for a fixed p-adic field realization. -/
def MultisegmentConstituentCompatibilityTheorems : Prop :=
  MultisegmentConstituentRealTwistCompatibility.{uF, uV} F T ∧
    MultisegmentConstituentCharacterTwistCompatibility.{uF, uV} F T ∧
    MultisegmentConstituentContragredientCompatibility.{uF, uV} F T ∧
    SquareIntegrableLanglandsHeadContragredientCompatibility.{uF, uV} F T ∧
    MultisegmentConstituentCentralCharacter.{uF, uV} F T

/-- The compatibility family over every prime, finite p-adic extension and
compatible topological realization, with both field and carrier universes
explicit. These are statements, not proofs or assumed classification data. -/
def PadicMultisegmentConstituentCompatibilityTheorems : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData),
    MultisegmentConstituentCompatibilityTheorems.{uF, uV} F T

end Langlands.Classification
