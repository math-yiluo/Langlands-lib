import Langlands.Representation.Classification.Segments
import Langlands.Representation.Classification.Tempered

/-!
# Special representations and square-integrability for GL_n

Bernstein's theorem (Ze80 §9.3) characterizes the essentially square-integrable
irreducibles as the special heads of segments. The centered normalization,
unitarity criterion, parameter uniqueness and unique real exponent are recorded
as separate proposition definitions. No classification theorem is assumed.
-/

namespace Langlands.Classification

open CategoryTheory GeneralLinear

universe uF uV

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData)

/-- The special irreducible quotient of every segment product is essentially
square-integrable (Ze80 §9.3, construction direction). -/
def SegmentSpecialEssentialSquareIntegrability : Prop :=
  letI := T.topology
  ∀ (Δ : T.Segment.{max uF uV, uF})
    (π : SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear Δ.degree F.Carrier)),
    T.IsSegmentQuotient Δ π → T.IsEssentiallySquareIntegrable π.representation

/-- Bernstein's theorem, Ze80 §9.3: an irreducible positive-rank representation
is essentially square-integrable iff it is the head attached to some segment.
The degree equality transports the same representation to the segment rank. -/
def SegmentEssentialSquareIntegrableClassification : Prop :=
  letI := T.topology
  ∀ (n : ℕ), 0 < n →
    ∀ π : SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear n F.Carrier),
      Representation.IsIrreducible π.representation →
        (T.IsEssentiallySquareIntegrable π.representation ↔
          ∃ (Δ : T.Segment.{max uF uV, uF}) (h : Δ.degree = n),
            T.IsSegmentHead Δ (h.symm ▸ π))

/-- The segment parameter of a special representation is unique, as in
Henniart 2002 §2.6. Segment equality includes the actual cuspidal isomorphism
class and its rank, as well as the positive length. -/
def SegmentSpecialParameterUniqueness : Prop :=
  letI := T.topology
  ∀ (Δ Δ' : T.Segment.{max uF uV, uF}) (h : Δ.degree = Δ'.degree)
    (π : SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear Δ.degree F.Carrier))
    (π' : SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear Δ'.degree F.Carrier)),
    T.IsSegmentHead Δ π → T.IsSegmentHead Δ' π' →
      Nonempty ((h ▸ π) ≅ π') → Δ = Δ'

/-- Among special representations, square-integrability, a unitary scalar
central character and unitarizability agree. The first equivalence uses removal
of real norm twists; the second also uses Casselman 1995 Proposition 2.5.4. -/
def SegmentSpecialSquareIntegrabilityCriterion : Prop :=
  letI := T.topology
  ∀ (Δ : T.Segment.{max uF uV, uF})
    (π : SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear Δ.degree F.Carrier)),
    T.IsSegmentQuotient Δ π →
      (T.IsSquareIntegrable π.representation ↔
        Nonempty (UnitaryCentralCharacter π.representation)) ∧
      (T.IsSquareIntegrable π.representation ↔ IsUnitarizable π.representation)

/-- For a segment beginning at a unitarizable supercuspidal representation,
twisting its special quotient by `ν^(-(m-1)/2)` is square-integrable and
unitarizable. The increasing segment itself remains uncentered. -/
def SegmentCenteredSpecialSquareIntegrability : Prop :=
  letI := T.topology
  ∀ (Δ : T.Segment.{max uF uV, uF})
    (A : SupercuspidalRep.{uF, max uF uV} (F := F.Carrier) (n := Δ.rank)),
    Δ.base.IsRepresentedBy A → IsUnitarizable A.obj.representation →
      ∀ π : SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear Δ.degree F.Carrier),
        T.IsSegmentQuotient Δ π →
          let ρ₀ := realPowerTwist (T.determinantNorm Δ.degree)
            (-(((Δ.length : ℝ) - 1) / 2)) π.representation
          T.IsSquareIntegrable ρ₀ ∧ IsUnitarizable ρ₀

/-- An irreducible essentially square-integrable representation has a unique
real square-integrability exponent. Positivity of the rank excludes the
rank-zero character, on which real determinant twists would all be trivial. -/
def EssentialSquareIntegrabilityExponentUniqueness : Prop :=
  letI := T.topology
  ∀ (n : ℕ), 0 < n →
    ∀ π : SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear n F.Carrier),
      Representation.IsIrreducible π.representation →
        T.IsEssentiallySquareIntegrable π.representation →
          ∃! s : ℝ, T.IsSquareIntegrable
            (realPowerTwist (T.determinantNorm n) (-s) π.representation)

/-- The special-square-integrability statements for one p-adic field. -/
def SegmentSquareIntegrabilityTheorems : Prop :=
  SegmentSpecialEssentialSquareIntegrability.{uF, uV} F T ∧
    SegmentEssentialSquareIntegrableClassification.{uF, uV} F T ∧
    SegmentSpecialParameterUniqueness.{uF, uV} F T ∧
    SegmentSpecialSquareIntegrabilityCriterion.{uF, uV} F T ∧
    SegmentCenteredSpecialSquareIntegrability.{uF, uV} F T ∧
    EssentialSquareIntegrabilityExponentUniqueness.{uF, uV} F T

/-- The family for every prime, finite p-adic extension and compatible topology. -/
def PadicSegmentSquareIntegrabilityTheorems : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData),
    SegmentSquareIntegrabilityTheorems.{uF, uV} F T

end Langlands.Classification
