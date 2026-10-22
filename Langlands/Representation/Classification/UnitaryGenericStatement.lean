import Langlands.Representation.Classification.LanglandsData
import Langlands.Representation.Whittaker.GeneralLinear

/-!
# Unitary generic classification for GL_n

Strict complementary-series bounds, Hermitian symmetry of the unitary blocks,
and unordered uniqueness are stated using actual smooth representations and
normalized upper induction. The declarations below are proposition definitions,
not proofs or assumed classification constructors.
-/

namespace Langlands.Classification

open CategoryTheory GeneralLinear HarmonicAnalysis

universe uF uV

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData)

/-- Every block is an actual irreducible unitarizable square-integrable
representation. Unitarizability uses an invariant positive Hermitian form. -/
def IsUnitarySquareIntegrableBlockFamily {n : ℕ} (B : BlockShape n)
    (δ : letI := T.topology
      ∀ i, SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear (B.size i) F.Carrier)) : Prop :=
  letI := T.topology
  ∀ i, Representation.IsIrreducible (δ i).representation ∧
    IsUnitarizable (δ i).representation ∧ T.IsSquareIntegrable (δ i).representation

/-- The open complementary-series interval; neither endpoint is allowed. -/
def HasStrictUnitaryExponents {r : ℕ} (s : Fin r → ℝ) : Prop :=
  ∀ i, -(1 / 2 : ℝ) < s i ∧ s i < (1 / 2 : ℝ)

/-- Equality of finite unordered parameter families with multiplicities:
matched ranks and real exponents agree and matched blocks are isomorphic after
transport along the rank equality. -/
def SameUnorderedUnitaryParameters {n : ℕ} (B C : BlockShape n)
    (δ : letI := T.topology
      ∀ i, SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear (B.size i) F.Carrier))
    (ε : letI := T.topology
      ∀ j, SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear (C.size j) F.Carrier))
    (s : Fin B.length → ℝ) (t : Fin C.length → ℝ) : Prop :=
  letI := T.topology
  ∃ (e : Fin B.length ≃ Fin C.length) (h : ∀ i, B.size i = C.size (e i)),
    ∀ i, s i = t (e i) ∧ Nonempty ((h i ▸ δ i) ≅ ε (e i))

/-- The multiset of `(s, δ)` is stable under `(s, δ) ↦ (-s, δ)`.
This is Hermitian parameter symmetry, not ordinary self-contragredience of δ. -/
def HasHermitianSymmetricParameters {n : ℕ} (B : BlockShape n)
    (δ : letI := T.topology
      ∀ i, SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear (B.size i) F.Carrier))
    (s : Fin B.length → ℝ) : Prop :=
  SameUnorderedUnitaryParameters F T B B δ δ s (fun i => -s i)

/-- Valid unitary generic construction parameters. Positive block ranks and
summation to the total rank are carried by `B`. -/
def IsUnitaryGenericDatum {n : ℕ} (B : BlockShape n)
    (δ : letI := T.topology
      ∀ i, SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear (B.size i) F.Carrier))
    (s : Fin B.length → ℝ) : Prop :=
  IsUnitarySquareIntegrableBlockFamily F T B δ ∧
    HasStrictUnitaryExponents s ∧ HasHermitianSymmetricParameters F T B δ s

/-- Every valid family induces an irreducible admissible unitarizable generic
representation, for every nontrivial continuous unitary additive character. -/
def UnitaryGenericConstruction : Prop :=
  letI := T.topology
  ∀ (n : ℕ) (B : BlockShape (n + 1))
    (δ : ∀ i, SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear (B.size i) F.Carrier))
    (s : Fin B.length → ℝ),
    IsUnitaryGenericDatum F T B δ s →
      IsUnitarizable (T.twistedProductInduced B δ s).representation ∧
        ∀ ψ : UnitaryAdditiveCharacter F.Carrier,
          Whittaker.IsGeneric ψ n (T.twistedProductInduced B δ s).representation

/-- Every unitary generic representation of positive rank is isomorphic to the
actual normalized induction of a valid family of unitary square-integrable blocks. -/
def UnitaryGenericExhaustion : Prop :=
  letI := T.topology
  ∀ (n : ℕ) (ψ : UnitaryAdditiveCharacter F.Carrier)
    (π : SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear (n + 1) F.Carrier)),
    Whittaker.IsGeneric ψ n π.representation → IsUnitarizable π.representation →
      ∃ (B : BlockShape (n + 1))
        (δ : ∀ i, SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear (B.size i) F.Carrier))
        (s : Fin B.length → ℝ),
        IsUnitaryGenericDatum F T B δ s ∧
          Nonempty (π ≅ T.twistedProductInduced B δ s)

/-- Two valid inductions are isomorphic exactly when their parameter families
match up to a rank-preserving bijection and actual block isomorphisms.
The reverse implication also states independence of the ordering. -/
def UnitaryGenericParameterUniqueness : Prop :=
  letI := T.topology
  ∀ (n : ℕ) (B C : BlockShape (n + 1))
    (δ : ∀ i, SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear (B.size i) F.Carrier))
    (ε : ∀ j, SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear (C.size j) F.Carrier))
    (s : Fin B.length → ℝ) (t : Fin C.length → ℝ),
    IsUnitaryGenericDatum F T B δ s → IsUnitaryGenericDatum F T C ε t →
      (Nonempty (T.twistedProductInduced B δ s ≅ T.twistedProductInduced C ε t) ↔
        SameUnorderedUnitaryParameters F T B C δ ε s t)

/-- Both classification directions and genuine unordered uniqueness for a
fixed p-adic field with its compatible topology. -/
def UnitaryGenericTheorems : Prop :=
  UnitaryGenericConstruction.{uF, uV} F T ∧
    UnitaryGenericExhaustion.{uF, uV} F T ∧
    UnitaryGenericParameterUniqueness.{uF, uV} F T

/-- The unitary generic classification for every finite p-adic extension,
with arbitrary field and representation carrier universes. -/
def PadicUnitaryGenericTheorems : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData),
    UnitaryGenericTheorems.{uF, uV} F T

end Langlands.Classification
