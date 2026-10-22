import Langlands.Representation.Classification.LanglandsData
import Langlands.Representation.Whittaker.GeneralLinear

/-!
# Tempered block induction and classification for GL_n

Analytic square-integrability and temperedness, invariant positive forms, actual
normalized upper parabolic induction, and nonzero Whittaker functionals are used
throughout. These proposition definitions assert no classification theorem.
-/

namespace Langlands.Classification

open CategoryTheory GeneralLinear HarmonicAnalysis

universe uF uV

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData)

/-- Normalized induction of irreducible square-integrable unitary GL blocks is
irreducible, unitarizable and analytically tempered. -/
def SquareIntegrableBlockInduction : Prop :=
  letI := T.topology
  ∀ (n : ℕ), 0 < n → ∀ (B : BlockShape n)
    (σ : ∀ i, SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear (B.size i) F.Carrier)),
    (∀ i, Representation.IsIrreducible (σ i).representation ∧
      T.IsSquareIntegrable (σ i).representation ∧ IsUnitarizable (σ i).representation) →
    let I := (T.normalizedProductInductionFunctor B).obj σ
    Representation.IsIrreducible I.representation ∧
      IsUnitarizable I.representation ∧ T.IsTempered I.representation

/-- The same normalized product has an actual nonzero standard Whittaker
functional for every continuous nontrivial unitary additive character. -/
def SquareIntegrableBlockGenericity : Prop :=
  letI := T.topology
  ∀ (n : ℕ) (B : BlockShape (n + 1))
    (σ : ∀ i, SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear (B.size i) F.Carrier)),
    (∀ i, Representation.IsIrreducible (σ i).representation ∧
      T.IsSquareIntegrable (σ i).representation ∧ IsUnitarizable (σ i).representation) →
    ∀ ψ : UnitaryAdditiveCharacter F.Carrier,
      Whittaker.IsGeneric ψ n
        ((T.normalizedProductInductionFunctor B).obj σ).representation

/-- Every irreducible analytically tempered positive-rank representation is
isomorphic to a normalized product of square-integrable unitary blocks. -/
def TemperedBlockExhaustion : Prop :=
  letI := T.topology
  ∀ (n : ℕ), 0 < n →
    ∀ π : SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear n F.Carrier),
      Representation.IsIrreducible π.representation → T.IsTempered π.representation →
        ∃ (B : BlockShape n)
          (σ : ∀ i, SmoothRep.{0, uF, max uF uV} ℂ
            (GeneralLinear (B.size i) F.Carrier)),
          (∀ i, Representation.IsIrreducible (σ i).representation ∧
            T.IsSquareIntegrable (σ i).representation ∧
              IsUnitarizable (σ i).representation) ∧
          Nonempty (π ≅ (T.normalizedProductInductionFunctor B).obj σ)

/-- Two such products are isomorphic exactly when their blocks match by a
permutation, equality of ranks, and actual isomorphisms after rank transport.
The reverse implication includes independence of the ordering. -/
def TemperedBlockUniqueness : Prop :=
  letI := T.topology
  ∀ (n : ℕ), 0 < n → ∀ (B C : BlockShape n)
    (σ : ∀ i, SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear (B.size i) F.Carrier))
    (τ : ∀ j, SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear (C.size j) F.Carrier)),
    (∀ i, Representation.IsIrreducible (σ i).representation ∧
      T.IsSquareIntegrable (σ i).representation ∧ IsUnitarizable (σ i).representation) →
    (∀ j, Representation.IsIrreducible (τ j).representation ∧
      T.IsSquareIntegrable (τ j).representation ∧ IsUnitarizable (τ j).representation) →
    (Nonempty ((T.normalizedProductInductionFunctor B).obj σ ≅
        (T.normalizedProductInductionFunctor C).obj τ) ↔
      ∃ (e : Fin B.length ≃ Fin C.length) (h : ∀ i, B.size i = C.size (e i)),
        ∀ i, Nonempty ((h i ▸ σ i) ≅ τ (e i)))

/-- The GL_n-specific consequence: products of irreducible tempered blocks
are irreducible, unitarizable and tempered. -/
def TemperedBlockInduction : Prop :=
  letI := T.topology
  ∀ (n : ℕ), 0 < n → ∀ (B : BlockShape n)
    (σ : ∀ i, SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear (B.size i) F.Carrier)),
    (∀ i, Representation.IsIrreducible (σ i).representation ∧
      T.IsTempered (σ i).representation) →
    let I := (T.normalizedProductInductionFunctor B).obj σ
    Representation.IsIrreducible I.representation ∧
      IsUnitarizable I.representation ∧ T.IsTempered I.representation

/-- Irreducible tempered GL representations admit invariant positive forms and
nonzero standard Whittaker functionals. -/
def TemperedUnitarityAndGenericity : Prop :=
  letI := T.topology
  ∀ (n : ℕ) (π : SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear (n + 1) F.Carrier)),
    Representation.IsIrreducible π.representation → T.IsTempered π.representation →
      IsUnitarizable π.representation ∧
        ∀ ψ : UnitaryAdditiveCharacter F.Carrier, Whittaker.IsGeneric ψ n π.representation

/-- Group maximal consecutive equal-exponent runs of square-integrable Langlands
data. Fiber bijections and rank transports identify every new block with the
actual normalized product of the old unitarily normalized blocks. -/
def SquareIntegrableEqualExponentGrouping : Prop :=
  letI := T.topology
  ∀ (n : ℕ), 0 < n →
    ∀ d : T.SquareIntegrableLanglandsDatum.{max uF uV, uF} n,
      (∀ i, T.IsSquareIntegrable
        (T.segmentFactor (d.blocks i) (-d.exponent i)).representation) ∧
      ∃ (t : T.TemperedLanglandsDatum.{max uF uV, uF} n)
        (q : Fin d.shape.length → Fin t.shape.length),
        Monotone q ∧ Function.Surjective q ∧
        (∀ i, d.exponent i = t.exponent (q i)) ∧
        (∀ j, ∃ (C : BlockShape (t.shape.size j))
          (e : Fin C.length ≃ {i : Fin d.shape.length // q i = j})
          (h : ∀ k, C.size k = d.shape.size (e k).val),
          StrictMono (fun k => (e k).val) ∧
          Nonempty ((T.normalizedProductInductionFunctor C).obj
            (fun k => (h k).symm ▸ T.segmentFactor (d.blocks (e k).val)
              (-d.exponent (e k).val)) ≅ t.blocks j)) ∧
        Nonempty (d.induced ≅ t.standardModule)

/-- The focused GL_n tempered block statement family for one p-adic field. -/
def TemperedBlockTheorems : Prop :=
  SquareIntegrableBlockInduction.{uF, uV} F T ∧
    SquareIntegrableBlockGenericity.{uF, uV} F T ∧
    TemperedBlockExhaustion.{uF, uV} F T ∧
    TemperedBlockUniqueness.{uF, uV} F T ∧
    TemperedBlockInduction.{uF, uV} F T ∧
    TemperedUnitarityAndGenericity.{uF, uV} F T ∧
    SquareIntegrableEqualExponentGrouping.{uF, uV} F T

/-- The statements for every prime, finite p-adic extension and compatible
topological realization, in arbitrary carrier universes. -/
def PadicTemperedBlockTheorems : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData),
    TemperedBlockTheorems.{uF, uV} F T

end Langlands.Classification
