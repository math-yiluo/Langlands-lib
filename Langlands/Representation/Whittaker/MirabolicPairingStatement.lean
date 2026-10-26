import Langlands.Representation.Whittaker.MirabolicModels
import Langlands.Representation.Filtration.InvariantBilinear
import Langlands.Representation.RankinSelberg.AnalyticStatement

/-!
# Irreducible mirabolic functionals and twisted pairings

Proposition targets for the consequences of JPSS (1983), Proposition 1.4 and
Section 1.5, used in Section 2.10. No classification or proof is asserted here.
-/

noncomputable section

namespace Langlands.Whittaker

open GeneralLinear HarmonicAnalysis RankinSelberg

universe uF uV uW

/-- JPSS Section 1.5, Corollary 1: scalar uniqueness of the full character
functional space, recognition of the compact standard representation by a
linear equivalence with `ℂ`, and vanishing for every other irreducible. -/
def MirabolicFunctionalMultiplicityStatement {p : ℕ} [Fact p.Prime]
    (F : PadicField.{uF} p) (T : F.TopologicalData) (n : ℕ) : Prop :=
  letI := T.topology
  letI : IsTopologicalRing F.Carrier := by
    let := T.valuativeRel
    let := T.localField
    infer_instance
  ∀ ψ : UnitaryAdditiveCharacter F.Carrier,
    ∀ (V : Type uV) [AddCommGroup V] [Module ℂ V],
    ∀ ξ : Representation ℂ (mirabolic n F.Carrier) V,
      IsSmooth ξ → Representation.IsIrreducible ξ →
      let L := functionals (Mirabolic.upperUnipotent n F.Carrier)
        (mirabolicCharacter ψ n) ξ
      let τ := mirabolicCompactInduced ψ n
      (∀ ℓ ℓ' : L, ℓ ≠ 0 → ∃ c : ℂ, ℓ' = c • ℓ) ∧
      (Nonempty (L ≃ₗ[ℂ] ℂ) ↔ Nonempty (ξ.Equiv τ)) ∧
      (¬ Nonempty (ξ.Equiv τ) → ∀ ℓ : L, ℓ = 0)

/-- JPSS Section 1.5, Corollary 2: outside finitely many spectral values,
a nonzero twisted bilinear form on two irreducible smooth mirabolic
representations forces both to be equivalent to the actual compact model. -/
def MirabolicTwistedPairingRigidityStatement {p : ℕ} [Fact p.Prime]
    (F : PadicField.{uF} p) (T : F.TopologicalData) (n : ℕ) : Prop :=
  letI := T.topology
  letI : IsTopologicalRing F.Carrier := by
    let := T.valuativeRel
    let := T.localField
    infer_instance
  ∀ ψ : UnitaryAdditiveCharacter F.Carrier,
    ∀ (V : Type uV) [AddCommGroup V] [Module ℂ V],
    ∀ (W : Type uW) [AddCommGroup W] [Module ℂ W],
    ∀ (ξ : Representation ℂ (mirabolic n F.Carrier) V)
      (ξ' : Representation ℂ (mirabolic n F.Carrier) W),
      IsSmooth ξ → Representation.IsIrreducible ξ →
      IsSmooth ξ' → Representation.IsIrreducible ξ' →
      ∃ E : Finset ℂ, ∀ s : ℂ, spectralPoint T.residueCardinality s ∉ E →
        ∀ β : InvariantBilinear.forms ξ ξ'
          (fun g => determinantWeight (normalizedAbsoluteValue T) g.val (-s)),
          β ≠ 0 →
            Nonempty (ξ.Equiv (mirabolicCompactInduced ψ n)) ∧
            Nonempty (ξ'.Equiv (mirabolicCompactInduced ψ n))

/-- The compact standard representation paired with itself has a nonzero,
exactly one-dimensional twisted form space for every exponent, as used in
JPSS Section 2.10, printed p.398. -/
def MirabolicCompactTwistedPairingStatement {p : ℕ} [Fact p.Prime]
    (F : PadicField.{uF} p) (T : F.TopologicalData) (n : ℕ) : Prop :=
  letI := T.topology
  letI : IsTopologicalRing F.Carrier := by
    let := T.valuativeRel
    let := T.localField
    infer_instance
  ∀ (ψ : UnitaryAdditiveCharacter F.Carrier) (s : ℂ),
    Nonempty ((InvariantBilinear.forms
      (mirabolicCompactInduced ψ n) (mirabolicCompactInduced ψ n)
      (fun g => determinantWeight (normalizedAbsoluteValue T) g.val (-s))) ≃ₗ[ℂ] ℂ)

/-- The three irreducible-mirabolic inputs to the minimal-pair argument of
JPSS Section 2.10, retaining independent field and representation universes. -/
def MirabolicPairingStatement {p : ℕ} [Fact p.Prime]
    (F : PadicField.{uF} p) (T : F.TopologicalData) (n : ℕ) : Prop :=
  MirabolicFunctionalMultiplicityStatement.{uF, uV} F T n ∧
  MirabolicTwistedPairingRigidityStatement.{uF, uV, uW} F T n ∧
  MirabolicCompactTwistedPairingStatement.{uF} F T n

end Langlands.Whittaker
