import Langlands.Weil.Local.ParameterOperations
import Langlands.LocalFactor.WeilDeligne
import Langlands.WeilDeligne.DirectSum

/-!
# Pole regions of Weil–Deligne L-polynomials

The Weil-group half of Henniart 1986, Proposition 4.5(i), on the actual local
Weil group of a p-adic field and its actual Weil–Deligne parameters.
-/

noncomputable section

universe u v w

namespace Langlands.Global

open Langlands.Weil.Local

namespace WeilPoleRegion

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{u} p)

/-- The residue cardinality `q` of the canonical realization of `F`. -/
abbrev residueCardinality : ℕ :=
  F.canonicalTopologicalData.residueCardinality

/-- The L-polynomial `P_σ(X) = det(1 - X Φ | (ker N)^I)` at the chosen geometric
Frobenius `Φ`, so that `L(σ, s) = P_σ(q^(-s))⁻¹`. -/
def lPolynomial (σ : LocalParameterObjects.{u, v} F) : Polynomial ℂ :=
  LocalFactor.WeilDeligne.eulerPolynomial σ.val (localInertia F) (localGeometricFrobenius F)

/-- `P` and the reflected polynomial `Pdual(q⁻¹ X⁻¹)` have no common nonzero zero. -/
def HasNoReflectedCommonZero (P Pdual : Polynomial ℂ) : Prop :=
  ∀ z : ℂ, z ≠ 0 →
    ¬ (P.eval z = 0 ∧ Pdual.eval ((residueCardinality F : ℂ)⁻¹ * z⁻¹) = 0)

/-- Essential unitarity: some continuous character twists the representation
into a unitarizable one. -/
def IsEssentiallyUnitary (A : LocalOpenInertiaWeilObjects.{u, v} F) : Prop :=
  ∃ χ : localWeilGroup F →ₜ* ℂˣ,
    (FiniteRepresentation.twist χ.toMonoidHom A.val).IsUnitary

/-- The blocks `ρ ⊗ Sp(m)` and `ρ' ⊗ Sp(m')` are juxtaposed when
`ρ' ≅ ν^m ρ` or `ρ ≅ ν^m' ρ'`, for the actual norm character `ν`. -/
def AreJuxtaposed (ρ : LocalOpenInertiaWeilObjects.{u, v} F) (m : ℕ)
    (ρ' : LocalOpenInertiaWeilObjects.{u, v} F) (m' : ℕ) : Prop :=
  FiniteRepresentation.IsIsomorphic ρ'.val
      (FiniteRepresentation.twist ((localNormCharacter F).toMonoidHom ^ m) ρ.val) ∨
    FiniteRepresentation.IsIsomorphic ρ.val
      (FiniteRepresentation.twist ((localNormCharacter F).toMonoidHom ^ m') ρ'.val)

end WeilPoleRegion

open WeilPoleRegion

/-- Henniart 1986, Proposition 4.5(i), first case, for zero monodromy: if `σ` and `σ'`
are essentially unitary, then `P_{σ ⊗ σ'}` and the reflected `P_{σ^∨ ⊗ σ'^∨}`
have no common zero. -/
def EssentiallyUnitaryPoleRegionStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{u} p)
    (A : LocalOpenInertiaWeilObjects.{u, v} F) (B : LocalOpenInertiaWeilObjects.{u, w} F),
    IsEssentiallyUnitary F A → IsEssentiallyUnitary F B →
    let σ := localZeroMonodromyParameter F A
    let σ' := localZeroMonodromyParameter F B
    HasNoReflectedCommonZero F
      (lPolynomial F (localParameterTensor F σ σ'))
      (lPolynomial F (localParameterTensor F (localParameterDual F σ) (localParameterDual F σ')))

/-- Henniart 1986, Proposition 4.5(i), second case: if `σ'` is irreducible and `σ` is a
sum of blocks `ρ_i ⊗ Sp(n_i)`, with `ρ_i` irreducible and `n_i ≥ 1`, no two of which are
juxtaposed, then `P_{σ ⊗ σ'}` and the reflected `P_{σ^∨ ⊗ σ'^∨}` have no common zero. -/
def NonJuxtaposedPoleRegionStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{u} p) (k : ℕ)
    (ρ : Fin k → LocalOpenInertiaWeilObjects.{u, v} F) (n : Fin k → ℕ),
    (∀ i, (ρ i).val.IsIrreducible) → (∀ i, 0 < n i) →
    (∀ i j, i ≠ j → ¬ AreJuxtaposed F (ρ i) (n i) (ρ j) (n j)) →
    ∀ σ : LocalParameterObjects.{u, v} F,
    Nonempty (WeilDeligneRepresentation.Equiv σ.val
      (WeilDeligneRepresentation.directSum fun i => (localBlock F (ρ i) (n i)).val)) →
    ∀ B : LocalOpenInertiaWeilObjects.{u, w} F, B.val.IsIrreducible →
    let σ' := localZeroMonodromyParameter F B
    HasNoReflectedCommonZero F
      (lPolynomial F (localParameterTensor F σ σ'))
      (lPolynomial F (localParameterTensor F (localParameterDual F σ) (localParameterDual F σ')))

/-- The Weil-side pole-region hypotheses of Henniart 1986, Proposition 4.5(i). -/
def WeilPairPoleRegionStatement : Prop :=
  EssentiallyUnitaryPoleRegionStatement.{u, v, w} ∧ NonJuxtaposedPoleRegionStatement.{u, v, w}

end Langlands.Global
