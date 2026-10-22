import Langlands.Group.GL.BlockModulus
import Langlands.Representation.Induction.Definitions
import Langlands.Representation.Parabolic.LeviBridges

namespace Langlands.Parabolic

universe uF uV

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)
    (T : F.TopologicalData) {n : ℕ} (B : GeneralLinear.BlockShape n)
    (V : Type uV) [AddCommGroup V] [Module ℂ V]

/-- Every scalar character of the actual ambient GL group kills the block
unipotent radical. This is an algebraic assertion, not an input assumption. -/
def AmbientCharacterRadicalClause : Prop :=
  ∀ χ : GeneralLinear n F.Carrier →* ℂˣ,
    ∀ u : B.unipotentRadical F.Carrier,
      χ ((B.parabolic F.Carrier).subtype u.val) = 1

/-- Normalized induction commutes with every smooth ambient scalar character;
the equivalence is prescribed by multiplying functions by that character. -/
def NormalizedInductionTwistClause : Prop :=
  letI := T.topology
  letI := T.generalLinearTopologicalGroup n
  ∀ (χ : Induction.SmoothCharacter ℂ (GeneralLinear n F.Carrier))
    (σ : Representation ℂ (B.Levi F.Carrier) V),
    IsSmooth σ →
    let χM := χ.toMonoidHom.comp (B.leviEmbedding F.Carrier)
    ∃ E : Representation.Equiv
      (twist χ.toMonoidHom (Induction.smoothInduced (B.parabolic F.Carrier)
        (twist (T.parabolicHalfModulus B) (inflate B σ))))
      (Induction.smoothInduced (B.parabolic F.Carrier)
        (twist (T.parabolicHalfModulus B) (inflate B (twist χM σ)))),
      ∀ f g,
        Induction.eval (B.parabolic F.Carrier)
          (twist (T.parabolicHalfModulus B) (inflate B (twist χM σ))) (E f) g =
        (χ.toMonoidHom g : ℂ) •
          Induction.eval (B.parabolic F.Carrier)
            (twist (T.parabolicHalfModulus B) (inflate B σ)) f g

/-- Normalized Jacquet commutes with ambient scalar twisting; the equivalence
sends each actual quotient class to the class of the same vector. -/
def NormalizedJacquetTwistClause : Prop :=
  letI := T.topology
  ∀ (χ : Induction.SmoothCharacter ℂ (GeneralLinear n F.Carrier))
    (ρ : Representation ℂ (GeneralLinear n F.Carrier) V),
    IsSmooth ρ →
    let χM := χ.toMonoidHom.comp (B.leviEmbedding F.Carrier)
    ∃ E : Representation.Equiv
      (twist (Jacquet.inverseHalfCharacter (T.leviModulus B))
        (leviCoinvariants B
          ((twist χ.toMonoidHom ρ).comp (B.parabolic F.Carrier).subtype)))
      (twist χM (twist (Jacquet.inverseHalfCharacter (T.leviModulus B))
        (leviCoinvariants B (ρ.comp (B.parabolic F.Carrier).subtype)))),
      ∀ v,
        E (Jacquet.mk ((twist χ.toMonoidHom ρ).comp (B.parabolic F.Carrier).subtype)
          (B.unipotentRadical F.Carrier) v) =
        Jacquet.mk (ρ.comp (B.parabolic F.Carrier).subtype)
          (B.unipotentRadical F.Carrier) v

/-- A scalar central character on the product Levi passes unchanged to
normalized induction; the genuine half-modulus cancels on ambient scalars. -/
def NormalizedInductionCentralClause : Prop :=
  letI := T.topology
  letI := T.generalLinearTopologicalGroup n
  ∀ (σ : Representation ℂ (B.Levi F.Carrier) V) (ω : F.Carrierˣ →* ℂˣ),
    (∀ (a : F.Carrierˣ) (v : V),
      σ (fun i => GeneralLinear.scalar (n := B.size i) a) v = (ω a : ℂ) • v) →
    ∀ (a : F.Carrierˣ) f,
      Induction.smoothInduced (B.parabolic F.Carrier)
        (twist (T.parabolicHalfModulus B) (inflate B σ))
        (GeneralLinear.scalar (n := n) a) f = (ω a : ℂ) • f

/-- An ambient scalar central character descends unchanged to the normalized
product-Levi Jacquet quotient. -/
def NormalizedJacquetCentralClause : Prop :=
  letI := T.topology
  ∀ (ρ : Representation ℂ (GeneralLinear n F.Carrier) V) (ω : F.Carrierˣ →* ℂˣ),
    (∀ (a : F.Carrierˣ) (v : V),
      ρ (GeneralLinear.scalar (n := n) a) v = (ω a : ℂ) • v) →
    ∀ (a : F.Carrierˣ)
      (v : LeviCoinvariants B (ρ.comp (B.parabolic F.Carrier).subtype)),
      twist (Jacquet.inverseHalfCharacter (T.leviModulus B))
        (leviCoinvariants B (ρ.comp (B.parabolic F.Carrier).subtype))
        (fun i => GeneralLinear.scalar (n := B.size i) a) v = (ω a : ℂ) • v

/-- Actual normalized scalar-twist and scalar-central-character compatibility,
including the ambient radical-triviality prerequisite as a conclusion. -/
def NormalizedCompatibilityStatement : Prop :=
  AmbientCharacterRadicalClause F B ∧
  NormalizedInductionTwistClause F T B V ∧
  NormalizedJacquetTwistClause F T B V ∧
  NormalizedInductionCentralClause F T B V ∧
  NormalizedJacquetCentralClause F T B V

end Langlands.Parabolic
