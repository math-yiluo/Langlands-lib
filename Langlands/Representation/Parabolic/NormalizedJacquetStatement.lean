import Langlands.Group.GL.BlockModulus
import Langlands.Representation.Induction.Definitions
import Langlands.Representation.Parabolic.LeviBridges

namespace Langlands.Parabolic

universe uF uU uV uW

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)
    (T : F.TopologicalData) {n : ℕ} (B : GeneralLinear.BlockShape n)
    (U : Type uU) (V : Type uV) (W : Type uW)
    [AddCommGroup U] [Module ℂ U] [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W]

/-- The actual normalized product-Levi Jacquet action is smooth on smooth input. -/
def NormalizedJacquetSmoothnessClause : Prop :=
  letI := T.topology
  ∀ ρ : Representation ℂ (GeneralLinear n F.Carrier) V,
    IsSmooth ρ →
    IsSmooth (twist (Jacquet.inverseHalfCharacter (T.leviModulus B))
      (leviCoinvariants B (ρ.comp (B.parabolic F.Carrier).subtype)))

/-- Admissibility for the actual radical quotient with inverse block half-modulus. -/
def NormalizedJacquetAdmissibilityClause : Prop :=
  letI := T.topology
  ∀ ρ : Representation ℂ (GeneralLinear n F.Carrier) V,
    IsAdmissible ρ →
    IsAdmissible (twist (Jacquet.inverseHalfCharacter (T.leviModulus B))
      (leviCoinvariants B (ρ.comp (B.parabolic F.Carrier).subtype)))

/-- The normalized quotient intertwiners preserve all three parts of a short
exact sequence of smooth ambient representations. -/
def NormalizedJacquetExactnessClause : Prop :=
  letI := T.topology
  ∀ (ρ : Representation ℂ (GeneralLinear n F.Carrier) U)
    (σ : Representation ℂ (GeneralLinear n F.Carrier) V)
    (τ : Representation ℂ (GeneralLinear n F.Carrier) W)
    (i : ρ.IntertwiningMap σ) (q : σ.IntertwiningMap τ),
    IsSmooth ρ → IsSmooth σ → IsSmooth τ →
    Function.Injective i → Function.Surjective q →
    LinearMap.range i.toLinearMap = LinearMap.ker q.toLinearMap →
    let iN := twistIntertwining (Jacquet.inverseHalfCharacter (T.leviModulus B))
      (leviCoinvariantsMap B (Jacquet.restrictMap i (B.parabolic F.Carrier)))
    let qN := twistIntertwining (Jacquet.inverseHalfCharacter (T.leviModulus B))
      (leviCoinvariantsMap B (Jacquet.restrictMap q (B.parabolic F.Carrier)))
    Function.Injective iN ∧
      LinearMap.range iN.toLinearMap = LinearMap.ker qN.toLinearMap ∧
      Function.Surjective qN

/-- Evaluation at one gives first adjointness with the genuine positive
induction half and inverse Jacquet half. -/
def NormalizedFrobeniusClause : Prop :=
  letI := T.topology
  letI := T.generalLinearTopologicalGroup n
  ∀ (ρ : Representation ℂ (GeneralLinear n F.Carrier) V)
    (σ : Representation ℂ (B.Levi F.Carrier) W),
    IsSmooth ρ → IsSmooth σ →
    ∃ E :
      ρ.IntertwiningMap (Induction.smoothInduced (B.parabolic F.Carrier)
        (twist (T.parabolicHalfModulus B) (inflate B σ))) ≃ₗ[ℂ]
      Representation.IntertwiningMap
        (twist (Jacquet.inverseHalfCharacter (T.leviModulus B))
          (leviCoinvariants B (ρ.comp (B.parabolic F.Carrier).subtype))) σ,
      ∀ f v,
        E f (Jacquet.mk (ρ.comp (B.parabolic F.Carrier).subtype)
          (B.unipotentRadical F.Carrier) v) =
        Induction.eval (B.parabolic F.Carrier)
          (twist (T.parabolicHalfModulus B) (inflate B σ)) (f v) 1

/-- Actual normalized Jacquet smoothness, admissibility, exactness and
evaluation reciprocity, with independent field and three carrier universes. -/
def NormalizedJacquetStatement : Prop :=
  NormalizedJacquetSmoothnessClause F T B V ∧
  NormalizedJacquetAdmissibilityClause F T B V ∧
  NormalizedJacquetExactnessClause F T B U V W ∧
  NormalizedFrobeniusClause F T B V W

end Langlands.Parabolic
