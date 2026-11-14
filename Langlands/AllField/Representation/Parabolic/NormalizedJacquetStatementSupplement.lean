import Langlands.Representation.Parabolic.NormalizedJacquetStatement
import Langlands.AllField.Group.GL.BlockModulusSupplement
import Langlands.AllField.Representation.Parabolic.NormalizedJacquetStatement
namespace Langlands.AllField.Parabolic
open Langlands.Parabolic hiding NormalizedJacquetExactnessClause
open Langlands.AllField.Parabolic

universe uF uU uV uW

variable (F : Type uF) [Field F]
    (T : LocalFieldData F) {n : ℕ} (B : GeneralLinear.BlockShape n)
    (U : Type uU) (V : Type uV) (W : Type uW)
    [AddCommGroup U] [Module ℂ U] [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W]

/-- The normalized quotient intertwiners preserve all three parts of a short
exact sequence of smooth ambient representations. -/
def NormalizedJacquetExactnessClause : Prop :=
  letI := T.topology
  ∀ (ρ : Representation ℂ (GeneralLinear n F) U)
    (σ : Representation ℂ (GeneralLinear n F) V)
    (τ : Representation ℂ (GeneralLinear n F) W)
    (i : ρ.IntertwiningMap σ) (q : σ.IntertwiningMap τ),
    IsSmooth ρ → IsSmooth σ → IsSmooth τ →
    Function.Injective i → Function.Surjective q →
    LinearMap.range i.toLinearMap = LinearMap.ker q.toLinearMap →
    let iN := twistIntertwining (Jacquet.inverseHalfCharacter (T.leviModulus B))
      (leviCoinvariantsMap B (Jacquet.restrictMap i (B.parabolic F)))
    let qN := twistIntertwining (Jacquet.inverseHalfCharacter (T.leviModulus B))
      (leviCoinvariantsMap B (Jacquet.restrictMap q (B.parabolic F)))
    Function.Injective iN ∧
      LinearMap.range iN.toLinearMap = LinearMap.ker qN.toLinearMap ∧
      Function.Surjective qN

end Langlands.AllField.Parabolic
