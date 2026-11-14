import Langlands.AllFieldBZ.Group.GL.BlockModulus
import Langlands.Representation.Parabolic.NormalizedJacquetStatement

/-!
# All-field port of `Langlands.Representation.Parabolic.NormalizedJacquetStatement`

Mechanical port of the field-dependent declarations of the p-adic module
`Langlands.Representation.Parabolic.NormalizedJacquetStatement` to an arbitrary nonarchimedean local field
(`Langlands.AllFieldBZ.LocalFieldPackage`). See the paired Markdown.
-/
namespace Langlands.AllFieldBZ.Parabolic
open Langlands.Parabolic hiding NormalizedJacquetExactnessClause
universe uF uU uV uW

variable (F : LocalFieldPackage.{uF})
    (T : F.TopologicalData) {n : ℕ} (B : GeneralLinear.BlockShape n)
    (U : Type uU) (V : Type uV) (W : Type uW)
    [AddCommGroup U] [Module ℂ U] [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W]

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

end Langlands.AllFieldBZ.Parabolic
