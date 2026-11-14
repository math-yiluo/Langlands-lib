import Langlands.Representation.Parabolic.NormalizedInductionStatement
import Langlands.AllField.Group.GL.BlockModulusSupplement
import Langlands.AllField.Representation.Parabolic.NormalizedInductionStatement
namespace Langlands.AllField.Parabolic
open Langlands.Parabolic hiding NormalizedInductionExactnessClause
open Langlands.AllField.Parabolic

universe uF uU uV uW

variable (F : Type uF) [Field F]
    (T : LocalFieldData F) {n : ℕ} (B : GeneralLinear.BlockShape n)
    (U : Type uU) (V : Type uV) (W : Type uW)
    [AddCommGroup U] [Module ℂ U] [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W]

/-- The actual maps of normalized parabolic induction preserve short exact
sequences of smooth complex representations of the product Levi. -/
def NormalizedInductionExactnessClause : Prop :=
  letI := T.topology
  letI := T.generalLinearTopologicalGroup n
  ∀ (ρ : Representation ℂ (B.Levi F) U)
    (σ : Representation ℂ (B.Levi F) V)
    (τ : Representation ℂ (B.Levi F) W)
    (i : ρ.IntertwiningMap σ) (q : σ.IntertwiningMap τ),
    IsSmooth ρ → IsSmooth σ → IsSmooth τ →
    Function.Injective i → Function.Surjective q →
    LinearMap.range i.toLinearMap = LinearMap.ker q.toLinearMap →
    let iP : Representation.IntertwiningMap
        (ρ.comp (B.leviProjection F))
        (σ.comp (B.leviProjection F)) :=
      { toLinearMap := i.toLinearMap
        isIntertwining' g := i.isIntertwining' (B.leviProjection F g) }
    let qP : Representation.IntertwiningMap
        (σ.comp (B.leviProjection F))
        (τ.comp (B.leviProjection F)) :=
      { toLinearMap := q.toLinearMap
        isIntertwining' g := q.isIntertwining' (B.leviProjection F g) }
    let iG := Induction.smoothInducedMap (B.parabolic F)
      (twistIntertwining (T.parabolicHalfModulus B) iP)
    let qG := Induction.smoothInducedMap (B.parabolic F)
      (twistIntertwining (T.parabolicHalfModulus B) qP)
    Function.Injective iG ∧
      LinearMap.range iG.toLinearMap = LinearMap.ker qG.toLinearMap ∧
      Function.Surjective qG

end Langlands.AllField.Parabolic
