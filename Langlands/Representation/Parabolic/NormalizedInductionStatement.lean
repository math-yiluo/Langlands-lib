import Langlands.Group.GL.BlockModulus
import Langlands.Representation.Induction.Definitions
import Langlands.Representation.Smooth.Contragredient.Definitions
import Langlands.Representation.Unitary.Basic

namespace Langlands.Parabolic

universe uF uU uV uW

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)
    (T : F.TopologicalData) {n : ℕ} (B : GeneralLinear.BlockShape n)
    (U : Type uU) (V : Type uV) (W : Type uW)
    [AddCommGroup U] [Module ℂ U] [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W]

/-- Admissibility for right-translation induction with the actual positive
block half-modulus. -/
def NormalizedInductionAdmissibilityClause : Prop :=
  letI := T.topology
  letI := T.generalLinearTopologicalGroup n
  ∀ σ : Representation ℂ (B.Levi F.Carrier) V,
    IsAdmissible σ →
    IsAdmissible (Induction.smoothInduced (B.parabolic F.Carrier)
      (twist (T.parabolicHalfModulus B)
        (σ.comp (B.leviProjection F.Carrier))))

/-- The actual maps of normalized parabolic induction preserve short exact
sequences of smooth complex representations of the product Levi. -/
def NormalizedInductionExactnessClause : Prop :=
  letI := T.topology
  letI := T.generalLinearTopologicalGroup n
  ∀ (ρ : Representation ℂ (B.Levi F.Carrier) U)
    (σ : Representation ℂ (B.Levi F.Carrier) V)
    (τ : Representation ℂ (B.Levi F.Carrier) W)
    (i : ρ.IntertwiningMap σ) (q : σ.IntertwiningMap τ),
    IsSmooth ρ → IsSmooth σ → IsSmooth τ →
    Function.Injective i → Function.Surjective q →
    LinearMap.range i.toLinearMap = LinearMap.ker q.toLinearMap →
    let iP : Representation.IntertwiningMap
        (ρ.comp (B.leviProjection F.Carrier))
        (σ.comp (B.leviProjection F.Carrier)) :=
      { toLinearMap := i.toLinearMap
        isIntertwining' g := i.isIntertwining' (B.leviProjection F.Carrier g) }
    let qP : Representation.IntertwiningMap
        (σ.comp (B.leviProjection F.Carrier))
        (τ.comp (B.leviProjection F.Carrier)) :=
      { toLinearMap := q.toLinearMap
        isIntertwining' g := q.isIntertwining' (B.leviProjection F.Carrier g) }
    let iG := Induction.smoothInducedMap (B.parabolic F.Carrier)
      (twistIntertwining (T.parabolicHalfModulus B) iP)
    let qG := Induction.smoothInducedMap (B.parabolic F.Carrier)
      (twistIntertwining (T.parabolicHalfModulus B) qP)
    Function.Injective iG ∧
      LinearMap.range iG.toLinearMap = LinearMap.ker qG.toLinearMap ∧
      Function.Surjective qG

/-- Smooth contragredient commutes with normalized induction from the same
actual upper parabolic, for admissible Levi input. -/
def NormalizedInductionDualityClause : Prop :=
  letI := T.topology
  letI := T.generalLinearTopologicalGroup n
  letI := T.leviTopologicalGroup B
  ∀ σ : Representation ℂ (B.Levi F.Carrier) V,
    IsAdmissible σ →
    Nonempty (Representation.Equiv
      (smoothContragredient (Induction.smoothInduced (B.parabolic F.Carrier)
        (twist (T.parabolicHalfModulus B)
          (σ.comp (B.leviProjection F.Carrier)))))
      (Induction.smoothInduced (B.parabolic F.Carrier)
        (twist (T.parabolicHalfModulus B)
          ((smoothContragredient σ).comp (B.leviProjection F.Carrier)))))

/-- Normalized induction preserves existence of a positive invariant
Hermitian form for admissible Levi input. -/
def NormalizedInductionUnitarityClause : Prop :=
  letI := T.topology
  letI := T.generalLinearTopologicalGroup n
  ∀ σ : Representation ℂ (B.Levi F.Carrier) V,
    IsAdmissible σ → IsUnitarizable σ →
    IsUnitarizable (Induction.smoothInduced (B.parabolic F.Carrier)
      (twist (T.parabolicHalfModulus B)
        (σ.comp (B.leviProjection F.Carrier))))

/-- Structural normalized-induction assertions on actual finite-p-adic GL
blocks. The field and all three representation universes are independent. -/
def NormalizedInductionStatement : Prop :=
  NormalizedInductionAdmissibilityClause F T B V ∧
  NormalizedInductionExactnessClause F T B U V W ∧
  NormalizedInductionDualityClause F T B V ∧
  NormalizedInductionUnitarityClause F T B V

end Langlands.Parabolic
