import Langlands.Group.GL.Blocks
import Langlands.Group.GL.Padic
import Langlands.Representation.Induction.Definitions
import Langlands.Representation.Jacquet.Coinvariants

namespace Langlands.Parabolic

universe uF uU uV uW

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)
    (T : F.TopologicalData) {n : ℕ} (B : GeneralLinear.BlockShape n)
    (U : Type uU) (V : Type uV) (W : Type uW)
    [AddCommGroup U] [Module ℂ U] [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W]

/-- Evaluation reciprocity for the actual unnormalized block-parabolic
induction and Levi Jacquet quotient. -/
def FrobeniusClause : Prop :=
  letI := T.topology
  letI := T.generalLinearTopologicalGroup n
  ∀ (ρ : Representation ℂ (GeneralLinear n F.Carrier) V)
    (σ : Representation ℂ (B.Levi F.Carrier) W),
    IsSmooth ρ → IsSmooth σ →
    ∃ E :
      ρ.IntertwiningMap (Induction.smoothInduced (B.parabolic F.Carrier)
        (σ.comp (B.leviProjection F.Carrier))) ≃ₗ[ℂ]
      Representation.IntertwiningMap
        ((Representation.toCoinvariants (ρ.comp (B.parabolic F.Carrier).subtype)
          (B.unipotentRadical F.Carrier)).comp (B.leviInParabolic F.Carrier)) σ,
      ∀ f v,
        E f (Representation.Coinvariants.mk
          ((ρ.comp (B.parabolic F.Carrier).subtype).comp
            (B.unipotentRadical F.Carrier).subtype) v) =
        Induction.eval (B.parabolic F.Carrier)
          (σ.comp (B.leviProjection F.Carrier)) (f v) 1

/-- Exactness of the actual unipotent coinvariant maps for smooth GL
representations, without an assumed compact-exhaustion premise. -/
def JacquetExactnessClause : Prop :=
  letI := T.topology
  ∀ (ρ : Representation ℂ (GeneralLinear n F.Carrier) U)
    (σ : Representation ℂ (GeneralLinear n F.Carrier) V)
    (τ : Representation ℂ (GeneralLinear n F.Carrier) W)
    (i : ρ.IntertwiningMap σ) (q : σ.IntertwiningMap τ),
    IsSmooth ρ → IsSmooth σ → IsSmooth τ →
    Function.Injective i → Function.Surjective q →
    LinearMap.range i.toLinearMap = LinearMap.ker q.toLinearMap →
    let P := B.parabolic F.Carrier
    let N := B.unipotentRadical F.Carrier
    let iN := Representation.Coinvariants.map
      ((ρ.comp P.subtype).comp N.subtype) ((σ.comp P.subtype).comp N.subtype)
      (Jacquet.restrictMap (Jacquet.restrictMap i P) N)
    let qN := Representation.Coinvariants.map
      ((σ.comp P.subtype).comp N.subtype) ((τ.comp P.subtype).comp N.subtype)
      (Jacquet.restrictMap (Jacquet.restrictMap q P) N)
    Function.Injective iN ∧ LinearMap.range iN = LinearMap.ker qN ∧
      Function.Surjective qN

/-- Exactness of actual unnormalized block-parabolic induction on smooth
representations of the product Levi. -/
def InductionExactnessClause : Prop :=
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
        (ρ.comp (B.leviProjection F.Carrier)) (σ.comp (B.leviProjection F.Carrier)) :=
      { toLinearMap := i.toLinearMap
        isIntertwining' x := i.isIntertwining' (B.leviProjection F.Carrier x) }
    let qP : Representation.IntertwiningMap
        (σ.comp (B.leviProjection F.Carrier)) (τ.comp (B.leviProjection F.Carrier)) :=
      { toLinearMap := q.toLinearMap
        isIntertwining' x := q.isIntertwining' (B.leviProjection F.Carrier x) }
    let iG := Induction.smoothInducedMap (B.parabolic F.Carrier) iP
    let qG := Induction.smoothInducedMap (B.parabolic F.Carrier) qP
    Function.Injective iG ∧
      LinearMap.range iG.toLinearMap = LinearMap.ker qG.toLinearMap ∧
      Function.Surjective qG

/-- Concrete parabolic exactness and evaluation reciprocity over finite
p-adic extensions; all four carrier universes remain independent. -/
def ExactnessReciprocityStatement : Prop :=
  FrobeniusClause F T B V W ∧
  JacquetExactnessClause F T B U V W ∧
  InductionExactnessClause F T B U V W

end Langlands.Parabolic
