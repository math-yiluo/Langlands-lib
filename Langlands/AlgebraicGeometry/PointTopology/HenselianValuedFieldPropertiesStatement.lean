import Langlands.AlgebraicGeometry.PointTopology.HenselianEtalePointStatement
import Mathlib.Analysis.Normed.Field.WithAbs
import Mathlib.Analysis.Normed.Unbundled.RingSeminorm
import Mathlib.FieldTheory.IsRealClosed.Basic
import Mathlib.RingTheory.Etale.Basic
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.TensorProduct.Basic
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Topology.MetricSpace.Ultra.Basic

/-!
# Henselian valued fields: the assertions of Conrad's printed p.14

Conrad recalls a number of facts about henselian valued fields before Lemma 5.3: the
characterization by separable closedness in the completion, the valuation-ring criterion in
the non-archimedean case, the decomposition of `k' ⊗_k k̂` into completions, the consequence
that this tensor product is a field for henselian `k`, the description of archimedean henselian
fields, and the equivalence of finite étale algebras over `k` and over `k̂`.
-/

noncomputable section

universe u

open scoped TensorProduct

namespace Langlands.AlgebraicGeometry.PointTopology

/-- The characterization of henselian valued fields: `K` is henselian exactly when it is
separably algebraically closed in its completion. -/
def HenselianIffSeparablyClosedStatement : Prop :=
  ∀ (K : Type u) [NontriviallyNormedField K],
    IsHenselianValuedField K ↔ separableClosure K (UniformSpace.Completion K) = ⊥

/-- The non-archimedean criterion ([Ber, 2.4.3]): a non-archimedean `K` is henselian exactly
when its valuation ring, the closed unit ball, is a henselian local ring. -/
def HenselianIffValuationRingHenselianStatement : Prop :=
  ∀ (K : Type u) [NontriviallyNormedField K] [IsUltrametricDist K] (O : Subring K),
    (∀ x : K, x ∈ O ↔ ‖x‖ ≤ 1) → (IsHenselianValuedField K ↔ HenselianLocalRing O)

/-- For a finite separable extension `L` of a valued field `K`, the completion of `K` tensored
with `L` is the product of the completions of `L` at the finitely many absolute values
extending the absolute value of `K`. -/
def TensorCompletionProductStatement : Prop :=
  ∀ (K : Type u) [NontriviallyNormedField K] (L : Type u) [Field L] [Algebra K L]
    [FiniteDimensional K L] [Algebra.IsSeparable K L],
    Finite {w : AbsoluteValue L ℝ // w.LiesOver (NormedField.toAbsoluteValue K)} ∧
      letI (w : {w : AbsoluteValue L ℝ // w.LiesOver (NormedField.toAbsoluteValue K)}) :
          Algebra (NormedField.toAbsoluteValue K).Completion w.1.Completion :=
        @AbsoluteValue.Completion.algebraOfLiesOver K _ (NormedField.toAbsoluteValue K) L _ _ w.1 w.2
      Nonempty ((NormedField.toAbsoluteValue K).Completion ⊗[K] L ≃ₐ[(NormedField.toAbsoluteValue K).Completion]
        ∀ w : {w : AbsoluteValue L ℝ // w.LiesOver (NormedField.toAbsoluteValue K)}, w.1.Completion)

/-- For a henselian `K` and a finite separable extension `L`, the completion of `K` tensored with
`L` is a field, of degree `[L : K]` over the completion. -/
def HenselianTensorCompletionFieldStatement : Prop :=
  ∀ (K : Type u) [NontriviallyNormedField K], IsHenselianValuedField K →
    ∀ (L : Type u) [Field L] [Algebra K L] [FiniteDimensional K L] [Algebra.IsSeparable K L],
      IsField (UniformSpace.Completion K ⊗[K] L) ∧
        Module.finrank (UniformSpace.Completion K) (UniformSpace.Completion K ⊗[K] L) =
          Module.finrank K L

/-- The archimedean henselian fields are the algebraically closed subfields of `ℂ` and the real
closed subfields of `ℝ`, with the induced absolute value up to a power: an archimedean `K` is
henselian exactly when it has an embedding `σ` into `ℂ` with `‖x‖ = ‖σ x‖ ^ s` for some
`0 < s ≤ 1`, and either `K` is algebraically closed, or `σ` lands in `ℝ` and `K` is real
closed. -/
def ArchimedeanHenselianStatement : Prop :=
  ∀ (K : Type u) [NontriviallyNormedField K], ¬ IsUltrametricDist K →
    (IsHenselianValuedField K ↔
      ∃ (σ : K →+* ℂ) (s : ℝ), 0 < s ∧ s ≤ 1 ∧ (∀ x, ‖x‖ = ‖σ x‖ ^ s) ∧
        (IsAlgClosed K ∨ ((∀ x, (σ x).im = 0) ∧ IsRealClosed K)))

/-- For a henselian `K`, base change `A ↦ K̂ ⊗_K A` is an equivalence between finite étale
`K`-algebras and finite étale `K̂`-algebras: it is bijective on algebra maps and every finite
étale `K̂`-algebra arises. -/
def HenselianFiniteEtaleEquivalenceStatement : Prop :=
  ∀ (K : Type u) [NontriviallyNormedField K], IsHenselianValuedField K →
    (∀ (A B : Type u) [CommRing A] [Algebra K A] [Algebra.Etale K A] [Module.Finite K A]
        [CommRing B] [Algebra K B] [Algebra.Etale K B] [Module.Finite K B],
        Function.Bijective (fun φ : A →ₐ[K] B =>
          Algebra.TensorProduct.map
            (AlgHom.id (UniformSpace.Completion K) (UniformSpace.Completion K)) φ)) ∧
      ∀ (E : Type u) [CommRing E] [Algebra (UniformSpace.Completion K) E]
        [Algebra.Etale (UniformSpace.Completion K) E]
        [Module.Finite (UniformSpace.Completion K) E],
        ∃ (A : Type u) (_ : CommRing A) (_ : Algebra K A), Algebra.Etale K A ∧
          Module.Finite K A ∧
            Nonempty (UniformSpace.Completion K ⊗[K] A ≃ₐ[UniformSpace.Completion K] E)

/-- The assertions on henselian valued fields of Conrad's printed p.14. -/
def HenselianValuedFieldPropertiesStatement : Prop :=
  HenselianIffSeparablyClosedStatement.{u} ∧ HenselianIffValuationRingHenselianStatement.{u} ∧
    TensorCompletionProductStatement.{u} ∧ HenselianTensorCompletionFieldStatement.{u} ∧
    ArchimedeanHenselianStatement.{u} ∧ HenselianFiniteEtaleEquivalenceStatement.{u}

end Langlands.AlgebraicGeometry.PointTopology
