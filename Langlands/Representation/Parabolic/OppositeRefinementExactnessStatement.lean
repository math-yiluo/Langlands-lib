import Langlands.Representation.Parabolic.OppositeRefinementFunctors

/-! Exactness and binary products for the actual normalized refined opposite
Jacquet quotient. These are proposition definitions, not proofs. -/

namespace Langlands.Parabolic

open GeneralLinear Geometric

universe uF uU uV uW

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)
  (T : F.TopologicalData) {n : ℕ} (B : BlockShape n) (S : BlockRefinement B)

/-- The actual normalized refined opposite quotient preserves injections into
smooth representations, on the original independently quantified carriers. -/
def NormalizedRefinedOppositeJacquetInjectionClause : Prop :=
  letI := T.topology
  ∀ (U : Type uU) (V : Type uV) [AddCommGroup U] [Module ℂ U]
    [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ (B.Levi F.Carrier) U)
    (σ : Representation ℂ (B.Levi F.Carrier) V) (i : ρ.IntertwiningMap σ),
    IsSmooth σ → Function.Injective i →
      Function.Injective (T.normalizedRefinedOppositeJacquetMap B S i)

/-- The actual quotient maps preserve right exact sequences algebraically;
no smoothness or injectivity premise is needed here. -/
def NormalizedRefinedOppositeJacquetRightExactnessClause : Prop :=
  ∀ (U : Type uU) (V : Type uV) (W : Type uW)
    [AddCommGroup U] [Module ℂ U] [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W]
    (ρ : Representation ℂ (B.Levi F.Carrier) U)
    (σ : Representation ℂ (B.Levi F.Carrier) V)
    (τ : Representation ℂ (B.Levi F.Carrier) W)
    (i : ρ.IntertwiningMap σ) (q : σ.IntertwiningMap τ),
    Function.Surjective q →
    LinearMap.range i.toLinearMap = LinearMap.ker q.toLinearMap →
      LinearMap.range (T.normalizedRefinedOppositeJacquetMap B S i).toLinearMap =
        LinearMap.ker (T.normalizedRefinedOppositeJacquetMap B S q).toLinearMap ∧
      Function.Surjective (T.normalizedRefinedOppositeJacquetMap B S q)

/-- The actual binary-product comparison is an equivariant linear equivalence
and sends the class of a pair to the pair of its classes. -/
def NormalizedRefinedOppositeJacquetBinaryProductClause : Prop :=
  ∀ (U : Type uU) (V : Type uV) [AddCommGroup U] [Module ℂ U]
    [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ (B.Levi F.Carrier) U)
    (σ : Representation ℂ (B.Levi F.Carrier) V),
    ∃ E : (T.normalizedRefinedOppositeJacquet B S (ρ.prod σ)).Equiv
      ((T.normalizedRefinedOppositeJacquet B S ρ).prod
        (T.normalizedRefinedOppositeJacquet B S σ)),
      ∀ (u : U) (v : V),
        E (refinedOppositeJacquetMk B S (ρ.prod σ) (u, v)) =
          (refinedOppositeJacquetMk B S ρ u, refinedOppositeJacquetMk B S σ v)

/-- Closed exactness and binary-product assertions for all actual p-adic
refinements, including zero rank and zero representations. -/
def NormalizedRefinedOppositeJacquetExactnessStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData)
    (n : ℕ) (B : BlockShape n) (S : BlockRefinement B),
    NormalizedRefinedOppositeJacquetInjectionClause.{uF, uU, uV} F T B S ∧
    NormalizedRefinedOppositeJacquetRightExactnessClause.{uF, uU, uV, uW} F T B S ∧
    NormalizedRefinedOppositeJacquetBinaryProductClause.{uF, uU, uV} F T B S

end Langlands.Parabolic
