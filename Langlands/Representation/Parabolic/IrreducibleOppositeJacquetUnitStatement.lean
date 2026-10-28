import Langlands.Representation.Parabolic.SecondAdjointnessStatement

/-!
# Irreducible opposite-Jacquet unit embeddings

Existence of injective intertwiners into the opposite Jacquet module of one's
own normalized induction, for standard and refined parabolics.
-/

namespace Langlands.Parabolic

open GeneralLinear Geometric

universe uF uV

/-- An irreducible admissible Levi representation embeds into the opposite
normalized Jacquet module of its actual standard normalized induction. -/
def StandardIrreducibleOppositeJacquetUnitClause : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData),
    letI := T.topology
    ∀ (n : ℕ), 0 < n → ∀ (B : BlockShape n)
      (σ : Rep.{uV} ℂ (B.Levi F.Carrier)),
      σ.ρ.IsIrreducible → IsAdmissible σ.ρ →
        let I : Rep.{max uF uV} ℂ (GeneralLinear n F.Carrier) :=
          Rep.of (T.normalizedParabolicInduced B σ.ρ)
        ∃ j : σ.ρ.IntertwiningMap
            (CuspidalJacquetMultiplicity.oppositeJacquet T B I).ρ,
          Function.Injective j

/-- The analogous embedding for arbitrary inducing representations of a
refined Levi, with normalized induction inside the whole product Levi. -/
def RefinedIrreducibleOppositeJacquetUnitClause : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData),
    letI := T.topology
    ∀ (n : ℕ), 0 < n → ∀ (B : BlockShape n) (S : BlockRefinement B)
      (σ : Rep.{uV} ℂ (refinedLevi F.Carrier B S)),
      σ.ρ.IsIrreducible → IsAdmissible σ.ρ →
        let I : Rep.{max uF uV} ℂ (B.Levi F.Carrier) :=
          Rep.of (T.normalizedRefinedInduced B S σ.ρ)
        ∃ j : σ.ρ.IntertwiningMap (T.normalizedRefinedOppositeJacquet B S I.ρ),
          Function.Injective j

/-- Standard and refined existence statements, retaining independent field and
inducing-carrier universes. No canonical choice of an embedding is asserted. -/
def IrreducibleOppositeJacquetUnitStatement : Prop :=
  StandardIrreducibleOppositeJacquetUnitClause.{uF, uV} ∧
    RefinedIrreducibleOppositeJacquetUnitClause.{uF, uV}

end Langlands.Parabolic
