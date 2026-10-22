import Langlands.Representation.CuspidalSupport.LeviDefinitions
import Langlands.Representation.Jacquet.Parabolic

/-! Comparison of standard Jacquet vanishing and the existing cuspidality predicates. -/

noncomputable section

namespace Langlands.CuspidalSupport

open GeneralLinear

universe uF uV

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p}
  (T : F.TopologicalData) (n : ℕ)

/-- The conjugate-radical definition of supercuspidality agrees with
admissibility and vanishing of all proper standard Jacquet quotients. -/
def StandardJacquetSupercuspidalityClause : Prop :=
  letI := T.topology
  ∀ (V : Type uV) [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ (GeneralLinear n F.Carrier) V),
    IsSupercuspidal ρ ↔
      IsAdmissible ρ ∧
        ∀ B : BlockShape n, B.parabolic F.Carrier ≠ ⊤ →
          Subsingleton (B.JacquetModule ρ)

/-- Pullback along the actual block diagonal embedding for a single block
identifies product-Levi cuspidality with GL supercuspidality. -/
def SingleBlockCuspidalityClause : Prop :=
  letI := T.topology
  ∀ (B : BlockShape n), B.length = 1 →
    ∀ (V : Type uV) [AddCommGroup V] [Module ℂ V]
      (ρ : Representation ℂ (GeneralLinear n F.Carrier) V),
      IsLeviCuspidal B (ρ.comp (B.leviEmbedding F.Carrier)) ↔ IsSupercuspidal ρ

/-- The two comparison targets for every positive-rank p-adic general linear group. -/
def PadicCuspidalityComparisonTheorems : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData)
    (n : ℕ), 0 < n →
      StandardJacquetSupercuspidalityClause.{uF, uV} T n ∧
      SingleBlockCuspidalityClause.{uF, uV} T n

end Langlands.CuspidalSupport
