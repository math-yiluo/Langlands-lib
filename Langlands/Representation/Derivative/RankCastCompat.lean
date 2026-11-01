import Langlands.Representation.Derivative.Homogeneity

/-! Natural compatibility of actual rank transport, restriction, and derivatives. -/

noncomputable section
open CategoryTheory

namespace Langlands.Derivative

universe uF uV

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p}

/-- Rank transport commutes naturally with each valid general-linear derivative. -/
def generalLinearRankCastDerivativeIso (T : F.TopologicalData)
    (ψ : @HarmonicAnalysis.UnitaryAdditiveCharacter F.Carrier _ T.topology)
    {m n : ℕ} (h : m = n) (d : ℕ) (hm : d ≤ m) (hn : d ≤ n) :
    letI := T.topology
    generalLinearRankCast.{uF, uV} T h ⋙ generalLinearDerivative T ψ n d hn ≅
      generalLinearDerivative T ψ m d hm ⋙
        generalLinearRankCast T (congrArg (fun r => r - d) h) := by
  letI := T.topology
  subst n
  exact eqToIso ((Functor.id_comp _).trans (Functor.comp_id _).symm)

/-- Rank transport commutes naturally with each valid mirabolic derivative. -/
def mirabolicRankCastDerivativeIso (T : F.TopologicalData)
    (ψ : @HarmonicAnalysis.UnitaryAdditiveCharacter F.Carrier _ T.topology)
    {m n : ℕ} (h : m = n) (d : ℕ)
    (hm : 0 < d ∧ d ≤ m + 1) (hn : 0 < d ∧ d ≤ n + 1) :
    letI := T.topology
    mirabolicRankCast.{uF, uV} T h ⋙ mirabolicDerivativeOfOrder T ψ n d hn ≅
      mirabolicDerivativeOfOrder T ψ m d hm ⋙
        generalLinearRankCast T (congrArg (fun r => r + 1 - d) h) := by
  letI := T.topology
  subst n
  exact eqToIso ((Functor.id_comp _).trans (Functor.comp_id _).symm)

/-- The natural square relating general-linear and mirabolic rank transport. -/
def generalLinearRankCastRestrictionIso (T : F.TopologicalData)
    {m n : ℕ} (h : m = n) :
    letI := T.topology
    generalLinearRankCast.{uF, uV} T (congrArg (fun r => r + 1) h) ⋙
        generalLinearRestriction T n ≅
      generalLinearRestriction T m ⋙ mirabolicRankCast T h := by
  letI := T.topology
  subst n
  exact eqToIso ((Functor.id_comp _).trans (Functor.comp_id _).symm)

/-- A positive general-linear derivative is restriction followed by the actual
mirabolic derivative of the same order, including the top-order boundary. -/
def generalLinearRestrictionDerivativeIso (T : F.TopologicalData)
    (ψ : @HarmonicAnalysis.UnitaryAdditiveCharacter F.Carrier _ T.topology)
    (n d : ℕ) (hd : 0 < d ∧ d ≤ n + 1) :
    letI := T.topology
    generalLinearRestriction.{uF, uV} T n ⋙
        mirabolicDerivativeOfOrder T ψ n d hd ≅
      generalLinearDerivative T ψ (n + 1) d hd.2 := by
  letI := T.topology
  let h := mirabolic_rank_eq_of_order hd
  have e := generalLinearRankCastRestrictionIso.{uF, uV} T h
  refine (Functor.isoWhiskerRight e.symm
    (mirabolicDerivative T ψ (n + 1 - d) (d - 1))) ≪≫ ?_
  apply eqToIso
  exact (generalLinearDerivative_of_pos T ψ (n + 1) d hd.2 hd.1).symm

end Langlands.Derivative
