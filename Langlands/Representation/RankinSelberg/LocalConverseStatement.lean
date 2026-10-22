import Langlands.Representation.RankinSelberg.EpsilonFactor
import Langlands.LocalFactor.Abelian.Padic

/-!
# Henniart's local converse theorems for epsilon factors of pairs

Henniart 1993, printed page 340, Corollary: two supercuspidal representations
of `GL_n(F)`, `n ≥ 2`, with the same epsilon factors of pairs against every
supercuspidal representation of `GL_r(F)`, `1 ≤ r ≤ n - 1`, are equivalent. The
epsilon factors are the JPSS relation `IsPairEpsilonFactor` with the self-dual
measure; agreement means one common factor value.
-/

noncomputable section

namespace Langlands.RankinSelberg

open HarmonicAnalysis Whittaker GeneralLinear

universe uF uV uW

variable {p : ℕ} [Fact p.Prime]

/-- The epsilon-factor relation for actual representations of `GL_(r+1)(F)` and
`GL_(n+1)(F)` over a p-adic field with its canonical topological data: `q` is
the residue cardinality and the absolute value is the normalized one. -/
def IsPadicPairEpsilonFactor (F : PadicField.{uF} p)
    (ψ : letI := F.canonicalTopologicalData.topology; UnitaryAdditiveCharacter F.Carrier)
    (ν : letI := F.canonicalTopologicalData.topology; letI := borel F.Carrier
      AdditiveHaarMeasure F.Carrier)
    {r n : ℕ} {V : Type uV} {W : Type uW} [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W]
    (π : Representation ℂ (Langlands.GeneralLinear (r + 1) F.Carrier) V)
    (σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F.Carrier) W)
    (e : ℂˣ × ℤ) : Prop :=
  letI := F.canonicalTopologicalData.topology
  letI := F.canonicalTopologicalData.valuativeRel
  letI := F.canonicalTopologicalData.localField
  letI := borel F.Carrier
  letI : BorelSpace F.Carrier := ⟨rfl⟩
  letI := borel (Langlands.GeneralLinear (n + 1) F.Carrier)
  letI : BorelSpace (Langlands.GeneralLinear (n + 1) F.Carrier) := ⟨rfl⟩
  letI := borel (upperUnipotent (n + 1) F.Carrier)
  letI : BorelSpace (upperUnipotent (n + 1) F.Carrier) := ⟨rfl⟩
  letI := borel (LeftUnipotentQuotient n F.Carrier)
  IsPairEpsilonFactor F.canonicalTopologicalData.residueCardinality ψ
    (normalizedAbsoluteValue F.canonicalTopologicalData) ν π σ e

/-- Two supercuspidal classes of `GL_(k+2)(F)` have the same epsilon factor of
pairs, with respect to `ψ` and `ν`, against every supercuspidal class of
`GL_(r+1)(F)` for `r ≤ k`: for each test class some value is the epsilon
factor of both pairs. -/
def SameClassEpsilonFactors (F : PadicField.{uF} p)
    (ψ : letI := F.canonicalTopologicalData.topology; UnitaryAdditiveCharacter F.Carrier)
    (ν : letI := F.canonicalTopologicalData.topology; letI := borel F.Carrier
      AdditiveHaarMeasure F.Carrier) (k : ℕ)
    (π π' : PadicField.SupercuspidalClass.{uV, uF} F (k + 1 + 1) (Nat.succ_pos (k + 1))) :
    Prop :=
  ∀ r ≤ k, ∀ τ : PadicField.SupercuspidalClass.{uW, uF} F (r + 1) (Nat.succ_pos r),
    ∃ e : ℂˣ × ℤ, IsClassEpsilonFactor F ψ ν π τ e ∧ IsClassEpsilonFactor F ψ ν π' τ e

/-- Two actual representations of `GL_(k+2)(F)` have the same epsilon factor of
pairs, with respect to `ψ` and `ν`, against every actual supercuspidal
representation of `GL_(r+1)(F)` for `r ≤ k`. -/
def SameSupercuspidalEpsilonFactors (F : PadicField.{uF} p)
    (ψ : letI := F.canonicalTopologicalData.topology; UnitaryAdditiveCharacter F.Carrier)
    (ν : letI := F.canonicalTopologicalData.topology; letI := borel F.Carrier
      AdditiveHaarMeasure F.Carrier) (k : ℕ)
    {V V' : Type uV} [AddCommGroup V] [Module ℂ V] [AddCommGroup V'] [Module ℂ V']
    (π : Representation ℂ (Langlands.GeneralLinear (k + 1 + 1) F.Carrier) V)
    (π' : Representation ℂ (Langlands.GeneralLinear (k + 1 + 1) F.Carrier) V') : Prop :=
  ∀ r ≤ k, ∀ τ : (letI := F.canonicalTopologicalData.topology
      GeneralLinear.SupercuspidalRep.{uF, uW} (F := F.Carrier) (n := r + 1)),
    letI := F.canonicalTopologicalData.topology
    ∃ e : ℂˣ × ℤ, IsPadicPairEpsilonFactor F ψ ν π τ.obj.representation e ∧
      IsPadicPairEpsilonFactor F ψ ν π' τ.obj.representation e

/-- On representatives the class condition is the condition on actual
representations. -/
theorem sameClassEpsilonFactors_mk_iff (F : PadicField.{uF} p)
    (ψ : letI := F.canonicalTopologicalData.topology; UnitaryAdditiveCharacter F.Carrier)
    (ν : letI := F.canonicalTopologicalData.topology; letI := borel F.Carrier
      AdditiveHaarMeasure F.Carrier) (k : ℕ)
    (A A' : letI := F.canonicalTopologicalData.topology
      GeneralLinear.SupercuspidalRep.{uF, uV} (F := F.Carrier) (n := k + 1 + 1)) :
    SameClassEpsilonFactors.{uF, uV, uW} F ψ ν k (Quotient.mk _ A) (Quotient.mk _ A') ↔
      letI := F.canonicalTopologicalData.topology
      SameSupercuspidalEpsilonFactors.{uF, uV, uW} F ψ ν k
        A.obj.representation A'.obj.representation := by
  refine forall₂_congr fun r _ => ⟨fun h B => h (Quotient.mk _ B), fun h τ => ?_⟩
  induction τ using Quotient.inductionOn with
  | h B => exact h B

/-- Henniart 1993, Corollary (printed page 340), for every p-adic field, every
nontrivial unitary additive character `ψ`, the self-dual additive Haar measure
`ν` for `ψ`, and every rank `n = k + 2 ≥ 2`: supercuspidal classes with the same
epsilon factors of pairs against all supercuspidal classes of ranks `1, ..., n - 1`
are equal. -/
def SupercuspidalLocalConverseStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{uF} p)
    (ψ : letI := F.canonicalTopologicalData.topology; UnitaryAdditiveCharacter F.Carrier)
    (ν : LocalFactor.PadicAbelian.SelfDualHaar F.canonicalTopologicalData ψ) (k : ℕ)
    (π π' : PadicField.SupercuspidalClass.{uV, uF} F (k + 1 + 1) (Nat.succ_pos (k + 1))),
    SameClassEpsilonFactors.{uF, uV, uW} F ψ ν.val k π π' → π = π'

end Langlands.RankinSelberg
