import Langlands.Representation.RankinSelberg.GammaFactor
import Langlands.LocalFactor.Abelian.Padic

/-!
# Henniart's local converse theorems for gamma factors of pairs

Henniart 1993, printed page 340. Theorem 1.1: two irreducible admissible generic
representations of `GL_n(F)`, `n ≥ 2`, with the same gamma factors of pairs
against every irreducible admissible generic representation of `GL_(n-1)(F)` are
equivalent. The referee's Remark: the same conclusion holds when the tests are
the supercuspidal representations of `GL_r(F)`, `1 ≤ r ≤ n - 1`. The gamma
factors are the relation `IsPairGammaFactor` with the self-dual measure;
agreement means one common factor value.
-/

noncomputable section

namespace Langlands.RankinSelberg

open HarmonicAnalysis Whittaker GeneralLinear

universe uF uV uW

variable {p : ℕ} [Fact p.Prime]

/-- Two actual representations of `GL_(k+2)(F)` have the same gamma factor of
pairs, with respect to `ψ` and `ν`, against every irreducible admissible generic
representation of `GL_(k+1)(F)` on a carrier in universe `uW`: for each test
some rational function is the gamma factor of both pairs. -/
def SameGenericGammaFactors (F : PadicField.{uF} p)
    (ψ : letI := F.canonicalTopologicalData.topology; UnitaryAdditiveCharacter F.Carrier)
    (ν : letI := F.canonicalTopologicalData.topology; letI := borel F.Carrier
      AdditiveHaarMeasure F.Carrier) (k : ℕ)
    {V V' : Type uV} [AddCommGroup V] [Module ℂ V] [AddCommGroup V'] [Module ℂ V']
    (π : Representation ℂ (Langlands.GeneralLinear (k + 1 + 1) F.Carrier) V)
    (π' : Representation ℂ (Langlands.GeneralLinear (k + 1 + 1) F.Carrier) V') : Prop :=
  ∀ (W : Type uW) [AddCommGroup W] [Module ℂ W]
    (τ : Representation ℂ (Langlands.GeneralLinear (k + 1) F.Carrier) W),
    (letI := F.canonicalTopologicalData.topology; Whittaker.IsGeneric ψ k τ) →
      ∃ G : RationalFunctions,
        IsPadicPairGammaFactor F ψ ν π τ G ∧ IsPadicPairGammaFactor F ψ ν π' τ G

/-- Henniart 1993, Theorem 1.1 (printed page 340), for every p-adic field, every
unitary additive character `ψ`, the self-dual additive Haar measure `ν` for `ψ`,
and every rank `n = k + 2 ≥ 2`: irreducible admissible generic representations
of `GL_n(F)` with the same gamma factors of pairs against all irreducible
admissible generic representations of `GL_(n-1)(F)` are equivalent. -/
def GenericLocalConverseStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{uF} p)
    (ψ : letI := F.canonicalTopologicalData.topology; UnitaryAdditiveCharacter F.Carrier)
    (ν : LocalFactor.PadicAbelian.SelfDualHaar F.canonicalTopologicalData ψ) (k : ℕ)
    {V V' : Type uV} [AddCommGroup V] [Module ℂ V] [AddCommGroup V'] [Module ℂ V']
    (π : Representation ℂ (Langlands.GeneralLinear (k + 1 + 1) F.Carrier) V)
    (π' : Representation ℂ (Langlands.GeneralLinear (k + 1 + 1) F.Carrier) V'),
    (letI := F.canonicalTopologicalData.topology; Whittaker.IsGeneric ψ (k + 1) π) →
    (letI := F.canonicalTopologicalData.topology; Whittaker.IsGeneric ψ (k + 1) π') →
    SameGenericGammaFactors.{uF, uV, uW} F ψ ν.val k π π' → Nonempty (π.Equiv π')

/-- Two actual representations of `GL_(k+2)(F)` have the same gamma factor of
pairs, with respect to `ψ` and `ν`, against every actual supercuspidal
representation of `GL_(r+1)(F)` for `r ≤ k`. -/
def SameSupercuspidalGammaFactors (F : PadicField.{uF} p)
    (ψ : letI := F.canonicalTopologicalData.topology; UnitaryAdditiveCharacter F.Carrier)
    (ν : letI := F.canonicalTopologicalData.topology; letI := borel F.Carrier
      AdditiveHaarMeasure F.Carrier) (k : ℕ)
    {V V' : Type uV} [AddCommGroup V] [Module ℂ V] [AddCommGroup V'] [Module ℂ V']
    (π : Representation ℂ (Langlands.GeneralLinear (k + 1 + 1) F.Carrier) V)
    (π' : Representation ℂ (Langlands.GeneralLinear (k + 1 + 1) F.Carrier) V') : Prop :=
  ∀ r ≤ k, ∀ τ : (letI := F.canonicalTopologicalData.topology
      GeneralLinear.SupercuspidalRep.{uF, uW} (F := F.Carrier) (n := r + 1)),
    letI := F.canonicalTopologicalData.topology
    ∃ G : RationalFunctions, IsPadicPairGammaFactor F ψ ν π τ.obj.representation G ∧
      IsPadicPairGammaFactor F ψ ν π' τ.obj.representation G

/-- The referee's Remark after Henniart 1993, Theorem 1.1 (printed page 340), for
every p-adic field, every unitary additive character `ψ`, the self-dual additive
Haar measure `ν` for `ψ`, and every rank `n = k + 2 ≥ 2`: irreducible admissible
generic representations of `GL_n(F)` with the same gamma factors of pairs against
all supercuspidal representations of `GL_r(F)`, `1 ≤ r ≤ n - 1`, are equivalent. -/
def GenericSupercuspidalLocalConverseStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{uF} p)
    (ψ : letI := F.canonicalTopologicalData.topology; UnitaryAdditiveCharacter F.Carrier)
    (ν : LocalFactor.PadicAbelian.SelfDualHaar F.canonicalTopologicalData ψ) (k : ℕ)
    {V V' : Type uV} [AddCommGroup V] [Module ℂ V] [AddCommGroup V'] [Module ℂ V']
    (π : Representation ℂ (Langlands.GeneralLinear (k + 1 + 1) F.Carrier) V)
    (π' : Representation ℂ (Langlands.GeneralLinear (k + 1 + 1) F.Carrier) V'),
    (letI := F.canonicalTopologicalData.topology; Whittaker.IsGeneric ψ (k + 1) π) →
    (letI := F.canonicalTopologicalData.topology; Whittaker.IsGeneric ψ (k + 1) π') →
    SameSupercuspidalGammaFactors.{uF, uV, uW} F ψ ν.val k π π' → Nonempty (π.Equiv π')

/-- Both gamma-factor local converse statements of Henniart 1993, printed page 340:
Theorem 1.1 and the referee's Remark. -/
def GammaLocalConverseStatement : Prop :=
  GenericLocalConverseStatement.{uF, uV, uW} ∧
    GenericSupercuspidalLocalConverseStatement.{uF, uV, uW}

end Langlands.RankinSelberg
