import Langlands.Representation.RankinSelberg.LanglandsQuotientLFactorStatement
import Langlands.Representation.Classification.Segments
import Langlands.Representation.Smooth.Contragredient.Definitions

/-!
# L- and gamma factors of pairs of segment representations `St_n(ρ)`

Henniart 2002, §2.6, printed page 595. For irreducible supercuspidal `ρ`, `ρ'` and
`n, n' ≥ 1`, `St_n(ρ)` is the unique irreducible quotient of the normalized
induced representation `i(ρ, νρ, …, ν^(n-1) ρ)`, and

* `L(s, St_n(ρ) × St_n'(ρ')) = ∏_j L(s, ν^(n+n'-1-j) ρ × ρ')`,
* `L(s, St_n(ρ)^∨ × St_n'(ρ')^∨) = ∏_j L(s, ν^(1-j) ρ^∨ × ρ'^∨)`,

with `j` from `1` to `min(n, n')`, and

* `γ(s, St_n(ρ) × St_n'(ρ'), ψ) = ∏_(i=1)^n ∏_(j=1)^n' γ(s, ν^(i+j-2) ρ × ρ', ψ)`.

The special representations are recorded by the published relation
`IsSegmentHead`, and the factors by the rank-symmetric relations of
`PadicPairFactors`, through the arbitrary-rank wrappers `IsPadicRankLPolynomial`
(Section 9 module) and `IsPadicRankGammaFactor` (defined here).
-/

noncomputable section

namespace Langlands.RankinSelberg

open MeasureTheory HarmonicAnalysis Whittaker GeneralLinear QuotientIntegration Polynomial

universe uF uV uW

variable {p : ℕ} [Fact p.Prime]

/-- `γ(s, π × σ, ψ) = G(q^(-s))` for representations `π` of `GL_n(F)` and `σ` of
`GL_t(F)` of arbitrary rank: the relation `IsPadicSymmetricGammaFactor` when both
ranks are positive, and `False` when one of them is zero. -/
def IsPadicRankGammaFactor (F : PadicField.{uF} p)
    (ψ : letI := F.canonicalTopologicalData.topology; UnitaryAdditiveCharacter F.Carrier)
    (ν : letI := F.canonicalTopologicalData.topology; letI := borel F.Carrier
      AdditiveHaarMeasure F.Carrier)
    {n t : ℕ} {V : Type uV} {W : Type uW} [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W]
    (π : Representation ℂ (Langlands.GeneralLinear n F.Carrier) V)
    (σ : Representation ℂ (Langlands.GeneralLinear t F.Carrier) W)
    (G : RationalFunctions) : Prop :=
  match n, t, π, σ with
  | _ + 1, _ + 1, π, σ => IsPadicSymmetricGammaFactor F ψ ν π σ G
  | _, _, _, _ => False

section Rank

variable {F : PadicField.{uF} p}
  {ψ : letI := F.canonicalTopologicalData.topology; UnitaryAdditiveCharacter F.Carrier}
  {ν : letI := F.canonicalTopologicalData.topology; letI := borel F.Carrier
    AdditiveHaarMeasure F.Carrier}
  {V : Type uV} {W : Type uW} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

theorem isPadicRankGammaFactor_succ {r k : ℕ}
    {π : Representation ℂ (Langlands.GeneralLinear (r + 1) F.Carrier) V}
    {σ : Representation ℂ (Langlands.GeneralLinear (k + 1) F.Carrier) W}
    {G : RationalFunctions} :
    IsPadicRankGammaFactor F ψ ν π σ G ↔ IsPadicSymmetricGammaFactor F ψ ν π σ G :=
  Iff.rfl

/-- The gamma factor of a pair of arbitrary ranks is unique. -/
theorem IsPadicRankGammaFactor.unique {n t : ℕ}
    {π : Representation ℂ (Langlands.GeneralLinear n F.Carrier) V}
    {σ : Representation ℂ (Langlands.GeneralLinear t F.Carrier) W}
    {G G' : RationalFunctions}
    (h : IsPadicRankGammaFactor F ψ ν π σ G) (h' : IsPadicRankGammaFactor F ψ ν π σ G') :
    G = G' := by
  match n, t, π, σ, h, h' with
  | _ + 1, _ + 1, _, _, h, h' => exact IsPadicSymmetricGammaFactor.unique h h'

end Rank

/-- Henniart 2002, §2.6, printed page 595, first display: let `St_n(ρ)` be the
unique irreducible quotient of `i(ρ, νρ, …, ν^(n-1) ρ)` and `St_n'(ρ')` that of
`i(ρ', νρ', …, ν^(n'-1) ρ')`, for irreducible supercuspidal `ρ`, `ρ'`. Then
`L(s, St_n(ρ) × St_n'(ρ')) = ∏_j L(s, ν^(n+n'-1-j) ρ × ρ')`, `1 ≤ j ≤ min(n, n')`.
The index `j : Fin (min n n')` here is Henniart's `j - 1`. -/
def SegmentHeadLFactorStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{uF} p)
    (ψ : letI := F.canonicalTopologicalData.topology; UnitaryAdditiveCharacter F.Carrier)
    (ν : LocalFactor.PadicAbelian.SelfDualHaar F.canonicalTopologicalData ψ)
    (Δ : F.canonicalTopologicalData.Segment.{uV, uF})
    (Δ' : F.canonicalTopologicalData.Segment.{uW, uF})
    (π : letI := F.canonicalTopologicalData.topology
      SmoothRep.{0, uF, max uF uV} ℂ (Langlands.GeneralLinear Δ.degree F.Carrier))
    (σ : letI := F.canonicalTopologicalData.topology
      SmoothRep.{0, uF, max uF uW} ℂ (Langlands.GeneralLinear Δ'.degree F.Carrier))
    (A : letI := F.canonicalTopologicalData.topology
      GeneralLinear.SupercuspidalRep.{uF, uV} (F := F.Carrier) (n := Δ.rank))
    (A' : letI := F.canonicalTopologicalData.topology
      GeneralLinear.SupercuspidalRep.{uF, uW} (F := F.Carrier) (n := Δ'.rank)),
    F.canonicalTopologicalData.IsSegmentHead Δ π →
    F.canonicalTopologicalData.IsSegmentHead Δ' σ →
    Δ.base.IsRepresentedBy A → Δ'.base.IsRepresentedBy A' →
    letI := F.canonicalTopologicalData.topology
    ∃ (P : ℂ[X]) (Q : Fin (min Δ.length Δ'.length) → ℂ[X]),
      IsPadicRankLPolynomial F ψ ν.val π.representation σ.representation P ∧
      (∀ j : Fin (min Δ.length Δ'.length), IsPadicRankLPolynomial F ψ ν.val
        (realPowerTwist (F.canonicalTopologicalData.determinantNorm Δ.rank)
          ((Δ.length : ℝ) + Δ'.length - 2 - (j : ℕ)) A.obj.representation)
        A'.obj.representation (Q j)) ∧
      P = ∏ j, Q j

/-- Henniart 2002, §2.6, printed page 595, second display: with the notation of
`SegmentHeadLFactorStatement`,
`L(s, St_n(ρ)^∨ × St_n'(ρ')^∨) = ∏_j L(s, ν^(1-j) ρ^∨ × ρ'^∨)`,
`1 ≤ j ≤ min(n, n')`, where `^∨` is the smooth contragredient. The index
`j : Fin (min n n')` here is Henniart's `j - 1`, so the exponent is `-j`. -/
def SegmentHeadContragredientLFactorStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{uF} p)
    (ψ : letI := F.canonicalTopologicalData.topology; UnitaryAdditiveCharacter F.Carrier)
    (ν : LocalFactor.PadicAbelian.SelfDualHaar F.canonicalTopologicalData ψ)
    (Δ : F.canonicalTopologicalData.Segment.{uV, uF})
    (Δ' : F.canonicalTopologicalData.Segment.{uW, uF})
    (π : letI := F.canonicalTopologicalData.topology
      SmoothRep.{0, uF, max uF uV} ℂ (Langlands.GeneralLinear Δ.degree F.Carrier))
    (σ : letI := F.canonicalTopologicalData.topology
      SmoothRep.{0, uF, max uF uW} ℂ (Langlands.GeneralLinear Δ'.degree F.Carrier))
    (A : letI := F.canonicalTopologicalData.topology
      GeneralLinear.SupercuspidalRep.{uF, uV} (F := F.Carrier) (n := Δ.rank))
    (A' : letI := F.canonicalTopologicalData.topology
      GeneralLinear.SupercuspidalRep.{uF, uW} (F := F.Carrier) (n := Δ'.rank)),
    F.canonicalTopologicalData.IsSegmentHead Δ π →
    F.canonicalTopologicalData.IsSegmentHead Δ' σ →
    Δ.base.IsRepresentedBy A → Δ'.base.IsRepresentedBy A' →
    letI := F.canonicalTopologicalData.topology
    haveI := F.canonicalTopologicalData.generalLinearTopologicalGroup Δ.degree
    haveI := F.canonicalTopologicalData.generalLinearTopologicalGroup Δ'.degree
    haveI := F.canonicalTopologicalData.generalLinearTopologicalGroup Δ.rank
    haveI := F.canonicalTopologicalData.generalLinearTopologicalGroup Δ'.rank
    ∃ (P : ℂ[X]) (Q : Fin (min Δ.length Δ'.length) → ℂ[X]),
      IsPadicRankLPolynomial F ψ ν.val (smoothContragredient π.representation)
        (smoothContragredient σ.representation) P ∧
      (∀ j : Fin (min Δ.length Δ'.length), IsPadicRankLPolynomial F ψ ν.val
        (realPowerTwist (F.canonicalTopologicalData.determinantNorm Δ.rank)
          (-((j : ℕ) : ℝ)) (smoothContragredient A.obj.representation))
        (smoothContragredient A'.obj.representation) (Q j)) ∧
      P = ∏ j, Q j

/-- Henniart 2002, §2.6, printed page 595, third display: with the notation of
`SegmentHeadLFactorStatement`,
`γ(s, St_n(ρ) × St_n'(ρ'), ψ) = ∏_(i=1)^n ∏_(j=1)^n' γ(s, ν^(i+j-2) ρ × ρ', ψ)`.
The indices `i : Fin n`, `j : Fin n'` here are Henniart's `i - 1`, `j - 1`, so
the exponent is `i + j`. -/
def SegmentHeadGammaFactorStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{uF} p)
    (ψ : letI := F.canonicalTopologicalData.topology; UnitaryAdditiveCharacter F.Carrier)
    (ν : LocalFactor.PadicAbelian.SelfDualHaar F.canonicalTopologicalData ψ)
    (Δ : F.canonicalTopologicalData.Segment.{uV, uF})
    (Δ' : F.canonicalTopologicalData.Segment.{uW, uF})
    (π : letI := F.canonicalTopologicalData.topology
      SmoothRep.{0, uF, max uF uV} ℂ (Langlands.GeneralLinear Δ.degree F.Carrier))
    (σ : letI := F.canonicalTopologicalData.topology
      SmoothRep.{0, uF, max uF uW} ℂ (Langlands.GeneralLinear Δ'.degree F.Carrier))
    (A : letI := F.canonicalTopologicalData.topology
      GeneralLinear.SupercuspidalRep.{uF, uV} (F := F.Carrier) (n := Δ.rank))
    (A' : letI := F.canonicalTopologicalData.topology
      GeneralLinear.SupercuspidalRep.{uF, uW} (F := F.Carrier) (n := Δ'.rank)),
    F.canonicalTopologicalData.IsSegmentHead Δ π →
    F.canonicalTopologicalData.IsSegmentHead Δ' σ →
    Δ.base.IsRepresentedBy A → Δ'.base.IsRepresentedBy A' →
    letI := F.canonicalTopologicalData.topology
    ∃ (G : RationalFunctions) (H : Fin Δ.length → Fin Δ'.length → RationalFunctions),
      IsPadicRankGammaFactor F ψ ν.val π.representation σ.representation G ∧
      (∀ (i : Fin Δ.length) (j : Fin Δ'.length), IsPadicRankGammaFactor F ψ ν.val
        (realPowerTwist (F.canonicalTopologicalData.determinantNorm Δ.rank)
          (((i : ℕ) + (j : ℕ) : ℕ) : ℝ) A.obj.representation)
        A'.obj.representation (H i j)) ∧
      G = ∏ i, ∏ j, H i j

/-- The local factors of pairs of segment representations of Henniart 2002, §2.6:
the conjunction of the two L-factor formulas and the gamma-factor formula. -/
def SegmentHeadFactorStatement : Prop :=
  SegmentHeadLFactorStatement.{uF, uV, uW} ∧
    SegmentHeadContragredientLFactorStatement.{uF, uV, uW} ∧
    SegmentHeadGammaFactorStatement.{uF, uV, uW}

end Langlands.RankinSelberg
