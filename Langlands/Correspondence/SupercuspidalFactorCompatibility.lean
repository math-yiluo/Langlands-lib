import Langlands.Correspondence.ArithmeticFactors
import Langlands.Representation.RankinSelberg.PadicPairFactors

/-!
# Pair-factor compatibility of supercuspidal families

The Rankin-Selberg side uses the published JPSS relations for either rank order,
lifted to supercuspidal isomorphism classes. The Weil-Deligne side uses the
arithmetic pair L-factor and the epsilon value of a supplied local-constant
system. No additive character, measure or system is chosen.
-/

noncomputable section

namespace Langlands.Correspondence

universe uF uP uA uV uW

open Polynomial LocalFactor LocalFactor.CommonClosure

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

/-- `L(s, π × τ) = 1 / P(q^(-s))` for supercuspidal classes of ranks `r + 1` and
`n + 1`, in either rank order: the published symmetric JPSS relation on
representatives. Representation equivalences preserve it. -/
def IsSupercuspidalPairLPolynomial (ψ : NontrivialAdditiveCharacter F)
    (ν : LocalAdditiveHaarMeasure F) {r n : ℕ}
    (π : PadicField.SupercuspidalClass.{uV, uF} F (r + 1) (Nat.succ_pos r))
    (τ : PadicField.SupercuspidalClass.{uW, uF} F (n + 1) (Nat.succ_pos n))
    (P : ℂ[X]) : Prop :=
  letI := F.canonicalTopologicalData.topology
  Quotient.lift₂
    (fun (A : GeneralLinear.SupercuspidalRep.{uF, uV} (F := F.Carrier) (n := r + 1))
        (B : GeneralLinear.SupercuspidalRep.{uF, uW} (F := F.Carrier) (n := n + 1)) =>
      RankinSelberg.IsPadicSymmetricLPolynomial F ψ ν
        A.obj.representation B.obj.representation P)
    (by
      rintro A B A' B' ⟨i⟩ ⟨j⟩
      exact propext (RankinSelberg.IsPadicSymmetricLPolynomial.congr_equiv
        (SmoothRep.equivOfIso (GeneralLinear.supercuspidalProperty.ι.mapIso i))
        (SmoothRep.equivOfIso (GeneralLinear.supercuspidalProperty.ι.mapIso j))))
    π τ

/-- `ε(s, π × τ, ψ) = c q^(-ms)`, `e = (c, m)`, for supercuspidal classes of
ranks `r + 1` and `n + 1`, in either rank order: the published symmetric JPSS
relation on representatives. Representation equivalences preserve it. -/
def IsSupercuspidalPairEpsilonFactor (ψ : NontrivialAdditiveCharacter F)
    (ν : LocalAdditiveHaarMeasure F) {r n : ℕ}
    (π : PadicField.SupercuspidalClass.{uV, uF} F (r + 1) (Nat.succ_pos r))
    (τ : PadicField.SupercuspidalClass.{uW, uF} F (n + 1) (Nat.succ_pos n))
    (e : ℂˣ × ℤ) : Prop :=
  letI := F.canonicalTopologicalData.topology
  Quotient.lift₂
    (fun (A : GeneralLinear.SupercuspidalRep.{uF, uV} (F := F.Carrier) (n := r + 1))
        (B : GeneralLinear.SupercuspidalRep.{uF, uW} (F := F.Carrier) (n := n + 1)) =>
      RankinSelberg.IsPadicSymmetricEpsilonFactor F ψ ν
        A.obj.representation B.obj.representation e)
    (by
      rintro A B A' B' ⟨i⟩ ⟨j⟩
      exact propext (RankinSelberg.IsPadicSymmetricEpsilonFactor.congr_equiv
        (SmoothRep.equivOfIso (GeneralLinear.supercuspidalProperty.ι.mapIso i))
        (SmoothRep.equivOfIso (GeneralLinear.supercuspidalProperty.ι.mapIso j))))
    π τ

/-- Pair L- and epsilon-factor compatibility of a supercuspidal map for the
supplied local-constant system. For every nontrivial `ψ`, all ranks `r + 1` and
`n + 1` and all irreducible Weil classes `σ`, `τ`: a self-dual measure exists,
and for every self-dual measure `ν` the JPSS L-polynomial of the image pair
gives the arithmetic L-factor of `σ ⊗ τ`, and some `c q^(-ms)` is both the JPSS
epsilon factor and the arithmetic epsilon factor. -/
def SupercuspidalPairFactorCompatibility (eC : ReciprocityFamily F)
    (ε : NonabelianSystem.Assignment.{uF, uP} F) (hε : NonabelianSystem.IsSystem F eC ε)
    (c : SupercuspidalMap.{uF, uP, uA} F) : Prop :=
  ∀ (ψ : NontrivialAdditiveCharacter F) (r n : ℕ)
    (σ : IrreducibleWeilClass.{uF, uP} F r.succPNat)
    (τ : IrreducibleWeilClass.{uF, uP} F n.succPNat),
    (∃ ν : LocalAdditiveHaarMeasure F, IsSelfDualMeasure F ψ ν) ∧
    ∀ ν : LocalAdditiveHaarMeasure F, IsSelfDualMeasure F ψ ν →
      (∃ P : ℂ[X],
        IsSupercuspidalPairLPolynomial F ψ ν (c r.succPNat σ) (c n.succPNat τ) P ∧
          arithmeticPairLFactor F (weilPairClass F σ) (weilPairClass F τ) =
            (algebraMap ℂ[X] (RatFunc ℂ) P)⁻¹) ∧
      ∃ e : ℂˣ × ℤ,
        IsSupercuspidalPairEpsilonFactor F ψ ν (c r.succPNat σ) (c n.succPNat τ) e ∧
          IsArithmeticPairEpsilonFactor F eC ε hε ψ (weilPairClass F σ) (weilPairClass F τ)
            e.1 e.2

/-- Pair-factor compatibility relative to a rank-one reciprocity candidate: some
local-constant system, whose reciprocity family has `e` as its base component,
satisfies `SupercuspidalPairFactorCompatibility`. -/
def SupercuspidalFactorCompatibility (e : ReciprocityCandidate F)
    (c : SupercuspidalMap.{uF, uP, uA} F) : Prop :=
  ∃ (eC : ReciprocityFamily F) (ε : NonabelianSystem.Assignment.{uF, uP} F)
    (hε : NonabelianSystem.IsSystem F eC ε),
    IsBaseReciprocity F e eC ∧ SupercuspidalPairFactorCompatibility F eC ε hε c

end Langlands.Correspondence
