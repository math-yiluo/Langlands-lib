import Langlands.Representation.Classification.TemperedSmoothDualityProof
import Langlands.Representation.RankinSelberg.AnalyticTemperedLFactor
import Langlands.Representation.RankinSelberg.LanglandsQuotientLFactorStatement
import Langlands.Representation.Twist.UnitaryModCenterProof

/-! # Roots of the forward and dual tempered twisted self-pair polynomials -/

noncomputable section

set_option autoImplicit false

universe u uV

namespace Langlands.BaseChange

open GeneralLinear HarmonicAnalysis LocalFactor.PadicAbelian RankinSelberg

section Local

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{u} p)

private local instance : TopologicalSpace F.Carrier := F.canonicalTopologicalData.topology
private local instance (n : ℕ) : IsTopologicalGroup (GeneralLinear n F.Carrier) :=
  F.canonicalTopologicalData.generalLinearTopologicalGroup n

private theorem isTempered_unitaryTwist {n : ℕ}
    {V : Type uV} [AddCommGroup V] [Module ℂ V]
    {ρ : Representation ℂ (GeneralLinear n F.Carrier) V}
    (hρ : F.canonicalTopologicalData.IsTempered ρ)
    (χ : GeneralLinear n F.Carrier →* ℂˣ) (ho : IsOpen (χ.ker : Set (GeneralLinear n F.Carrier)))
    (hu : ∀ g, ‖(χ g : ℂ)‖ = 1) : F.canonicalTopologicalData.IsTempered (twist χ ρ) := by
  let T := F.canonicalTopologicalData
  let := T.centralQuotientMeasurableSpace n
  intro μ _
  exact isTemperedModCenter_unitaryTwist χ ho hu μ (hρ μ)

private theorem twistedSelfPair_poleFree {n : ℕ}
    {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ (GeneralLinear (n + 1) F.Carrier) V)
    (hi : ρ.IsIrreducible) (ht : F.canonicalTopologicalData.IsTempered ρ)
    (χ : GeneralLinear (n + 1) F.Carrier →* ℂˣ)
    (ho : IsOpen (χ.ker : Set (GeneralLinear (n + 1) F.Carrier)))
    (hu : ∀ g, ‖(χ g : ℂ)‖ = 1)
    (ψ : UnitaryAdditiveCharacter F.Carrier) (ν : SelfDualHaar F.canonicalTopologicalData ψ)
    {Q : Polynomial ℂ}
    (hQ : IsPadicRankLPolynomial F ψ ν.val ρ (twist χ (smoothContragredient ρ)) Q) :
    ∀ z : ℂ, ‖z‖ < 1 → Q.eval z ≠ 0 := by
  let T := F.canonicalTopologicalData
  let A := SmoothRep.of ρ ht.isAdmissible.1
  have hid : (smoothContragredient ρ).IsIrreducible :=
    (A.isIrreducible_contragredient_iff (compactOpen_cofinal F T (n + 1)) ht.isAdmissible).mpr hi
  let d := analyticTemperedLPolynomialData F ψ ν ρ (twist χ (smoothContragredient ρ))
    hi ht ((isIrreducible_twist_iff χ _).mpr hid)
    (isTempered_unitaryTwist F ht.smoothContragredient χ ho hu)
  rw [(isPadicRankLPolynomial_succ.mp hQ).unique d.spec]
  exact d.poleFree

end Local

/-- Actual tempered pairs formed by a unitary twist of the smooth dual, and
both smooth duals of that pair, have no Euler roots in the open unit disk. -/
def TemperedSelfPairEulerRootRegionStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{u} p) (n : ℕ),
    letI := F.canonicalTopologicalData.topology
    letI := F.canonicalTopologicalData.generalLinearTopologicalGroup (n + 1)
    ∀ (V : Type uV) [AddCommGroup V] [Module ℂ V]
      (ρ : Representation ℂ (GeneralLinear (n + 1) F.Carrier) V),
      ρ.IsIrreducible → F.canonicalTopologicalData.IsTempered ρ →
    ∀ (χ : GeneralLinear (n + 1) F.Carrier →* ℂˣ),
      IsOpen (χ.ker : Set (GeneralLinear (n + 1) F.Carrier)) → (∀ g, ‖(χ g : ℂ)‖ = 1) →
    ∀ (ψ : UnitaryAdditiveCharacter F.Carrier) (ν : SelfDualHaar F.canonicalTopologicalData ψ),
      (∀ (Q : Polynomial ℂ),
        IsPadicRankLPolynomial F ψ ν.val ρ (twist χ (smoothContragredient ρ)) Q →
        ∀ z : ℂ, ‖z‖ < 1 → Q.eval z ≠ 0) ∧
      (∀ (Qd : Polynomial ℂ),
        IsPadicRankLPolynomial F ψ ν.val (smoothContragredient ρ)
          (smoothContragredient (twist χ (smoothContragredient ρ))) Qd →
        ∀ z : ℂ, ‖z‖ < 1 → Qd.eval z ≠ 0)

/-- Use smooth tempered duality and unitary twist preservation on the original
actions. The equivariant dual of a twist uses the inverse character. -/
theorem temperedSelfPairEulerRootRegion : TemperedSelfPairEulerRootRegionStatement.{u, uV} := by
  intro p _ F n
  let T := F.canonicalTopologicalData
  let := T.topology
  let := T.generalLinearTopologicalGroup (n + 1)
  intro V _ _ ρ hi ht χ ho hu ψ ν
  refine ⟨fun _ => twistedSelfPair_poleFree F ρ hi ht χ ho hu ψ ν, ?_⟩
  intro Qd hQd
  let A := SmoothRep.of ρ ht.isAdmissible.1
  have hid : (smoothContragredient ρ).IsIrreducible :=
    (A.isIrreducible_contragredient_iff (compactOpen_cofinal F T (n + 1)) ht.isAdmissible).mpr hi
  have hoinv : IsOpen ((χ⁻¹).ker : Set (GeneralLinear (n + 1) F.Carrier)) := by
    have hker : (χ⁻¹).ker = χ.ker := by ext g; simp
    rw [hker]
    exact ho
  have huinv (g : GeneralLinear (n + 1) F.Carrier) : ‖(χ⁻¹ g : ℂ)‖ = 1 := by
    simpa using hu g
  let e := smoothContragredientTwistEquiv χ (smoothContragredient ρ) ho
  have hQd' := (IsPadicSymmetricLPolynomial.congr_equiv (Representation.Equiv.refl _) e).mp
    (isPadicRankLPolynomial_succ.mp hQd)
  exact twistedSelfPair_poleFree F (smoothContragredient ρ) hid ht.smoothContragredient
    χ⁻¹ hoinv huinv ψ ν (isPadicRankLPolynomial_succ.mpr hQd')

end Langlands.BaseChange
