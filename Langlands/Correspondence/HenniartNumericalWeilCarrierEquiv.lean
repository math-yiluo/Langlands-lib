import Langlands.Correspondence.HenniartNumericalCarrierEquiv
import Langlands.Correspondence.HenniartWeilExponentComparison
import Langlands.Weil.Representation.ContinuousIrreducibleCarrierEquiv

/-!
# Changing the Weil carrier universe in Henniart's numerical theorem

The Weil class bijection preserves the Artin conductor and commutes with the
unramified twists used in the numerical injection predicate. Precomposition
therefore identifies the numerical injections at two Weil carrier levels.
Together with the supercuspidal comparison, this reduces numerical
surjectivity to the case where both carrier levels are zero.
-/

noncomputable section

set_option autoImplicit false

universe uK uW uV uX uY

namespace Langlands.Henniart

open Correspondence

namespace Numerical

variable {p : ℕ} [Fact p.Prime] (K : PadicField.{uK} p)

/-- Change carriers in the irreducible Weil classes of a fixed rank. -/
abbrev weilClassCarrierEquiv (n : ℕ+) :
    IrreducibleWeilClass.{uK, uW} K n ≃ IrreducibleWeilClass.{uK, uX} K n :=
  FiniteRepresentation.continuousIrreducibleCarrierEquiv (Weil.Local.localWeilGroup K) n

/-- The Artin conductor relation is invariant under the Weil class bijection. -/
theorem hasArtinConductor_weilClassCarrierEquiv_iff {k : ℕ}
    (σ : IrreducibleWeilClass.{uK, uW} K k.succPNat) (a : ℕ) :
    HasArtinConductor K (weilClassCarrierEquiv.{uK, uW, uX} K k.succPNat σ) a ↔
      HasArtinConductor K σ a := by
  let τ := weilClassCarrierEquiv.{uK, uW, uX} K k.succPNat σ
  obtain ⟨A, hA⟩ := Quotient.exists_rep (weilClassForget K σ)
  obtain ⟨B, hB⟩ := Quotient.exists_rep (weilClassForget K τ)
  change FiniteRepresentation.classOf A = _ at hA
  change FiniteRepresentation.classOf B = _ at hB
  obtain ⟨e⟩ := (FiniteRepresentation.continuousIrreducibleCarrierEquiv_rep_iff
    σ A B hA.symm).mp hB.symm
  change HasArtinConductor K τ a ↔ HasArtinConductor K σ a
  rw [hasArtinConductor_iff_artinExponent_eq K hA a,
    hasArtinConductor_iff_artinExponent_eq K hB a,
    Weil.Local.artinExponent_eq_of_equiv e]

/-- The Weil class bijection commutes with the geometrically normalized
unramified character twists. -/
theorem weilClassCarrierEquiv_unramifiedTwist {k : ℕ} (z : ℂˣ)
    (σ : IrreducibleWeilClass.{uK, uW} K k.succPNat) :
    weilClassCarrierEquiv.{uK, uW, uX} K k.succPNat (weilUnramifiedTwist K k z σ) =
      weilUnramifiedTwist K k z (weilClassCarrierEquiv K k.succPNat σ) :=
  FiniteRepresentation.continuousIrreducibleCarrierEquiv_twist
    (Weil.Local.unramifiedCharacter (Weil.Local.localDegree K) z) σ

/-- Precomposing with the Weil class bijection preserves and reflects the
numerical injection conditions. -/
theorem isNumericalInjection_comp_weilClassCarrierEquiv_iff {k : ℕ}
    (φ : IrreducibleWeilClass.{uK, uW} K k.succPNat →
      SupercuspidalAutomorphicClass.{uK, uV} K k.succPNat) :
    IsNumericalInjection K (φ ∘ weilClassCarrierEquiv.{uK, uX, uW} K k.succPNat) ↔
      IsNumericalInjection K φ := by
  let e := weilClassCarrierEquiv.{uK, uX, uW} K k.succPNat
  change IsNumericalInjection K (φ ∘ e) ↔ IsNumericalInjection K φ
  refine and_congr (Function.Injective.of_comp_iff' φ e.bijective) (and_congr ?_ ?_)
  · constructor
    · intro h σ a ha
      obtain ⟨τ, rfl⟩ := e.surjective σ
      exact h τ a ((hasArtinConductor_weilClassCarrierEquiv_iff K τ a).mp ha)
    · intro h σ a ha
      exact h (e σ) a ((hasArtinConductor_weilClassCarrierEquiv_iff K σ a).mpr ha)
  · have he (z : ℂˣ) (σ : IrreducibleWeilClass.{uK, uX} K k.succPNat) :
        e (weilUnramifiedTwist K k z σ) = weilUnramifiedTwist K k z (e σ) :=
      weilClassCarrierEquiv_unramifiedTwist K z σ
    constructor
    · intro h z σ
      obtain ⟨τ, rfl⟩ := e.surjective σ
      simpa only [Function.comp_apply, he] using h z τ
    · intro h z σ
      simpa only [Function.comp_apply, he] using h z (e σ)

/-- At fixed rank and supercuspidal carrier level, precomposition identifies
the numerical injections at any two Weil carrier levels. -/
def numericalInjectionWeilCarrierEquiv (k : ℕ) :
    {φ : IrreducibleWeilClass.{uK, uW} K k.succPNat →
        SupercuspidalAutomorphicClass.{uK, uV} K k.succPNat // IsNumericalInjection K φ} ≃
    {φ : IrreducibleWeilClass.{uK, uX} K k.succPNat →
        SupercuspidalAutomorphicClass.{uK, uV} K k.succPNat // IsNumericalInjection K φ} :=
  (Equiv.arrowCongr (weilClassCarrierEquiv.{uK, uX, uW} K k.succPNat).symm
    (Equiv.refl _)).subtypeEquiv
      fun φ => (isNumericalInjection_comp_weilClassCarrierEquiv_iff K φ).symm

/-- The injection after changing the Weil carrier has the same surjectivity
property as the original. -/
theorem surjective_numericalInjectionWeilCarrierEquiv_iff {k : ℕ}
    (φ : {φ : IrreducibleWeilClass.{uK, uW} K k.succPNat →
        SupercuspidalAutomorphicClass.{uK, uV} K k.succPNat // IsNumericalInjection K φ}) :
    Function.Surjective ((numericalInjectionWeilCarrierEquiv.{uK, uW, uV, uX} K k) φ).val ↔
      Function.Surjective φ.val :=
  Function.Surjective.of_comp_iff φ.val
    (weilClassCarrierEquiv.{uK, uX, uW} K k.succPNat).surjective

end Numerical

open Numerical

private theorem numericalSurjectivity_of_weilCarrierEquiv
    (h : NumericalSurjectivityStatement.{uK, uW, uV}) :
    NumericalSurjectivityStatement.{uK, uX, uV} := by
  intro p hp K k φ hφ
  let ψ := numericalInjectionWeilCarrierEquiv.{uK, uX, uV, uW} K k ⟨φ, hφ⟩
  exact (surjective_numericalInjectionWeilCarrierEquiv_iff K ⟨φ, hφ⟩).mp
    (h p K k ψ.val ψ.property)

/-- Numerical surjectivity is independent of the Weil carrier universe. -/
theorem numericalSurjectivity_weilCarrierEquiv_iff :
    NumericalSurjectivityStatement.{uK, uW, uV} ↔
      NumericalSurjectivityStatement.{uK, uX, uV} :=
  ⟨numericalSurjectivity_of_weilCarrierEquiv, numericalSurjectivity_of_weilCarrierEquiv⟩

/-- The two representation carrier universes can both change, while keeping
the universe of the fields fixed. -/
theorem numericalSurjectivity_representationUniverses_iff :
    NumericalSurjectivityStatement.{uK, uW, uV} ↔
      NumericalSurjectivityStatement.{uK, uX, uY} :=
  numericalSurjectivity_weilCarrierEquiv_iff.{uK, uW, uV, uX}.trans
    numericalSurjectivity_carrierEquiv_iff.{uK, uX, uV, uY}

/-- Numerical surjectivity at both carrier levels zero suffices for
surjectivity at any independent carrier levels. -/
theorem numericalSurjectivity_of_carrierUniversesZero
    (h : NumericalSurjectivityStatement.{uK, 0, 0}) :
    NumericalSurjectivityStatement.{uK, uW, uV} :=
  numericalSurjectivity_representationUniverses_iff.mp h

end Langlands.Henniart
