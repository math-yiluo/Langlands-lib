import Langlands.Automorphic.AssociatedGammaAutomorphicFamily
import Langlands.Correspondence.AutomorphicActualGamma
import Langlands.Global.Factors.CuspidalPairPartialGammaReduction
import Langlands.Representation.RankinSelberg.HighlyRamified.Duality
import Langlands.Representation.RankinSelberg.WhittakerTypeHighlyRamifiedProof

/-! # Finite Euler denominators under ramified twists of a cuspidal pair -/

noncomputable section

set_option autoImplicit false

universe u uQ

namespace Langlands.Global.CuspidalPairFunctionalEquation

open Langlands.Automorphic Langlands.Global.CompletionPadic
open Langlands.LocalFactor Langlands.RankinSelberg Langlands.Whittaker
open scoped NumberField

variable {F : Type u} [Field F] [NumberField F] [CompactSpace (AdeleQuotient F)]

local instance rationalAddCommGroup (n : ℕ) :
    AddCommGroup (RationalInvariantFunctions F n) := Submodule.addCommGroup _
local instance continuousAddCommGroup (n : ℕ) :
    AddCommGroup (ContinuousRationalFunctions F n) := Submodule.addCommGroup _
local instance smoothAddCommGroup (n : ℕ) :
    AddCommGroup (FiniteSmoothRationalFunctions F n) := Submodule.addCommGroup _
local instance formAddCommGroup (n : ℕ) :
    AddCommGroup (AutomorphicForms F n) := Submodule.addCommGroup _
local instance localComponentAddCommGroup {n : ℕ} {v : FinitePlace F}
    (A : LocalRealization F n v) : AddCommGroup A.Space := Submodule.addCommGroup _

set_option maxHeartbeats 500000 in
private theorem isPadicSymmetricLPolynomial_of_cuspidalPair
    {r t : ℕ} {T : CuspidalOperatorRealization F r} {T' : CuspidalOperatorRealization F t}
    (P : CuspidalSpectralPresentation.{u,uQ} T) (P' : CuspidalSpectralPresentation.{u,uQ} T')
    (hP : HasIrreducibleAdmissibleComponents P) (hP' : HasIrreducibleAdmissibleComponents P')
    (v : FinitePlace F) (ψ : Correspondence.NontrivialAdditiveCharacter (padicField v))
    (ν : PadicAbelian.SelfDualHaar (padicField v).canonicalTopologicalData ψ) {A : Polynomial ℂ}
    (hA : Correspondence.IsAutomorphicPairLPolynomial (padicField v) ψ ν.val
      (localClass P hP v) (localClass P' hP' v) A) :
    letI := (padicField v).canonicalTopologicalData.topology
    letI := (padicField v).canonicalGeneralLinearTopology (r + 1)
    letI := (padicField v).canonicalGeneralLinearTopology (t + 1)
    IsPadicSymmetricLPolynomial (padicField v) ψ ν.val
      ((P.localComponent v).padicObject (hP v).1 (hP v).2).obj.representation
      ((P'.localComponent v).padicObject (hP' v).1 (hP' v).2).obj.representation A := by
  let := (padicField v).canonicalTopologicalData.topology
  let := (padicField v).canonicalGeneralLinearTopology (r + 1)
  let := (padicField v).canonicalGeneralLinearTopology (t + 1)
  let X := (P.localComponent v).padicObject (hP v).1 (hP v).2
  let Y := (P'.localComponent v).padicObject (hP' v).1 (hP' v).2
  have hL := (Correspondence.isAutomorphicPairLPolynomial_iff (padicField v) X Y X.obj Y.obj
    (Representation.Equiv.refl _) (Representation.Equiv.refl _)).mp hA
  have hgen := CuspidalPairPartialGamma.localGenericity F r T P v (hP v).1 (hP v).2 ψ
  have hgen' := CuspidalPairPartialGamma.localGenericity F t T' P' v (hP' v).1 (hP' v).2 ψ
  exact hL.isPadicSymmetricLPolynomial (ν := ν) hgen hgen'

set_option maxHeartbeats 1000000 in
private theorem exists_ramified_lPolynomial_eq_one
    {r t : ℕ} {T : CuspidalOperatorRealization F r} {T' : CuspidalOperatorRealization F t}
    (P : CuspidalSpectralPresentation.{u,uQ} T) (P' : CuspidalSpectralPresentation.{u,uQ} T')
    (hP : HasIrreducibleAdmissibleComponents P) (hP' : HasIrreducibleAdmissibleComponents P')
    (v : FinitePlace F) (ψ : Correspondence.NontrivialAdditiveCharacter (padicField v))
    (ν : PadicAbelian.SelfDualHaar (padicField v).canonicalTopologicalData ψ) :
    ∃ b : ℕ, ∀ χ : HeckeCharacter F,
      b ≤ (padicField v).canonicalTopologicalData.multiplicativeConductor
        (quasicharacterBase v (χ.finiteComponent v)) →
      ∀ A : Polynomial ℂ,
        Correspondence.IsAutomorphicPairLPolynomial (padicField v) ψ ν.val
          (localClass (P.heckeDeterminantTwist χ)
            (P.heckeDeterminantTwist_hasIrreducibleAdmissibleComponents χ hP) v)
          (localClass P' hP' v) A → A = 1 := by
  let K := padicField v
  let := K.canonicalTopologicalData.topology
  let := K.canonicalGeneralLinearTopology (r + 1)
  let := K.canonicalGeneralLinearTopology (t + 1)
  let π := ((P.localComponent v).padicObject (hP v).1 (hP v).2).obj.representation
  let ρ := ((P'.localComponent v).padicObject (hP' v).1 (hP' v).2).obj.representation
  have hπ := CuspidalPairPartialGamma.localGenericity F r T P v (hP v).1 (hP v).2 ψ
  have hρ := CuspidalPairPartialGamma.localGenericity F t T' P' v (hP' v).1 (hP' v).2 ψ
  obtain ⟨b, hb⟩ := whittakerTypeHighlyRamifiedLVanishing (residuePrime v) K ψ ν r t π ρ
    (isOfWhittakerType_of_isGeneric K hπ) (isOfWhittakerType_of_isGeneric K hρ)
  refine ⟨b, fun χ hχ A hA => ?_⟩
  let η := quasicharacterBase v (χ.finiteComponent v)
  have hOne := hb η hχ
  let Pχ := P.heckeDeterminantTwist χ
  let hPχ := P.heckeDeterminantTwist_hasIrreducibleAdmissibleComponents χ hP
  have hPoly := isPadicSymmetricLPolynomial_of_cuspidalPair Pχ P' hPχ hP' v ψ ν hA
  let e := ((P.localComponent v).heckeDeterminantTwistRepresentationEquiv χ).trans
    (P.heckeDeterminantTwistLocalComponentEquiv χ v).symm
  change IsPadicSymmetricLPolynomial K ψ ν.val
    (twist (Correspondence.determinantQuasiCharacter K r.succPNat η) π) ρ 1 at hOne
  rw [CuspidalSpectralPresentation.determinantQuasiCharacter_quasicharacterBase (r := r) χ v]
    at hOne
  exact hPoly.unique ((IsPadicSymmetricLPolynomial.congr_equiv e (Representation.Equiv.refl ρ)).mp hOne)

/-- A high-conductor determinant twist of the first member of a cuspidal pair
makes both the finite forward and contragredient denominators equal to one. -/
def CuspidalPairRamifiedEulerVanishingStatement : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F] [CompactSpace (AdeleQuotient F)]
    {ψ : HarmonicAnalysis.UnitaryAdditiveCharacter (Adeles F)} {r t : ℕ}
    (D : AutomorphicTwistSetup.{u,uQ} ψ r t) (v : FinitePlace F),
    ∃ b : ℕ, ∀ χ : HeckeCharacter F,
      b ≤ (padicField v).canonicalTopologicalData.multiplicativeConductor
        (quasicharacterBase v (χ.finiteComponent v)) →
      (D.twistedChoice χ).lPolynomial v = 1 ∧ (D.twistedChoice χ).dualLPolynomial v = 1

/-- Use the maximum of the forward and contragredient thresholds. Inversion
of the character preserves the local multiplicative conductor. -/
theorem cuspidalPairRamifiedEulerVanishing : CuspidalPairRamifiedEulerVanishingStatement.{u,uQ} := by
  intro F _ _ _ ψ r t D v
  let ν : PadicAbelian.SelfDualHaar (padicField v).canonicalTopologicalData (D.additive v) :=
    ⟨D.measure v, D.measure_spec v⟩
  obtain ⟨b, hb⟩ := exists_ramified_lPolynomial_eq_one D.P D.P' D.h D.h' v (D.additive v) ν
  obtain ⟨c, hc⟩ := exists_ramified_lPolynomial_eq_one D.Pd D.Pd' D.hd D.hd' v (D.additive v) ν
  refine ⟨max b c, fun χ hχ => ⟨hb χ ((le_max_left b c).trans hχ) _ (D.finiteData_specs χ v).1, ?_⟩⟩
  have hχinv : c ≤ (padicField v).canonicalTopologicalData.multiplicativeConductor
      (quasicharacterBase v (χ⁻¹.finiteComponent v)) := by
    change c ≤ (padicField v).canonicalTopologicalData.multiplicativeConductor
      ((quasicharacterBase v (χ.finiteComponent v))⁻¹)
    rw [HighlyRamified.multiplicativeConductor_inv]
    exact (le_max_right b c).trans hχ
  exact hc χ⁻¹ hχinv _ (D.finiteData_specs χ v).2.1

end Langlands.Global.CuspidalPairFunctionalEquation
