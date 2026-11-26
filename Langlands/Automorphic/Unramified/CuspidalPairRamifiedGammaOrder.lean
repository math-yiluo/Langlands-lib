import Langlands.Automorphic.AssociatedGammaAutomorphicFamily
import Langlands.Global.Factors.CuspidalPairPartialGammaReduction
import Langlands.LocalFactor.UnitaryRationalGamma
import Langlands.Representation.RankinSelberg.HighlyRamified.Duality
import Langlands.Representation.RankinSelberg.WhittakerTypeHighlyRamifiedProof

/-! # Gamma orders under sufficiently ramified twists of cuspidal pairs -/

noncomputable section

set_option autoImplicit false

universe u uQ

namespace Langlands.Global.CuspidalPairFunctionalEquation

open Langlands.Automorphic Langlands.Global.CompletionPadic
open Langlands.Global.FunctionalEquationComparison
open Langlands.LocalFactor Langlands.RankinSelberg Langlands.Whittaker
open scoped NumberField

variable {F : Type u} [Field F] [NumberField F] [CompactSpace (AdeleQuotient F)]

local instance ramifiedRationalAddCommGroup (n : ℕ) :
    AddCommGroup (RationalInvariantFunctions F n) := Submodule.addCommGroup _
local instance ramifiedContinuousAddCommGroup (n : ℕ) :
    AddCommGroup (ContinuousRationalFunctions F n) := Submodule.addCommGroup _
local instance ramifiedSmoothAddCommGroup (n : ℕ) :
    AddCommGroup (FiniteSmoothRationalFunctions F n) := Submodule.addCommGroup _
local instance ramifiedFormAddCommGroup (n : ℕ) :
    AddCommGroup (AutomorphicForms F n) := Submodule.addCommGroup _
local instance ramifiedLocalAddCommGroup {n : ℕ} {v : FinitePlace F}
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
  obtain ⟨⟨d, hd⟩, ⟨e, he⟩, hall⟩ := hL
  have hgen := CuspidalPairPartialGamma.localGenericity F r T P v (hP v).1 (hP v).2 ψ
  have hgen' := CuspidalPairPartialGamma.localGenericity F t T' P' v (hP' v).1 (hP' v).2 ψ
  obtain ⟨A₀, hstd, hA₀⟩ := genericLanglandsQuotientLFactor (residuePrime v)
    (padicField v) ψ ν r t d e X.obj Y.obj hd he hgen hgen'
  rwa [(hall d e hd he).unique hstd]

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

omit [CompactSpace (AdeleQuotient F)] in
private theorem quasicharacterBase_inv_at (v : FinitePlace F) (χ : HeckeCharacter F) :
    quasicharacterBase v (χ⁻¹.finiteComponent v) = (quasicharacterBase v (χ.finiteComponent v))⁻¹ := rfl

/-- For each actual cuspidal pair and each finite place, sufficiently ramified
Hecke twists of the first member have local gamma order zero everywhere. -/
def CuspidalPairRamifiedGammaOrderStatement : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F] [CompactSpace (AdeleQuotient F)]
    {ψ : HarmonicAnalysis.UnitaryAdditiveCharacter (Adeles F)} {r t : ℕ}
    (D : AutomorphicTwistSetup.{u,uQ} ψ r t) (v : FinitePlace F),
    ∃ b : ℕ, ∀ χ : HeckeCharacter F,
      b ≤ (padicField v).canonicalTopologicalData.multiplicativeConductor
        (quasicharacterBase v (χ.finiteComponent v)) →
      ∀ z : ℂ, meromorphicOrderAt (D.localFactors χ (.inr v)).gamma z = 0

set_option maxHeartbeats 1000000 in
theorem cuspidalPairRamifiedGammaOrder : CuspidalPairRamifiedGammaOrderStatement.{u,uQ} := by
  intro F _ _ _ ψ r t D v
  let ν : PadicAbelian.SelfDualHaar (padicField v).canonicalTopologicalData (D.additive v) :=
    ⟨D.measure v, D.measure_spec v⟩
  obtain ⟨b, hb⟩ := exists_ramified_lPolynomial_eq_one D.P D.P' D.h D.h' v (D.additive v) ν
  obtain ⟨c, hc⟩ := exists_ramified_lPolynomial_eq_one D.Pd D.Pd' D.hd D.hd' v (D.additive v) ν
  refine ⟨max b c, fun χ hχ z => ?_⟩
  have hχinv : c ≤ (padicField v).canonicalTopologicalData.multiplicativeConductor
      (quasicharacterBase v (χ⁻¹.finiteComponent v)) := by
    rw [quasicharacterBase_inv_at v χ, HighlyRamified.multiplicativeConductor_inv]
    exact (le_max_right b c).trans hχ
  have hL := hb χ ((le_max_left b c).trans hχ) _ (D.finiteData_specs χ v).1
  have hLd := hc χ⁻¹ hχinv _ (D.finiteData_specs χ v).2.1
  let q := residueCardinality v
  let d := (D.finiteData χ v).2.2
  have hgamma : (D.localFactors χ (.inr v)).gamma = epsilonMonomial q d.1 d.2 := by
    funext s
    change ((d.1 : ℂ) * spectralPoint q s ^ d.2) *
      (((D.finiteData χ v).2.1).eval (spectralPoint q (1 - s)))⁻¹ /
        (((D.finiteData χ v).1).eval (spectralPoint q s))⁻¹ = _
    simp [hL, hLd, epsilonMonomial]
  have hq : 0 < (q : ℝ) := by
    exact_mod_cast (lt_trans Nat.zero_lt_one (FinitePairFactorChoice.one_lt_residueCardinality v))
  have hε := epsilonMonomial_analyticAt q hq d.1 d.2 z
  rw [hgamma, hε.meromorphicOrderAt_eq,
    hε.analyticOrderAt_eq_zero.mpr (epsilonMonomial_ne_zero q hq d.1 d.2 z)]
  rfl

end Langlands.Global.CuspidalPairFunctionalEquation
