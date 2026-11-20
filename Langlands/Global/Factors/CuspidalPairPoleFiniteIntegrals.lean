import Langlands.Automorphic.CuspidalUnitaryLocalGenericity
import Langlands.Correspondence.AutomorphicActualGamma
import Langlands.Global.Factors.CuspidalPairFiniteLayer
import Langlands.Global.Factors.CuspidalPairPoleFiniteComparison
import Langlands.Global.Factors.CuspidalSplitCentreUnitaryProof

/-! # Cuspidal pair L-polynomials and the actual finite integrals -/

noncomputable section

set_option autoImplicit false

universe u uQ

namespace Langlands.Global.CuspidalPairPoles.FinitePairLChoice

open NumberField CompletionPadic RankinSelberg
open Automorphic (CuspidalOperatorRealization CuspidalSpectralPresentation
  cuspidalUnitaryLocalGenericity)
open CuspidalPairFunctionalEquation
open ClassField.Global.RelativeWeilGroup (HasUnitaryCentralCharacter)

variable {F : Type u} [Field F] [NumberField F] [CompactSpace (AdeleQuotient F)]
  {r t : ℕ} {T : CuspidalOperatorRealization F r} {T' : CuspidalOperatorRealization F t}
  {P : CuspidalSpectralPresentation.{u, uQ} T} {P' : CuspidalSpectralPresentation.{u, uQ} T'}
  {h : HasIrreducibleAdmissibleComponents P} {h' : HasIrreducibleAdmissibleComponents P'}
  (c : FinitePairLChoice P P' h h') (v : FinitePlace F)
  (ψ : Correspondence.NontrivialAdditiveCharacter (padicField v))
  (ν : LocalFactor.PadicAbelian.SelfDualHaar (padicField v).canonicalTopologicalData ψ)

local instance : TopologicalSpace (padicField v).Carrier :=
  (padicField v).canonicalTopologicalData.topology

local instance (n : ℕ) : TopologicalSpace (GeneralLinear n (padicField v).Carrier) :=
  (padicField v).canonicalGeneralLinearTopology n

/-- The specified polynomial is the p-adic Rankin–Selberg polynomial of the actual
finite actions, with the supplied additive character and self-dual measure. -/
def IsIntegralPolynomialAt : Prop :=
  IsPadicSymmetricLPolynomial (padicField v) ψ ν.val
    ((P.localComponent v).padicObject (h v).1 (h v).2).obj.representation
    ((P'.localComponent v).padicObject (h' v).1 (h' v).2).obj.representation (c.lPolynomial v)

/-- For cuspidal realizations with unitary central characters, every finite L-polynomial
in the target is also the integral L-polynomial of the two actual local actions. -/
theorem isIntegralPolynomialAt_of_unitaryCentralCharacter (hT : HasUnitaryCentralCharacter T)
    (hT' : HasUnitaryCentralCharacter T') : c.IsIntegralPolynomialAt v ψ ν := by
  let A := (P.localComponent v).padicObject (h v).1 (h v).2
  let A' := (P'.localComponent v).padicObject (h' v).1 (h' v).2
  obtain ⟨Q, hQ⟩ := exists_isAutomorphicPairLPolynomial (padicField v) ψ ν.property
    (localClass P h v) (localClass P' h' v)
  have hpoly := (c.lPolynomial_spec v).unique_of_data hQ
  have hLang := (Correspondence.isAutomorphicPairLPolynomial_iff
    (padicField v) A A' A.obj A'.obj (Representation.Equiv.refl _) (Representation.Equiv.refl _)).mp hQ
  have hgen := cuspidalUnitaryLocalGenericity F r T hT P v (h v).1 (h v).2 ψ
  have hgen' := cuspidalUnitaryLocalGenericity F t T' hT' P' v (h' v).1 (h' v).2 ψ
  unfold IsIntegralPolynomialAt
  rw [hpoly]
  exact hLang.isPadicSymmetricLPolynomial hgen hgen'

/-- The finite integral comparison under the split-centre hypothesis of the pole theorem. -/
theorem isIntegralPolynomialAt (hT : IsTrivialOnSplitCentre T) (hT' : IsTrivialOnSplitCentre T') :
    c.IsIntegralPolynomialAt v ψ ν :=
  c.isIntegralPolynomialAt_of_unitaryCentralCharacter v ψ ν
    (cuspidalSplitCentreUnitaryCentralCharacter F r T hT)
    (cuspidalSplitCentreUnitaryCentralCharacter F t T' hT')

end Langlands.Global.CuspidalPairPoles.FinitePairLChoice
