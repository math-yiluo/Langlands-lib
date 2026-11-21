import Langlands.Automorphic.CuspidalContragredientLocalCompatibilityProof
import Langlands.Automorphic.SupercuspidalComponent
import Langlands.BaseChange.SphericalStandardFactorsAtCompletion
import Langlands.BaseChange.SupercuspidalStandardEulerPolynomial
import Langlands.Representation.Classification.SupercuspidalInverseTranspose
import Langlands.Representation.RankinSelberg.SmoothDualPairFactors

/-! # Standard Euler polynomials at a supercuspidal finite completion -/

noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u uQ

namespace Langlands.BaseChange

open Automorphic Correspondence Global Global.CompletionPadic GeneralLinear RankinSelberg Whittaker
open Global.CuspidalPairFunctionalEquation

variable {K : Type u} [Field K] [NumberField K]

/-- A supercuspidal component gives a Jacquet-vanishing object in the canonical topology. -/
theorem padicObject_isSupercuspidal {r : ℕ} {v : FinitePlace K}
    (A : LocalRealization K (r + 1) v) (hI : A.IsIrreducible) (hA : A.IsAdmissible)
    (hs : A.IsSupercuspidal) :
    letI := (padicField v).canonicalTopologicalData.topology
    IsSupercuspidal (A.padicObject hI hA).obj.representation := by
  let F := padicField v
  let := F.canonicalTopologicalData.topology
  obtain ⟨hI', hA', c, hc⟩ := hs
  obtain ⟨B, hB⟩ := Quotient.exists_rep c
  have he : automorphicClassOf F B.toIrreducibleAdmissible =
      automorphicClassOf F (A.padicObject hI hA) := by
    change supercuspidalToAutomorphic F (Quotient.mk _ B) = A.padicClass hI hA
    simpa only [hB] using hc
  obtain ⟨e⟩ := (automorphicClassOf_eq_iff F _ _).mp he
  exact isSupercuspidal_of_equiv e B.property.2

variable [CompactSpace (AdeleQuotient K)]

set_option maxHeartbeats 2500000 in
/-- At a supercuspidal finite place, the actual local component of the global
contragredient is supercuspidal with the canonical p-adic topology. -/
theorem padicObject_isSupercuspidal_of_isContragredientOf
    {r : ℕ} {T Td : CuspidalOperatorRealization K r}
    (hD : Td.realization.IsContragredientOf T.realization)
    (P : CuspidalSpectralPresentation.{u, uQ} T) (Pd : CuspidalSpectralPresentation.{u, uQ} Td)
    (h : HasIrreducibleAdmissibleComponents P) (hd : HasIrreducibleAdmissibleComponents Pd)
    (v : FinitePlace K) (hs : (P.localComponent v).IsSupercuspidal) :
    letI := (padicField v).canonicalTopologicalData.topology
    IsSupercuspidal ((Pd.localComponent v).padicObject (hd v).1 (hd v).2).obj.representation := by
  let F := padicField v
  let : TopologicalSpace F.Carrier := F.canonicalTopologicalData.topology
  let (n : ℕ) : TopologicalSpace (GeneralLinear n F.Carrier) := F.canonicalGeneralLinearTopology n
  let (n : ℕ) : IsTopologicalGroup (GeneralLinear n F.Carrier) := F.canonicalGeneralLinearTopologicalGroup n
  let A := (P.localComponent v).padicObject (h v).1 (h v).2
  obtain ⟨e⟩ := cuspidalContragredientLocalCompatibility K r T Td hD P Pd v
    (h v).1 (h v).2 (hd v).1 (hd v).2
  let d := inverseTransposeSmoothDualEquiv F A.obj.representation A.property.2 A.property.1
  have hs' : IsSupercuspidal (inverseTransposePullback A.obj.representation) :=
    isSupercuspidal_comp_inverseTranspose A.obj.representation
      (padicObject_isSupercuspidal (P.localComponent v) (h v).1 (h v).2 hs)
  exact (isSupercuspidal_iff_of_equiv (e.trans d.symm)).mpr hs'

/-- For an actual finite pair with a trivial rank-one second member, if the
first member has rank greater than one and is supercuspidal at the chosen
place, both the forward and contragredient standard polynomials there are one. -/
def SupercuspidalStandardFactorsAtCompletionStatement : Prop :=
  ∀ (K : Type u) [Field K] [NumberField K] [CompactSpace (AdeleQuotient K)]
    (r : ℕ), 0 < r → ∀ (T Td : CuspidalOperatorRealization K r),
    Td.realization.IsContragredientOf T.realization →
    ∀ (P : CuspidalSpectralPresentation.{u, uQ} T) (Pd : CuspidalSpectralPresentation.{u, uQ} Td)
      (h : HasIrreducibleAdmissibleComponents P) (hd : HasIrreducibleAdmissibleComponents Pd)
      (ψ : HarmonicAnalysis.UnitaryAdditiveCharacter (Adeles K)),
      let C := ConstantFunctions.rankOneSpectralPresentation.{u, uQ} K
      let hC := ConstantFunctions.rankOneSpectralPresentation_hasIrreducibleAdmissibleComponents.{u, uQ} K
      ∀ (c : FinitePairFactorChoice ψ P C Pd C h hC hd hC) (v : FinitePlace K),
        (P.localComponent v).IsSupercuspidal →
          c.lPolynomial v = 1 ∧ c.dualLPolynomial v = 1

set_option maxHeartbeats 2800000 in
/-- Use local contragredience and apply the same unequal-rank calculation to
both actual pairs in the completed equation. -/
theorem supercuspidalStandardFactorsAtCompletion : SupercuspidalStandardFactorsAtCompletionStatement.{u, uQ} := by
  intro K _ _ _ r hr T Td hD P Pd h hd ψ C hC c v hs
  let F := padicField v
  let A := (P.localComponent v).padicObject (h v).1 (h v).2
  let Ad := (Pd.localComponent v).padicObject (hd v).1 (hd v).2
  let B := (C.localComponent v).padicObject (hC v).1 (hC v).2
  have htriv := ConstantFunctions.rankOneSpectralPresentation_localTrivialEquiv.{u, uQ} K v
  have hs₀ := padicObject_isSupercuspidal (P.localComponent v) (h v).1 (h v).2 hs
  have hsd := padicObject_isSupercuspidal_of_isContragredientOf hD P Pd h hd v hs
  exact ⟨supercuspidalStandardEulerPolynomial (residuePrime v) F r hr (c.additive v) (c.measure v)
      (c.measure_spec v) A B hs₀ htriv (c.lPolynomial v) (c.lPolynomial_spec v),
    supercuspidalStandardEulerPolynomial (residuePrime v) F r hr (c.additive v) (c.measure v)
      (c.measure_spec v) Ad B hsd htriv (c.dualLPolynomial v) (c.dualLPolynomial_spec v)⟩

end Langlands.BaseChange
