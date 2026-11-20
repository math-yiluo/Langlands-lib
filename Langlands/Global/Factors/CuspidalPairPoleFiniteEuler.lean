import Langlands.Automorphic.CuspidalWhittaker.AdelicCharacter
import Langlands.Global.Factors.CuspidalPairFiniteLayer
import Langlands.Global.Factors.CuspidalPairPoleStatement
import Langlands.Global.RankinSelberg.PartialEulerProductConvergence

/-! # Finite data and the Euler product for cuspidal pair poles -/

noncomputable section

set_option autoImplicit false

universe u uQ

namespace Langlands.Global.CuspidalPairPoles

open NumberField CompletionPadic
open Automorphic (CuspidalOperatorRealization CuspidalSpectralPresentation)
open Automorphic.CuspidalWhittaker (adelicCharacter adelicCharacter_algebraMap
  continuous_adelicCharacter exists_adelicCharacter_ne_one)
open CuspidalPairFunctionalEquation
open CuspidalPairBoundaryNonvanishing (partialEulerFactor)
open RankinSelbergGlobal (exists_partialEulerFactor_convergence partialEulerProduct)

variable {F : Type u} [Field F] [NumberField F] [CompactSpace (AdeleQuotient F)]
  {r t : ℕ} {T : CuspidalOperatorRealization F r} {T' : CuspidalOperatorRealization F t}
  {P : CuspidalSpectralPresentation.{u, uQ} T} {P' : CuspidalSpectralPresentation.{u, uQ} T'}
  {h : HasIrreducibleAdmissibleComponents P} {h' : HasIrreducibleAdmissibleComponents P'}

/-- Finite pair L-data for spectral presentations with irreducible admissible finite
components, using the standard adelic additive character. -/
def standardFinitePairLChoice : FinitePairLChoice P P' h h' := by
  let ψ : HarmonicAnalysis.UnitaryAdditiveCharacter (Adeles F) :=
    ⟨adelicCharacter F, continuous_adelicCharacter F, by
      obtain ⟨x, hx⟩ := exists_adelicCharacter_ne_one F
      intro heq
      exact hx (by simp [heq])⟩
  let ψf := canonicalFiniteAdditiveComponent ψ (adelicCharacter_algebraMap F)
  let μ := fun v => Correspondence.localSelfDualHaar (padicField v) (ψf v)
  have hμ : ∀ v, Correspondence.IsSelfDualMeasure (padicField v) (ψf v) (μ v) :=
    fun v => Correspondence.isSelfDual_localSelfDualHaar (padicField v) (ψf v)
  have hL := fun v => exists_isAutomorphicPairLPolynomial (padicField v) (ψf v) (hμ v)
    (localClass P h v) (localClass P' h' v)
  exact
    { additive := ψf
      measure := μ
      measure_spec := hμ
      lPolynomial := fun v => (hL v).choose
      lPolynomial_spec := fun v => (hL v).choose_spec }

/-- The choice of finite pair L-data required by `CuspidalPairPoleStatement` exists. -/
theorem nonempty_finitePairLChoice : Nonempty (FinitePairLChoice P P' h h') :=
  ⟨standardFinitePairLChoice⟩

namespace FinitePairLChoice

variable (c : FinitePairLChoice P P' h h')
  {S : Finset (FinitePlace F)} (hP : P.exceptional ⊆ S) (hP' : P'.exceptional ⊆ S)

/-- At a place outside both exceptional sets, every certified finite pair factor equals
the spherical Euler factor of the respective Satake spectra. -/
theorem finiteL_eq_partialEulerFactor (v : {v : FinitePlace F // v ∉ S}) (s : ℂ) :
    c.finiteL v s = partialEulerFactor P P' hP hP' v s := by
  have hpoly := isAutomorphicPairLPolynomial_eq_pairEulerPolynomial (padicField v.1)
    (c.additive v.1) (c.measure_spec v.1) _ _
    (hasSphericalSpectrum_padicObject P h v.1 (fun hv => v.2 (hP hv)))
    (hasSphericalSpectrum_padicObject P' h' v.1 (fun hv => v.2 (hP' hv)))
    (c.lPolynomial_spec v.1)
  simp [finiteL, partialEulerFactor, hpoly]

/-- The full finite Euler product converges absolutely on a right half-plane and has
value the product of the factors in `S` times the partial Euler product outside `S`. -/
theorem exists_finiteL_convergence :
    ∃ σ : ℝ, ∀ s : ℂ, σ < s.re →
      Summable (fun v => ‖c.finiteL v s - 1‖) ∧
        HasProd (fun v => c.finiteL v s)
          ((∏ v ∈ S, c.finiteL v s) * partialEulerProduct P P' hP hP' s) := by
  classical
  obtain ⟨σ, hσ⟩ := exists_partialEulerFactor_convergence P P' hP hP'
  refine ⟨σ, fun s hs => ?_⟩
  obtain ⟨hsum, hprod⟩ := hσ s hs
  have hfactor := fun v => c.finiteL_eq_partialEulerFactor hP hP' v s
  have hsumOutside : Summable (fun v : ↥((S : Set (FinitePlace F))ᶜ) => ‖c.finiteL v s - 1‖) :=
    hsum.congr (fun v => congrArg (fun z : ℂ => ‖z - 1‖) (hfactor v).symm)
  have hprodOutside : HasProd (fun v : ↥((S : Set (FinitePlace F))ᶜ) => c.finiteL v s)
      (partialEulerProduct P P' hP hP' s) := hprod.congr_fun hfactor
  exact ⟨(S.hasSum (fun v => ‖c.finiteL v s - 1‖)).summable.add_compl hsumOutside,
    (S.hasProd (fun v => c.finiteL v s)).mul_compl hprodOutside⟩

/-- Matching the partial Euler product multiplied by the remaining factors on a right
half-plane suffices for the completed-L-function identity. -/
theorem isCompletedLFunction_of_partialEulerProduct (Linf Λ : ℂ → ℂ) (σ : ℝ)
    (hΛ : ∀ s : ℂ, σ < s.re → Λ s =
      Linf s * ((∏ v ∈ S, c.finiteL v s) * partialEulerProduct P P' hP hP' s)) :
    c.IsCompletedLFunction Linf Λ := by
  obtain ⟨σ', hσ'⟩ := c.exists_finiteL_convergence hP hP'
  refine ⟨max σ σ', fun s hs => ?_⟩
  obtain ⟨hsum, hprod⟩ := hσ' s (lt_of_le_of_lt (le_max_right _ _) hs)
  exact ⟨hsum, _, hprod, hΛ s (lt_of_le_of_lt (le_max_left _ _) hs)⟩

end FinitePairLChoice

end Langlands.Global.CuspidalPairPoles
