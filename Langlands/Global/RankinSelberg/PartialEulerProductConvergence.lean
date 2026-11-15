import Langlands.Global.Factors.CuspidalSatakeBoundReduction
import Langlands.Automorphic.IrreducibleCentralCharacterProof
import Langlands.Global.Factors.CuspidalPairBoundaryNonvanishingStatement

/-! # Absolute convergence of the partial pair Euler products

For actual cuspidal realizations `T`, `T'` of `GL_(r+1)`, `GL_(t+1)`, spectral presentations
`P`, `P'` and a finite set `S` of finite places containing both exceptional sets, the Euler
product `∏_(v ∉ S) L(s, Π_v × Π'_v)` of `partialEulerFactor` converges absolutely on a right
half-plane. No unitarity or irreducible-admissible hypothesis is used. See the paired
Markdown.
-/

noncomputable section
universe u uQ
open NumberField Polynomial
set_option autoImplicit false

namespace Langlands.Global.RankinSelbergGlobal

open CuspidalPairBoundaryNonvanishing CuspidalPairFunctionalEquation
open Automorphic (CuspidalOperatorRealization CuspidalSpectralPresentation)

variable {F : Type u} [Field F] [NumberField F] [CompactSpace (AdeleQuotient F)]

/-- Every spectral presentation of an actual cuspidal realization has Satake parameters bounded
by a fixed power `q_v ^ C` of the residue cardinality, at every place outside its exceptional
set. -/
theorem exists_hasSatakeBound_presentation {r : ℕ} (T : CuspidalOperatorRealization F r)
    (P : CuspidalSpectralPresentation.{u, uQ} T) : ∃ C : ℝ, HasSatakeBound P C := by
  obtain ⟨ω, hω, -⟩ := Automorphic.OperatorRealization.irreducibleCentralCharacter F (r + 1)
    T.realization T.irreducible
  exact CuspidalSatakeBound.exists_hasSatakeBound T ω hω P

/-- The value `∏'_(v ∉ S) L(s, Π_v × Π'_v)` of the partial pair Euler product, as an
unconditional infinite product over the finite places outside `S` (it is `1` when the product
is not multipliable). -/
def partialEulerProduct {r t : ℕ} {T : CuspidalOperatorRealization F r}
    {T' : CuspidalOperatorRealization F t} (P : CuspidalSpectralPresentation.{u, uQ} T)
    (P' : CuspidalSpectralPresentation.{u, uQ} T') {S : Finset (FinitePlace F)}
    (hP : P.exceptional ⊆ S) (hP' : P'.exceptional ⊆ S) (s : ℂ) : ℂ :=
  ∏' v, partialEulerFactor P P' hP hP' v s

/-- The partial pair Euler product converges absolutely on a right half-plane: there is `σ`
such that for `σ < Re s`, `∑_(v ∉ S) ‖L(s, Π_v × Π'_v) - 1‖` converges and the product has
the value `partialEulerProduct P P' hP hP' s`. -/
theorem exists_partialEulerFactor_convergence {r t : ℕ} {T : CuspidalOperatorRealization F r}
    {T' : CuspidalOperatorRealization F t} (P : CuspidalSpectralPresentation.{u, uQ} T)
    (P' : CuspidalSpectralPresentation.{u, uQ} T') {S : Finset (FinitePlace F)}
    (hP : P.exceptional ⊆ S) (hP' : P'.exceptional ⊆ S) :
    ∃ σ : ℝ, ∀ s : ℂ, σ < s.re →
      Summable (fun v => ‖partialEulerFactor P P' hP hP' v s - 1‖) ∧
        HasProd (fun v => partialEulerFactor P P' hP hP' v s)
          (partialEulerProduct P P' hP hP' s) := by
  classical
  obtain ⟨A, hA⟩ := exists_hasSatakeBound_presentation T P
  obtain ⟨B, hB⟩ := exists_hasSatakeBound_presentation T' P'
  refine ⟨A + B + (((r + 1) * (t + 1) + 1 : ℕ) : ℝ), fun s hs => ?_⟩
  let L : FinitePlace F → ℂ[X] := fun v =>
    if h : v ∈ S then 1 else
      pairEulerPolynomial (P.spectralSystem.eigenvalues v fun h' => h (hP h'))
        (P'.spectralSystem.eigenvalues v fun h' => h (hP' h'))
  have hsum := CuspidalPairEulerConvergence.summable_norm_inv_eval_sub_one S L
    (fun v hv => P.spectralSystem.eigenvalues v fun h => hv (hP h))
    (fun v hv => P'.spectralSystem.eigenvalues v fun h => hv (hP' h))
    (fun v hv => by simp [L, hv]) (fun v hv α hα => hA v _ α hα)
    (fun v hv β hβ => hB v _ β hβ) (s := s) hs
  have h1 : Summable (fun v : {v : FinitePlace F // v ∉ S} =>
      ‖partialEulerFactor P P' hP hP' v s - 1‖) := by
    refine (hsum.subtype (fun v => v ∉ S)).congr fun v => ?_
    simp [L, partialEulerFactor, v.2]
  exact ⟨h1, CuspidalPairEulerConvergence.hasProd_of_summable_norm_sub_one h1⟩

end Langlands.Global.RankinSelbergGlobal
