import Langlands.Global.Factors.RelativeGammaComparisonStatement
import Mathlib.Analysis.Meromorphic.Basic

/-!
# Finite-place factor data of cuspidal Rankin–Selberg pairs

Definitions for the completed global Rankin–Selberg functional equation of Henniart
(1986), §2.10, and Henniart (2000), §2.3, in the established form of Cogdell (2004),
Theorem 4.1, and Getz–Hahn (2024), Theorem 11.7.1. Henniart states it for arbitrary
automorphic `Π`, `Π'`; these definitions specialize to actual cuspidal
realizations of `GL_(r+1)` and `GL_(t+1)` over a number field, the specialization
the Library's consumers need. The finite local components are those of the original spectral
presentations, read as canonical p-adic classes. The local additive characters are
the finite components of one global character, with self-dual measures. The dual
side uses the presentations of further realizations, meant to be the actual
contragredients.

The archimedean factors enter `CompletedEquationHolds` only as supplied functions.
The completed statement, with the actual archimedean components and pair factors of
task 6c50b2fd, is not defined here.
-/

noncomputable section

set_option autoImplicit false

open Polynomial

universe u uQ

namespace Langlands.Global.CuspidalPairFunctionalEquation

open scoped NumberField
open Langlands.Global.CompletionPadic Langlands.ClassField.Global.RelativeWeilGroup

variable {F : Type u} [Field F] [NumberField F] [CompactSpace (AdeleQuotient F)]

/-- The residue cardinality `q_v` of the finite place `v`. -/
abbrev residueCardinality (v : FinitePlace F) : ℕ :=
  (padicField v).canonicalTopologicalData.residueCardinality

/-- The unramified pair Euler polynomial `∏_(i,j) (1 - a_i b_j X)` of two Satake
multisets, so that `L(s, Π_v × Π'_v) = 1 / P(q_v^(-s))` at unramified places. -/
def pairEulerPolynomial {n m : ℕ} (a : Unramified.Eigenvalues n)
    (b : Unramified.Eigenvalues m) : ℂ[X] :=
  (((a : Multiset ℂˣ) ×ˢ (b : Multiset ℂˣ)).map
    (fun z : ℂˣ × ℂˣ => 1 - C ((z.1 : ℂ) * z.2) * X)).prod

/-- Every finite local component of the presentation is irreducible and admissible. -/
def HasIrreducibleAdmissibleComponents {r : ℕ} {T : Automorphic.CuspidalOperatorRealization F r}
    (P : Automorphic.CuspidalSpectralPresentation.{u, uQ} T) : Prop :=
  ∀ v, (P.localComponent v).IsIrreducible ∧ (P.localComponent v).IsAdmissible

variable {r t : ℕ} {T Td : Automorphic.CuspidalOperatorRealization F r}
  {T' Td' : Automorphic.CuspidalOperatorRealization F t}

/-- The canonical p-adic class of the finite local component at `v`. -/
abbrev localClass (P : Automorphic.CuspidalSpectralPresentation.{u, uQ} T)
    (h : HasIrreducibleAdmissibleComponents P) (v : FinitePlace F) :
    Correspondence.AutomorphicClass.{u, u} (padicField v) r.succPNat :=
  (P.localComponent v).padicClass (h v).1 (h v).2

/-- A choice of local data at every finite place: the component `ψ_v` of `ψ`, a
self-dual measure for it, the pair L-polynomials of `(Π_v, Π'_v)` and of
`(Π∨_v, Π'∨_v)`, and the pair epsilon factor of `(Π_v, Π'_v)` at `ψ_v`. -/
structure FinitePairFactorChoice
    (ψ : HarmonicAnalysis.UnitaryAdditiveCharacter (Adeles F))
    (P : Automorphic.CuspidalSpectralPresentation.{u, uQ} T)
    (P' : Automorphic.CuspidalSpectralPresentation.{u, uQ} T')
    (Pd : Automorphic.CuspidalSpectralPresentation.{u, uQ} Td)
    (Pd' : Automorphic.CuspidalSpectralPresentation.{u, uQ} Td')
    (h : HasIrreducibleAdmissibleComponents P) (h' : HasIrreducibleAdmissibleComponents P')
    (hd : HasIrreducibleAdmissibleComponents Pd)
    (hd' : HasIrreducibleAdmissibleComponents Pd') where
  additive : ∀ v : FinitePlace F, Correspondence.NontrivialAdditiveCharacter (padicField v)
  additive_spec : ∀ v, IsCanonicalFiniteAdditiveComponent ψ v (additive v)
  measure : ∀ v : FinitePlace F, Correspondence.LocalAdditiveHaarMeasure (padicField v)
  measure_spec : ∀ v, Correspondence.IsSelfDualMeasure (padicField v) (additive v) (measure v)
  lPolynomial : FinitePlace F → ℂ[X]
  lPolynomial_spec : ∀ v, Correspondence.IsAutomorphicPairLPolynomial (padicField v)
    (additive v) (measure v) (localClass P h v) (localClass P' h' v) (lPolynomial v)
  dualLPolynomial : FinitePlace F → ℂ[X]
  dualLPolynomial_spec : ∀ v, Correspondence.IsAutomorphicPairLPolynomial (padicField v)
    (additive v) (measure v) (localClass Pd hd v) (localClass Pd' hd' v) (dualLPolynomial v)
  epsilon : FinitePlace F → ℂˣ × ℤ
  epsilon_spec : ∀ v, Correspondence.IsAutomorphicPairEpsilonFactor (padicField v)
    (additive v) (measure v) (localClass P h v) (localClass P' h' v) (epsilon v)

namespace FinitePairFactorChoice

variable {ψ : HarmonicAnalysis.UnitaryAdditiveCharacter (Adeles F)}
  {P : Automorphic.CuspidalSpectralPresentation.{u, uQ} T}
  {P' : Automorphic.CuspidalSpectralPresentation.{u, uQ} T'}
  {Pd : Automorphic.CuspidalSpectralPresentation.{u, uQ} Td}
  {Pd' : Automorphic.CuspidalSpectralPresentation.{u, uQ} Td'}
  {h : HasIrreducibleAdmissibleComponents P} {h' : HasIrreducibleAdmissibleComponents P'}
  {hd : HasIrreducibleAdmissibleComponents Pd} {hd' : HasIrreducibleAdmissibleComponents Pd'}
  (c : FinitePairFactorChoice ψ P P' Pd Pd' h h' hd hd')

/-- `L(s, Π_v × Π'_v) = 1 / P_v(q_v^(-s))`. -/
def finiteL (v : FinitePlace F) (s : ℂ) : ℂ :=
  ((c.lPolynomial v).eval (RankinSelberg.spectralPoint (residueCardinality v) s))⁻¹

/-- `L(s, Π∨_v × Π'∨_v) = 1 / P∨_v(q_v^(-s))`. -/
def finiteDualL (v : FinitePlace F) (s : ℂ) : ℂ :=
  ((c.dualLPolynomial v).eval (RankinSelberg.spectralPoint (residueCardinality v) s))⁻¹

/-- `ε(s, Π_v × Π'_v, ψ_v) = c_v q_v^(-m_v s)`. -/
def finiteEpsilon (v : FinitePlace F) (s : ℂ) : ℂ :=
  ((c.epsilon v).1 : ℂ) * RankinSelberg.spectralPoint (residueCardinality v) s ^ (c.epsilon v).2

/-- Outside `S` the chosen factors are the unramified ones: both L-polynomials are
the pair Euler polynomials of the supplied Satake spectra, and `ε_v = 1`. -/
def IsUnramifiedOutside (S : Finset (FinitePlace F)) : Prop :=
  ∀ v ∉ S,
    (∀ (hv : v ∉ P.exceptional) (hv' : v ∉ P'.exceptional),
      c.lPolynomial v = pairEulerPolynomial (P.spectralSystem.eigenvalues v hv)
        (P'.spectralSystem.eigenvalues v hv')) ∧
    (∀ (hv : v ∉ Pd.exceptional) (hv' : v ∉ Pd'.exceptional),
      c.dualLPolynomial v = pairEulerPolynomial (Pd.spectralSystem.eigenvalues v hv)
        (Pd'.spectralSystem.eigenvalues v hv')) ∧
    c.epsilon v = (1, 0)

/-- The analytic conclusions, given the products `Linf`, `Ldinf` of the archimedean
L-factors of the pair and of the contragredient pair and the product `εinf` of the
archimedean epsilon factors. On some right half-plane both finite Euler products
converge absolutely, and times `Linf`, `Ldinf` they are the completed L-functions
`Λ`, `Λd`. Both continue meromorphically to `ℂ`, and off a discrete set
`Λ(s) = (∏_(v ∈ S) ε_v(s)) ε_∞(s) Λd(1 - s)`. -/
def CompletedEquationHolds (S : Finset (FinitePlace F)) (Linf Ldinf εinf : ℂ → ℂ) : Prop :=
  ∃ (σ : ℝ) (Λ Λd : ℂ → ℂ),
    MeromorphicOn Λ Set.univ ∧ MeromorphicOn Λd Set.univ ∧
    (∀ s : ℂ, σ < s.re →
      Summable (fun v => ‖c.finiteL v s - 1‖) ∧ Summable (fun v => ‖c.finiteDualL v s - 1‖) ∧
      ∃ p pd : ℂ, HasProd (fun v => c.finiteL v s) p ∧ HasProd (fun v => c.finiteDualL v s) pd ∧
        Λ s = Linf s * p ∧ Λd s = Ldinf s * pd) ∧
    ∀ᶠ s in Filter.codiscrete ℂ,
      Λ s = (∏ v ∈ S, c.finiteEpsilon v s) * εinf s * Λd (1 - s)

end FinitePairFactorChoice

end Langlands.Global.CuspidalPairFunctionalEquation
