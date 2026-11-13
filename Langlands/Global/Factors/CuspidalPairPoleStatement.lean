import Langlands.Global.Factors.CuspidalPairFactorData
import Langlands.Automorphic.ArchimedeanPlaceParameter
import Langlands.Automorphic.Contragredient
import Langlands.LocalFactor.ArchimedeanPairFactor
import Mathlib.Analysis.Meromorphic.Order

/-!
# Poles and vertical-strip bounds of completed cuspidal pair L-functions

Getz–Hahn (2024), Theorem 11.7.1, apart from the functional equation, in the established
form of Cogdell (2004), Theorems 4.1 and 4.2, for actual cuspidal realizations of
`GL_(r+1)` and `GL_(t+1)` over a number field that are trivial on the split components
`A_GL` of their centres. The completed L-function is the finite Euler product of the
JPSS pair factors of the finite local components of the spectral presentations, times
the archimedean pair factors of the standard-module parameters at the infinite places.
It is holomorphic off `{0, 1}`, has at most simple poles at `0` and `1`, which occur
exactly when the ranks agree and `π ≅ π'^∨`, and is bounded in vertical strips away
from its poles. See the paired Markdown for sources, normalizations and the scope.
-/

noncomputable section

set_option autoImplicit false

open Polynomial

universe u uQ

namespace Langlands.Global

open NumberField
open Langlands.Global.CompletionPadic
open Automorphic (CuspidalOperatorRealization CuspidalSpectralPresentation OperatorRealization)
open Automorphic.ContinuousRationalFunctions (evaluate)
open CuspidalPairFunctionalEquation (HasIrreducibleAdmissibleComponents localClass
  residueCardinality FinitePairFactorChoice)
open LocalFactor.Archimedean

namespace CuspidalPairPoles

section SplitCentre

variable {F : Type u} [Field F] [NumberField F]

/-- The idele `a` lies in `A_(G_m)`: its finite component is `1`, and its archimedean
component is one positive real number `t` at every infinite place, read in `ℂ` through
the embedding of the completion. -/
def IsPositiveArchimedeanScalar (a : IdeleGroup (𝓞 F) F) : Prop :=
  (a : AdeleRing (𝓞 F) F).2 = 1 ∧
    ∃ t : ℝ, 0 < t ∧ ∀ v : InfinitePlace F,
      InfinitePlace.Completion.extensionEmbedding v ((a : AdeleRing (𝓞 F) F).1 v) = (t : ℂ)

end SplitCentre

variable {F : Type u} [Field F] [NumberField F] [CompactSpace (AdeleQuotient F)]
  {r t : ℕ}

/-- The cuspidal realization `T` of `GL_(r+1)` is trivial on `A_(GL_(r+1))`: every
function in it is invariant under the scalar matrices `a I` with `a ∈ A_(G_m)`. -/
def IsTrivialOnSplitCentre (T : CuspidalOperatorRealization F r) : Prop :=
  ∀ a : IdeleGroup (𝓞 F) F, IsPositiveArchimedeanScalar a →
    ∀ (f : T.realization.Space) (x : AdelicGL F (r + 1)),
      evaluate F (r + 1) (T.realization.toContinuous f) (AdelicGL.scalar F (r + 1) a * x) =
        evaluate F (r + 1) (T.realization.toContinuous f) x

variable {T : CuspidalOperatorRealization F r} {T' : CuspidalOperatorRealization F t}

/-- A choice of local data at every finite place for the pair L-function: a nontrivial
additive character `ψ_v` of `F_v`, a self-dual measure for it, and the JPSS pair
L-polynomial of the local components `(Π_v, Π'_v)`. -/
structure FinitePairLChoice
    (P : CuspidalSpectralPresentation.{u, uQ} T)
    (P' : CuspidalSpectralPresentation.{u, uQ} T')
    (h : HasIrreducibleAdmissibleComponents P) (h' : HasIrreducibleAdmissibleComponents P') where
  additive : ∀ v : FinitePlace F, Correspondence.NontrivialAdditiveCharacter (padicField v)
  measure : ∀ v : FinitePlace F, Correspondence.LocalAdditiveHaarMeasure (padicField v)
  measure_spec : ∀ v, Correspondence.IsSelfDualMeasure (padicField v) (additive v) (measure v)
  lPolynomial : FinitePlace F → ℂ[X]
  lPolynomial_spec : ∀ v, Correspondence.IsAutomorphicPairLPolynomial (padicField v)
    (additive v) (measure v) (localClass P h v) (localClass P' h' v) (lPolynomial v)

namespace FinitePairLChoice

variable {P : CuspidalSpectralPresentation.{u, uQ} T}
  {P' : CuspidalSpectralPresentation.{u, uQ} T'}
  {h : HasIrreducibleAdmissibleComponents P} {h' : HasIrreducibleAdmissibleComponents P'}

/-- The pair L-data contained in a choice of finite factor data for the functional
equation (`CuspidalPairFactorData`). -/
def ofFactorChoice {Td : CuspidalOperatorRealization F r}
    {Td' : CuspidalOperatorRealization F t}
    {ψ : HarmonicAnalysis.UnitaryAdditiveCharacter (Adeles F)}
    {Pd : CuspidalSpectralPresentation.{u, uQ} Td}
    {Pd' : CuspidalSpectralPresentation.{u, uQ} Td'}
    {hd : HasIrreducibleAdmissibleComponents Pd} {hd' : HasIrreducibleAdmissibleComponents Pd'}
    (c : FinitePairFactorChoice ψ P P' Pd Pd' h h' hd hd') : FinitePairLChoice P P' h h' where
  additive := c.additive
  measure := c.measure
  measure_spec := c.measure_spec
  lPolynomial := c.lPolynomial
  lPolynomial_spec := c.lPolynomial_spec

variable (c : FinitePairLChoice P P' h h')

/-- `L(s, Π_v × Π'_v) = 1 / P_v(q_v^(-s))`. -/
def finiteL (v : FinitePlace F) (s : ℂ) : ℂ :=
  ((c.lPolynomial v).eval (RankinSelberg.spectralPoint (residueCardinality v) s))⁻¹

/-- `Λ` is the completed L-function with archimedean factor `Linf`: on some right
half-plane the finite Euler product converges absolutely, and `Λ s` is `Linf s` times
its value. -/
def IsCompletedLFunction (Linf Λ : ℂ → ℂ) : Prop :=
  ∃ σ : ℝ, ∀ s : ℂ, σ < s.re →
    Summable (fun v => ‖c.finiteL v s - 1‖) ∧
      ∃ p : ℂ, HasProd (fun v => c.finiteL v s) p ∧ Λ s = Linf s * p

end FinitePairLChoice

/-- `Λ` is holomorphic off `{0, 1}`, and at `0` and at `1` it is meromorphic with at
most a simple pole; it has a pole there exactly when `cond` holds. -/
def HasSimplePoleProfile (Λ : ℂ → ℂ) (cond : Prop) : Prop :=
  DifferentiableOn ℂ Λ {0, 1}ᶜ ∧
    ∀ s ∈ ({0, 1} : Set ℂ),
      MeromorphicAt Λ s ∧ (-1 : WithTop ℤ) ≤ meromorphicOrderAt Λ s ∧
        (meromorphicOrderAt Λ s < 0 ↔ cond)

/-- `Λ` is bounded in vertical strips away from `0` and `1`: on every strip
`a ≤ Re s ≤ b`, outside the open discs of radius `ε > 0` about `0` and `1`. -/
def IsBoundedInVerticalStrips (Λ : ℂ → ℂ) : Prop :=
  ∀ a b ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ s : ℂ, a ≤ s.re → s.re ≤ b →
    ε ≤ ‖s‖ → ε ≤ ‖s - 1‖ → ‖Λ s‖ ≤ C

end CuspidalPairPoles

open CuspidalPairPoles

/-- **Getz–Hahn (2024), Theorem 11.7.1**, poles and vertical strips (Cogdell 2004,
Theorems 4.1 and 4.2), for actual cuspidal realizations.

For a number field `F` and actual cuspidal realizations `T`, `T'` of `GL_(r+1)`,
`GL_(t+1)`, both trivial on the split components of their centres, and spectral
presentations of both with irreducible admissible finite components: the finite local
L-data and the archimedean parameters of both realizations exist; and for every choice
of them there is a completed L-function `Λ(s, π × π')`, the absolutely convergent
finite Euler product times the archimedean factors on a right half-plane, that is
holomorphic off `{0, 1}`, has at most simple poles at `0` and `1`, has a pole at each of
them exactly when `r = t` and `T` realizes the contragredient of `T'`, and is bounded in
vertical strips away from `0` and `1`. -/
def CuspidalPairPoleStatement : Prop := by
  classical
  exact
  ∀ (F : Type u) [Field F] [NumberField F] [CompactSpace (AdeleQuotient F)]
    (r t : ℕ) (T : CuspidalOperatorRealization F r) (T' : CuspidalOperatorRealization F t),
    IsTrivialOnSplitCentre T → IsTrivialOnSplitCentre T' →
  ∀ (P : CuspidalSpectralPresentation.{u, uQ} T)
    (P' : CuspidalSpectralPresentation.{u, uQ} T')
    (h : HasIrreducibleAdmissibleComponents P) (h' : HasIrreducibleAdmissibleComponents P'),
    (Nonempty (FinitePairLChoice P P' h h') ∧
      (∀ v : {v : InfinitePlace F // v.IsReal},
        (∃ ds, OperatorRealization.HasRealPlaceParameter T.realization v ds) ∧
          ∃ ds, OperatorRealization.HasRealPlaceParameter T'.realization v ds) ∧
      ∀ v : {v : InfinitePlace F // v.IsComplex},
        (∃ ds, OperatorRealization.HasComplexPlaceParameter T.realization v ds) ∧
          ∃ ds, OperatorRealization.HasComplexPlaceParameter T'.realization v ds) ∧
    ∀ c : FinitePairLChoice P P' h h',
    ∀ (dR dR' : {v : InfinitePlace F // v.IsReal} → List RealBlock),
      (∀ v, OperatorRealization.HasRealPlaceParameter T.realization v (dR v)) →
      (∀ v, OperatorRealization.HasRealPlaceParameter T'.realization v (dR' v)) →
    ∀ (dC dC' : {v : InfinitePlace F // v.IsComplex} → List ComplexCharacterData),
      (∀ v, OperatorRealization.HasComplexPlaceParameter T.realization v (dC v)) →
      (∀ v, OperatorRealization.HasComplexPlaceParameter T'.realization v (dC' v)) →
    let infiniteL (s : ℂ) : ℂ :=
      (∏ v, ((realPairLFactor (dR v) (dR' v)).denominator s)⁻¹) *
        ∏ v, ((complexPairLFactor (dC v) (dC' v)).denominator s)⁻¹
    ∃ Λ : ℂ → ℂ, c.IsCompletedLFunction infiniteL Λ ∧
      HasSimplePoleProfile Λ
        (∃ hrt : r = t,
          OperatorRealization.IsContragredientOf (n := t + 1) (hrt ▸ T.realization)
            T'.realization) ∧
      IsBoundedInVerticalStrips Λ

end Langlands.Global
