import Langlands.Global.Factors.CuspidalPairPoleStatement
import Langlands.Global.RankinSelberg.PartialEqualWhittakerIntegral
import Langlands.Global.RankinSelberg.UnequalIntegrals

/-!
# Semi-local ratios of partial Rankin–Selberg integrals

Cogdell (2004), proof of Theorem 4.1 (printed p.219) and §4.2 (printed pp.221–222), with the
local theory of Theorem 3.1 (p.213) and Theorem 3.5 (p.217): for cuspidal realizations `T`,
`T'` and a finite set `S` of finite places containing the ramification, every partial
Whittaker integral `Ψ_(S∪∞)` with data spherical outside `S` is an entire function `E` times
`L_(S∪∞)(s) = L_∞(s) ∏_(v ∈ S) L(s, Π_v × Π'_v)` on a right half-plane independent of the
datum, and for every point `s₀` some such datum has `E(s₀) ≠ 0`. Proposition definition only. See the paired Markdown
for sources, normalizations and the scope.
-/

noncomputable section

set_option autoImplicit false

open Polynomial

universe u uQ

namespace Langlands.Global

open NumberField
open RankinSelbergGlobal
open Automorphic (CuspidalOperatorRealization CuspidalSpectralPresentation OperatorRealization)
open CuspidalPairFunctionalEquation (HasIrreducibleAdmissibleComponents)
open LocalFactor.Archimedean

namespace CuspidalPairPoles

/-- The family `Ψ i`, over the data `i` with `good i`, has the semi-local ratio property for
`L`: there is a half-plane `σ < Re s` on which every good datum gives `Ψ i = E · L` with `E`
entire, and for every point `s₀` some good datum has such an `E` with `E(s₀) ≠ 0`. -/
def IsSemilocalRatioFamily {ι : Type*} (good : ι → Prop) (Ψ : ι → ℂ → ℂ) (L : ℂ → ℂ) :
    Prop :=
  ∃ σ : ℝ,
    (∀ i, good i → ∃ E : ℂ → ℂ, Differentiable ℂ E ∧
      ∀ s : ℂ, σ < s.re → Ψ i s = E s * L s) ∧
    ∀ s₀ : ℂ, ∃ i, good i ∧ ∃ E : ℂ → ℂ, Differentiable ℂ E ∧ E s₀ ≠ 0 ∧
      ∀ s : ℂ, σ < s.re → Ψ i s = E s * L s

end CuspidalPairPoles

open CuspidalPairPoles

/-- **Semi-local ratios** (Cogdell (2004), proof of Theorem 4.1, p.219, and §4.2,
pp.221–222, with Theorems 3.1 and 3.5).

Let `ψ` be a nontrivial unitary character of `𝔸` trivial on `F`, `T`, `T'` actual cuspidal
realizations of `GL_(r+1)`, `GL_(t+1)` with spectral presentations `P`, `P'` with
irreducible admissible finite components, `S` a finite set of finite places containing both
exceptional sets outside which `ψ_v` has conductor `𝒪_v`, `c` a choice of finite pair
L-data and `dR`, `dR'`, `dC`, `dC'` archimedean parameters of `T`, `T'`. Put
`L_(S∪∞)(s) = L_∞(s) ∏_(v ∈ S) L(s, Π_v × Π'_v)`. Then, with `W = W_x` the `ψ`-Whittaker
function of the larger group and `W' = W'_x'` the `ψ⁻¹`-Whittaker function of the other one,
the partial integrals `Ψ_(S∪∞)(s; W, W', Φ)` (`r = t`, `Φ` Schwartz–Bruhat and standard
outside `S`) and `Ψ_(S∪∞)(s; W, W')` (`r ≠ t`), over vectors fixed by `GL(𝒪_v)` at every
finite `v ∉ S`, form a family with the semi-local ratio property for `L_(S∪∞)`. -/
def CuspidalPairSemilocalRatioStatement : Prop := by
  classical
  exact
  ∀ (F : Type u) [Field F] [NumberField F] [CompactSpace (AdeleQuotient F)]
    (ψ : HarmonicAnalysis.UnitaryAdditiveCharacter (Adeles F)),
    (∀ x : F, ψ (algebraMap F (Adeles F) x) = 1) →
  ∀ (r t : ℕ) (T : CuspidalOperatorRealization F r) (T' : CuspidalOperatorRealization F t)
    (P : CuspidalSpectralPresentation.{u, uQ} T)
    (P' : CuspidalSpectralPresentation.{u, uQ} T')
    (h : HasIrreducibleAdmissibleComponents P) (h' : HasIrreducibleAdmissibleComponents P')
    (S : Finset (FinitePlace F)), P.exceptional ⊆ S → P'.exceptional ⊆ S →
    FunctionalEquationComparison.FiniteAdditiveSupport ψ S →
  ∀ (c : FinitePairLChoice P P' h h')
    (dR dR' : {v : InfinitePlace F // v.IsReal} → List RealBlock),
    (∀ v, OperatorRealization.HasRealPlaceParameter T.realization v (dR v)) →
    (∀ v, OperatorRealization.HasRealPlaceParameter T'.realization v (dR' v)) →
  ∀ (dC dC' : {v : InfinitePlace F // v.IsComplex} → List ComplexCharacterData),
    (∀ v, OperatorRealization.HasComplexPlaceParameter T.realization v (dC v)) →
    (∀ v, OperatorRealization.HasComplexPlaceParameter T'.realization v (dC' v)) →
  let semilocalL (s : ℂ) : ℂ :=
    ((∏ v, ((realPairLFactor (dR v) (dR' v)).denominator s)⁻¹) *
      ∏ v, ((complexPairLFactor (dC v) (dC' v)).denominator s)⁻¹) *
      ∏ v ∈ S, c.finiteL v s
  (∀ hrt : r = t,
    IsSemilocalRatioFamily
      (fun d : T.Space × T'.Space × (RowVector F (r + 1) → ℂ) =>
        IsSphericalOutside F T S d.1 ∧ IsSphericalOutside F T' S d.2.1 ∧
          d.2.2 ∈ schwartzBruhat F (r + 1) ∧ IsStandardOutside F (r + 1) S d.2.2)
      (fun d s => partialEqualWhittakerIntegral F S (cuspWhittaker F T ψ.complex d.1)
        (hrt ▸ cuspWhittaker F T' ψ.complex⁻¹ d.2.1) d.2.2 s)
      semilocalL) ∧
  (∀ hlt : t < r,
    IsSemilocalRatioFamily
      (fun d : T.Space × T'.Space => IsSphericalOutside F T S d.1 ∧ IsSphericalOutside F T' S d.2)
      (fun d s => partialUnequalWhittakerIntegral F hlt S (cuspWhittaker F T ψ.complex d.1)
        (cuspWhittaker F T' ψ.complex⁻¹ d.2) s)
      semilocalL) ∧
  ∀ hlt : r < t,
    IsSemilocalRatioFamily
      (fun d : T.Space × T'.Space => IsSphericalOutside F T S d.1 ∧ IsSphericalOutside F T' S d.2)
      (fun d s => partialUnequalWhittakerIntegral F hlt S (cuspWhittaker F T' ψ.complex d.2)
        (cuspWhittaker F T ψ.complex⁻¹ d.1) s)
      semilocalL

end Langlands.Global
