import Langlands.Global.Factors.CuspidalPairPoleStatement

/-!
# The pole order at `s = 1` of `L(s, π₀ × (π₁ ⊞ ⋯ ⊞ π_k))`

Getz–Hahn (2024), Lemma 11.8.1, for actual cuspidal realizations over a number field that
are trivial on the split components `A_GL` of their centres. By Getz–Hahn's convention
(§11.8, p.312) the L-function of `π₀` against the isobaric sum `π₁ ⊞ ⋯ ⊞ π_k` is the
product of the completed pair L-functions `Λ(s, π₀ × π_i)`. Its pole at `s = 1` has order
equal to the number of `i` with `π_i ≅ π₀^∨`. The pair L-functions are those of
`Langlands.Global.CuspidalPairPoleStatement`. See the paired Markdown for sources,
normalizations and the scope.
-/

noncomputable section

set_option autoImplicit false

universe u uQ

namespace Langlands.Global

open NumberField
open Automorphic (CuspidalOperatorRealization CuspidalSpectralPresentation OperatorRealization)
open CuspidalPairFunctionalEquation (HasIrreducibleAdmissibleComponents)
open LocalFactor.Archimedean
open CuspidalPairPoles

namespace CuspidalIsobaricPoles

/-- `f` has a pole of order exactly `m` at `s`, and no pole when `m = 0`: the negative
part `min (ord_s f) 0` of the meromorphic order of `f` at `s` is `-m`. -/
def HasPoleOrder (f : ℂ → ℂ) (s : ℂ) (m : ℕ) : Prop :=
  min (meromorphicOrderAt f s) 0 = (((-(m : ℤ)) : ℤ) : WithTop ℤ)

variable {F : Type u} [Field F] [NumberField F] [CompactSpace (AdeleQuotient F)]

/-- The multiplicity of `π₀^∨` in `π₁ ⊞ ⋯ ⊞ π_k` (Getz–Hahn p.312): the number of
indices `i` such that the ranks agree and `T i` realizes the contragredient of `T₀`. -/
def contragredientMultiplicity {r₀ k : ℕ} (T₀ : CuspidalOperatorRealization F r₀)
    {r : Fin k → ℕ} (T : ∀ i, CuspidalOperatorRealization F (r i)) : ℕ :=
  Nat.card {i : Fin k // ∃ hr : r₀ = r i,
    OperatorRealization.IsContragredientOf (n := r i + 1) (T i).realization
      (hr ▸ T₀.realization)}

end CuspidalIsobaricPoles

open CuspidalIsobaricPoles

/-- **Getz–Hahn (2024), Lemma 11.8.1**, for actual cuspidal realizations.

For a number field `F`, an actual cuspidal realization `T₀` of `GL_(r₀+1)` and a finite
family `T 0, …, T (k-1)` of actual cuspidal realizations of `GL_(r i + 1)`, all trivial on
the split components of their centres, and spectral presentations of all of them with
irreducible admissible finite components: the finite local pair L-data of each pair
`(T₀, T i)` and the archimedean parameters of all realizations exist; for every choice of
them each completed pair L-function `Λ(s, π₀ × π_i)` exists as a meromorphic function on
`ℂ`; and for every family of such functions their product has at `s = 1` a pole whose
order is the number of `i` such that `T i` realizes the contragredient of `T₀` (no pole if
there is no such `i`). -/
def CuspidalIsobaricPoleOrderStatement : Prop := by
  classical
  exact
  ∀ (F : Type u) [Field F] [NumberField F] [CompactSpace (AdeleQuotient F)]
    (r₀ : ℕ) (T₀ : CuspidalOperatorRealization F r₀)
    (k : ℕ) (r : Fin k → ℕ) (T : ∀ i, CuspidalOperatorRealization F (r i)),
    IsTrivialOnSplitCentre T₀ → (∀ i, IsTrivialOnSplitCentre (T i)) →
  ∀ (P₀ : CuspidalSpectralPresentation.{u, uQ} T₀)
    (P : ∀ i, CuspidalSpectralPresentation.{u, uQ} (T i))
    (h₀ : HasIrreducibleAdmissibleComponents P₀)
    (h : ∀ i, HasIrreducibleAdmissibleComponents (P i)),
    ((∀ i, Nonempty (FinitePairLChoice P₀ (P i) h₀ (h i))) ∧
      (∀ v : {v : InfinitePlace F // v.IsReal},
        (∃ ds, OperatorRealization.HasRealPlaceParameter T₀.realization v ds) ∧
          ∀ i, ∃ ds, OperatorRealization.HasRealPlaceParameter (T i).realization v ds) ∧
      ∀ v : {v : InfinitePlace F // v.IsComplex},
        (∃ ds, OperatorRealization.HasComplexPlaceParameter T₀.realization v ds) ∧
          ∀ i, ∃ ds, OperatorRealization.HasComplexPlaceParameter (T i).realization v ds) ∧
    ∀ c : ∀ i, FinitePairLChoice P₀ (P i) h₀ (h i),
    ∀ (dR₀ : {v : InfinitePlace F // v.IsReal} → List RealBlock)
      (dR : Fin k → {v : InfinitePlace F // v.IsReal} → List RealBlock),
      (∀ v, OperatorRealization.HasRealPlaceParameter T₀.realization v (dR₀ v)) →
      (∀ i v, OperatorRealization.HasRealPlaceParameter (T i).realization v (dR i v)) →
    ∀ (dC₀ : {v : InfinitePlace F // v.IsComplex} → List ComplexCharacterData)
      (dC : Fin k → {v : InfinitePlace F // v.IsComplex} → List ComplexCharacterData),
      (∀ v, OperatorRealization.HasComplexPlaceParameter T₀.realization v (dC₀ v)) →
      (∀ i v, OperatorRealization.HasComplexPlaceParameter (T i).realization v (dC i v)) →
    let infiniteL (i : Fin k) (s : ℂ) : ℂ :=
      (∏ v, ((realPairLFactor (dR₀ v) (dR i v)).denominator s)⁻¹) *
        ∏ v, ((complexPairLFactor (dC₀ v) (dC i v)).denominator s)⁻¹
    let IsPairLFunction (i : Fin k) (Λ : ℂ → ℂ) : Prop :=
      MeromorphicOn Λ Set.univ ∧ (c i).IsCompletedLFunction (infiniteL i) Λ
    (∃ Λ : Fin k → ℂ → ℂ, ∀ i, IsPairLFunction i (Λ i)) ∧
    ∀ Λ : Fin k → ℂ → ℂ, (∀ i, IsPairLFunction i (Λ i)) →
      HasPoleOrder (fun s => ∏ i, Λ i s) 1 (contragredientMultiplicity T₀ T)

end Langlands.Global
