import Langlands.Automorphic.AssociatedCentralCharacter.EulerTopCoefficient
import Langlands.ClassField.Global.RelativeWeilUnramifiedTwist
import Langlands.Representation.Unramified.HeckeOperators

/-! # The Hecke character of `det S` at the good places of a weak association

If `det S = δ ∘ τ_F` and `S` is weakly associated with a spectral system `s` of rank `n`, then
at cofinitely many finite places `v` of `F` the character `δ` is unramified and its value
`δ_v(ϖ_v)` at a uniformizer is the top signed Euler coefficient `z_1 ⋯ z_n` of `s` at `v`.
-/

noncomputable section

set_option autoImplicit false

open Polynomial
open scoped NumberField

universe u uV

namespace Langlands.Unramified

/-- The top signed Euler coefficient of `n` eigenvalues is their product. -/
theorem elementaryCoefficient_rank {n : ℕ} (s : Eigenvalues n) :
    elementaryCoefficient s n = (((s : Multiset ℂˣ).prod : ℂˣ) : ℂ) := by
  rw [elementaryCoefficient, Eigenvalues.eulerPolynomial_coeff_rank, ← mul_assoc, ← pow_add,
    ← two_mul, pow_mul, neg_one_sq, one_pow, one_mul]

end Langlands.Unramified

namespace Langlands.ClassField.Global.RelativeWeilGroup

open Langlands.Global Langlands.Global.AdelicFunctoriality Langlands.Global.CompletionPadic
open Langlands.Unramified

variable {F E : Type u} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  [IsGalois F E] {c : FundamentalClass.ClassFamily.{u}}

/-- At a place `v` where `S` of rank `n` matches the Euler polynomial of the eigenvalues `z`,
every place above `v` has ramification index one, and `δ` is unramified, the identity
`det S = δ ∘ τ_F` gives `δ_v(ϖ_v) = z_1 ⋯ z_n`. -/
theorem finiteUniformizerValue_eq_prod_of_isUnramifiedMatchAt
    (h : FundamentalClass.Restriction c) {n : ℕ}
    {S : FiniteRepresentation.{0, u, uV} ℂ (RelativeWeilGroup c F E)} (hn : S.rank = n)
    {v : FinitePlace F} {z : Eigenvalues n} (hm : IsUnramifiedMatchAt S v z.eulerPolynomial)
    (hram : ∀ w : FinitePlacesAbove E v, w.1.asIdeal.ramificationIdx (𝓞 F) = 1)
    (δ : HeckeCharacter F) (hδv : δ.IsUnramifiedAt v)
    (hδ : FiniteRepresentation.determinantCharacter S = reciprocityCharacter c F E δ) :
    δ.finiteUniformizerValue v = (z : Multiset ℂˣ).prod := by
  let w : FinitePlacesAbove E v := placeAbove E v
  obtain ⟨e, ι, hι⟩ := (hm w).1
  have hdet := hm.determinantCharacter_eq_prod hn w e ι hι
  rw [hδ, reciprocityCharacter_eq_finiteUniformizerValue c v w.1 h (hram w) δ hδv e ι hι _
    (Weil.Local.localGeometricFrobenius_degree (padicField v))] at hdet
  exact hdet

/-- If `det S = δ ∘ τ_F` and `S` is weakly associated with `s` of rank `n`, then at
cofinitely many finite places `v` the character `δ` is unramified, `s` is defined, and
`δ_v(ϖ_v)` is the top signed Euler coefficient of the spectrum of `s` at `v`. -/
theorem eventually_finiteUniformizerValue_eq_elementaryCoefficient
    (hc : IsArithmeticClassFamily c) {n : ℕ}
    {S : FiniteRepresentation.{0, u, uV} ℂ (RelativeWeilGroup c F E)}
    {s : SpectralSystem (FinitePlace F) n} (hS : IsWeaklyAssociated S s)
    (δ : HeckeCharacter F)
    (hδ : FiniteRepresentation.determinantCharacter S = reciprocityCharacter c F E δ) :
    ∀ᶠ v in Filter.cofinite, δ.IsUnramifiedAt v ∧ ∃ hs : v ∉ s.exceptional,
      (δ.finiteUniformizerValue v : ℂ) = elementaryCoefficient (s.eigenvalues v hs) n := by
  obtain ⟨_, _, _, hres, _, _⟩ := hc
  obtain ⟨_, hn, hev⟩ := hS
  obtain ⟨T, hT⟩ := HeckeFunctionalEquation.exists_finset_isUnramifiedAt (K := F) δ
  filter_upwards [hev, eventually_ramificationIdx_eq_one (K := F) (L := E),
    T.eventually_cofinite_notMem] with v hv hram hvT
  obtain ⟨hs, hm⟩ := hv
  refine ⟨hT v hvT, hs, ?_⟩
  rw [elementaryCoefficient_rank,
    finiteUniformizerValue_eq_prod_of_isUnramifiedMatchAt hres hn hm (fun w => hram w.1 w.2)
      δ (hT v hvT) hδ]

end Langlands.ClassField.Global.RelativeWeilGroup
