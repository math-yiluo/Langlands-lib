import Langlands.Automorphic.Unramified.IsobaricWeakTransfer
import Langlands.Automorphic.AssociatedPresentationSpectrum

/-!
# Uniqueness of the spectral systems attached to isobaric data

Two numerical spectral systems attached to the same cuspidal class have the same spectrum
at every place where both are defined. Consequently two systems attached to the same
isobaric constituent data have the same Euler polynomials outside a finite set. The file
also records how the rank cast used by `IsobaricData.IsWeakBaseChangeOf` acts on spectra.
-/

noncomputable section

universe uI uF uV uW

set_option autoImplicit false

namespace Langlands.Unramified.SpectralSystem

variable {I : Type uI}

/-- The rank cast `h ▸ s` keeps the exceptional set. -/
theorem exceptional_eqRec {n m : ℕ} (h : n = m) (s : SpectralSystem I n) :
    (h ▸ s : SpectralSystem I m).exceptional = s.exceptional := by
  subst h
  rfl

/-- The rank cast `h ▸ s` keeps every spectrum, read as a multiset. -/
theorem coe_eigenvalues_eqRec {n m : ℕ} (h : n = m) (s : SpectralSystem I n) (v : I)
    (hv : v ∉ (h ▸ s : SpectralSystem I m).exceptional) (hv' : v ∉ s.exceptional) :
    (((h ▸ s : SpectralSystem I m).eigenvalues v hv : Eigenvalues m) : Multiset ℂˣ) =
      ((s.eigenvalues v hv' : Eigenvalues n) : Multiset ℂˣ) := by
  subst h
  rfl

end Langlands.Unramified.SpectralSystem

namespace Langlands.Automorphic

open Langlands.Global Langlands.Unramified

variable {F : Type uF} [Field F] [NumberField F] [CompactSpace (AdeleQuotient F)]

namespace CuspidalOperatorRealization.IsoClass

/-- Two spectral systems attached to the same cuspidal class, through presentations with
local factors in possibly different universes, have the same spectrum at every place where
both are defined. -/
theorem HasSpectralSystem.eigenvalues_eq {r : ℕ} {c : IsoClass F r}
    {s t : SpectralSystem (FinitePlace F) (r + 1)}
    (hs : HasSpectralSystem.{uF, uV} c s) (ht : HasSpectralSystem.{uF, uW} c t)
    (v : FinitePlace F) (hsv : v ∉ s.exceptional) (htv : v ∉ t.exceptional) :
    s.eigenvalues v hsv = t.eigenvalues v htv := by
  obtain ⟨S, P, rfl, rfl⟩ := hs
  obtain ⟨Q, rfl⟩ := (hasSpectralSystem_iff S t).mp ht
  exact P.spectralSystem_eigenvalues_eq Q v hsv htv

end CuspidalOperatorRealization.IsoClass

namespace IsobaricData

/-- Spectral systems attached to equal positive-rank classes have equal Euler polynomials
wherever both are defined. -/
theorem eulerPolynomial_eq_of_hasSpectralSystem {c c' : PositiveRankCuspidalClass F}
    (h : c = c') {t : SpectralSystem (FinitePlace F) c.rank}
    {t' : SpectralSystem (FinitePlace F) c'.rank}
    (ht : PositiveRankCuspidalClass.HasSpectralSystem.{uF, uV} c t)
    (ht' : PositiveRankCuspidalClass.HasSpectralSystem.{uF, uW} c' t')
    (v : FinitePlace F) (hv : v ∉ t.exceptional) (hv' : v ∉ t'.exceptional) :
    t.eulerPolynomial v hv = t'.eulerPolynomial v hv' := by
  subst h
  exact congrArg Eigenvalues.eulerPolynomial
    (CuspidalOperatorRealization.IsoClass.HasSpectralSystem.eigenvalues_eq ht ht' v hv hv')

/-- Two spectral systems attached to the same isobaric data have the same Euler polynomials
outside a finite set. -/
theorem HasSpectralSystem.sameEulerPolynomials {D : IsobaricData F}
    {s s' : SpectralSystem (FinitePlace F) D.rank}
    (hs : HasSpectralSystem.{uF, uV} D s) (hs' : HasSpectralSystem.{uF, uW} D s') :
    s.SameEulerPolynomials s' := by
  classical
  obtain ⟨k, σ, hσ, t, ht, hts⟩ := hs
  obtain ⟨k', σ', hσ', t', ht', hts'⟩ := hs'
  refine hts.symm.trans (SpectralSystem.SameEulerPolynomials.trans ?_ hts')
  refine Filter.Eventually.of_forall fun v hv hv' => ?_
  refine (SpectralSystem.finiteSum_eulerPolynomial t v hv).trans
    (Eq.trans ?_ (SpectralSystem.finiteSum_eulerPolynomial t' v hv').symm)
  let g : PositiveRankCuspidalClass F → Polynomial ℂ := fun c =>
    if h : ∃ j, σ j = c then
      (t h.choose).eulerPolynomial v (SpectralSystem.not_mem_exceptional t v hv h.choose)
    else 1
  have hg : ∀ (j : Fin k), σ j = σ j → (t j).eulerPolynomial v
      (SpectralSystem.not_mem_exceptional t v hv j) = g (σ j) := by
    intro j _
    have hex : ∃ i, σ i = σ j := ⟨j, rfl⟩
    simp only [g, hex, ↓reduceDIte]
    exact eulerPolynomial_eq_of_hasSpectralSystem hex.choose_spec.symm (ht j) (ht _) v _ _
  have hg' : ∀ j' : Fin k', (t' j').eulerPolynomial v
      (SpectralSystem.not_mem_exceptional t' v hv' j') = g (σ' j') := by
    intro j'
    have hmem : σ' j' ∈ D := hσ' ▸ Multiset.mem_map_of_mem σ' (Finset.mem_univ_val j')
    rw [← hσ] at hmem
    obtain ⟨i, -, hi⟩ := Multiset.mem_map.mp hmem
    have hex : ∃ i, σ i = σ' j' := ⟨i, hi⟩
    simp only [g, hex, ↓reduceDIte]
    exact eulerPolynomial_eq_of_hasSpectralSystem hex.choose_spec.symm (ht' j') (ht _) v _ _
  have hprod : ∀ {m : ℕ} (τ : Fin m → PositiveRankCuspidalClass F),
      Finset.univ.val.map τ = D → ∏ j, g (τ j) = (D.map g).prod := by
    intro m τ hτ
    rw [← hτ, Multiset.map_map, Finset.prod_eq_multiset_prod]
    rfl
  calc ∏ j, (t j).eulerPolynomial v (SpectralSystem.not_mem_exceptional t v hv j)
      = ∏ j, g (σ j) := Finset.prod_congr rfl fun j _ => hg j rfl
    _ = (D.map g).prod := hprod σ hσ
    _ = ∏ j', g (σ' j') := (hprod σ' hσ').symm
    _ = _ := Finset.prod_congr rfl fun j' _ => (hg' j').symm

/-- Two spectral systems attached to the same isobaric data have the same spectra outside a
finite set. -/
theorem HasSpectralSystem.eventually_eigenvalues_eq {D : IsobaricData F}
    {s s' : SpectralSystem (FinitePlace F) D.rank}
    (hs : HasSpectralSystem.{uF, uV} D s) (hs' : HasSpectralSystem.{uF, uW} D s') :
    ∀ᶠ v in Filter.cofinite, ∀ (hv : v ∉ s.exceptional) (hv' : v ∉ s'.exceptional),
      s.eigenvalues v hv = s'.eigenvalues v hv' :=
  (hs.sameEulerPolynomials hs').mono fun _ h hv hv' =>
    Eigenvalues.eulerPolynomial_injective (h hv hv')

end IsobaricData

end Langlands.Automorphic
