import Langlands.Automorphic.CuspidalArithmeticSpectralTransportStatement
import Langlands.Automorphic.Unramified.PrimeCyclicBaseChangeTower
import Langlands.Automorphic.Unramified.IsobaricSpectralUniqueness

/-!
# Arithmetic pullback of isobaric data carries attached spectral systems

Assume the cuspidal transport statement
`CuspidalArithmeticSpectralTransportStatement`: along a field isomorphism `e : K ≃+* L`, the
pullback of a cuspidal class over `L` has an attached spectral system whose Euler
polynomials at almost every finite place `v` of `K` are those of the original class at the
corresponding place of `L`. Applying it to every constituent gives the same statement for
isobaric constituent data.
-/

noncomputable section

universe uI uK uL uV

set_option autoImplicit false

namespace Langlands.Unramified.SpectralSystem

variable {I : Type uI}

/-- The rank cast `h ▸ s` keeps every Euler polynomial. -/
theorem eulerPolynomial_eqRec {n m : ℕ} (h : n = m) (s : SpectralSystem I n) (v : I)
    (hv : v ∉ (h ▸ s : SpectralSystem I m).exceptional) (hv' : v ∉ s.exceptional) :
    (h ▸ s : SpectralSystem I m).eulerPolynomial v hv = s.eulerPolynomial v hv' := by
  subst h
  rfl

end Langlands.Unramified.SpectralSystem

namespace Langlands.Automorphic

open Langlands.Global Langlands.Global.AdelicFunctoriality Langlands.Unramified

namespace IsobaricData

variable {K : Type uK} {L : Type uL} [Field K] [NumberField K] [Field L] [NumberField L]
  [CompactSpace (AdeleQuotient K)] [CompactSpace (AdeleQuotient L)]

/-- The constituent enumeration of the pullback is the pullback of an enumeration. -/
theorem map_arithmeticComap_eq {k : ℕ} (e : K ≃+* L) {D : IsobaricData L}
    {σ : Fin k → PositiveRankCuspidalClass L} (hσ : Finset.univ.val.map σ = D) :
    Finset.univ.val.map (fun j => (σ j).arithmeticComap e) = D.arithmeticComap e := by
  rw [← hσ, IsobaricData.arithmeticComap, Multiset.map_map]
  rfl

/-- The rank of the pullback is the sum of the ranks of an enumeration. -/
theorem sum_rank_arithmeticComap_eq {k : ℕ} (e : K ≃+* L) {D : IsobaricData L}
    {σ : Fin k → PositiveRankCuspidalClass L} (hσ : Finset.univ.val.map σ = D) :
    (∑ j, ((σ j).arithmeticComap e).rank) = (D.arithmeticComap e).rank := by
  rw [rank_eq_sum, ← map_arithmeticComap_eq e hσ, Multiset.map_map,
    Finset.sum_eq_multiset_sum]
  rfl

/-- Under the cuspidal transport statement, the pullback of isobaric data along
`e : K ≃+* L` has an attached spectral system whose Euler polynomial at almost every finite
place `v` of `K` is that of the original system at `(finitePlaceEquiv e).symm v`. -/
theorem HasSpectralSystem.arithmeticComap
    (hP : CuspidalArithmeticSpectralTransportStatement.{uK, uL, uV})
    (e : K ≃+* L) {D : IsobaricData L} {s : SpectralSystem (FinitePlace L) D.rank}
    (hs : HasSpectralSystem.{uL, uV} D s) :
    ∃ s' : SpectralSystem (FinitePlace K) (D.arithmeticComap e).rank,
      HasSpectralSystem.{uK, uV} (D.arithmeticComap e) s' ∧
        ∀ᶠ v in Filter.cofinite, ∀ (hv : v ∉ s'.exceptional)
          (hw : (finitePlaceEquiv e).symm v ∉ s.exceptional),
          s'.eulerPolynomial v hv = s.eulerPolynomial ((finitePlaceEquiv e).symm v) hw := by
  classical
  obtain ⟨k, σ, hσ, t, ht, hts⟩ := hs
  choose t' ht' hEuler using fun j => hP K L e (σ j).1 (σ j).2 (t j) (ht j)
  let σ' : Fin k → PositiveRankCuspidalClass K := fun j => (σ j).arithmeticComap e
  let t'' : ∀ j, SpectralSystem (FinitePlace K) (σ' j).rank := fun j => t' j
  have hrank : (∑ j, (σ' j).rank) = (D.arithmeticComap e).rank :=
    sum_rank_arithmeticComap_eq e hσ
  let s' : SpectralSystem (FinitePlace K) (D.arithmeticComap e).rank :=
    hrank ▸ SpectralSystem.finiteSum t''
  have hex : s'.exceptional = SpectralSystem.familyExceptional t'' :=
    SpectralSystem.exceptional_eqRec hrank _
  refine ⟨s', ⟨k, σ', map_arithmeticComap_eq e hσ, t'', fun j => ht' j,
    Filter.Eventually.of_forall fun v hv hv' =>
      (SpectralSystem.eulerPolynomial_eqRec hrank _ v hv' hv).symm⟩, ?_⟩
  let w : FinitePlace K ≃ FinitePlace L := (finitePlaceEquiv e).symm
  have htend : Filter.Tendsto w Filter.cofinite Filter.cofinite := w.injective.tendsto_cofinite
  have hall : ∀ᶠ v in Filter.cofinite, ∀ j, ∀ (hv : v ∉ (t' j).exceptional)
      (hw : w v ∉ (t j).exceptional),
      (t' j).eulerPolynomial v hv = (t j).eulerPolynomial (w v) hw :=
    Filter.eventually_all.mpr hEuler
  filter_upwards [hall, htend.eventually hts,
    htend.eventually (SpectralSystem.familyExceptional t).eventually_cofinite_notMem]
    with v hall hts hnot
  intro hv hw
  have hv0 : v ∉ SpectralSystem.familyExceptional t'' := hex ▸ hv
  calc s'.eulerPolynomial v hv
      = (SpectralSystem.finiteSum t'').eulerPolynomial v hv0 :=
        SpectralSystem.eulerPolynomial_eqRec hrank _ v hv hv0
    _ = ∏ j, (t'' j).eulerPolynomial v (SpectralSystem.not_mem_exceptional t'' v hv0 j) :=
        SpectralSystem.finiteSum_eulerPolynomial t'' v hv0
    _ = ∏ j, (t j).eulerPolynomial (w v) (SpectralSystem.not_mem_exceptional t (w v) hnot j) :=
        Finset.prod_congr rfl fun j _ => hall j _ _
    _ = (SpectralSystem.finiteSum t).eulerPolynomial (w v) hnot :=
        (SpectralSystem.finiteSum_eulerPolynomial t (w v) hnot).symm
    _ = s.eulerPolynomial (w v) hw := hts hnot hw

end IsobaricData

end Langlands.Automorphic
