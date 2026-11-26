import Langlands.Automorphic.Unramified.IsobaricWeakBaseChangeTransportStatement
import Langlands.Automorphic.Unramified.CuspidalSpectralArithmeticComapProof
import Langlands.Automorphic.Unramified.IsobaricArithmeticSpectralTransport

/-!
# Equivariance of attached weak base change under compatible automorphisms

Let `e : K ≃+* K'` and `f : L ≃+* L'` be isomorphisms of number fields forming a
commuting square with the algebra maps `K → L` and `K' → L'`. The isomorphism `f`
carries the primes of `L'` above a prime `v` of `K'` to the primes of `L` above the
corresponding prime of `K`, with the same ramification indices and residue degrees.
Reindexing spectral systems along these bijections therefore preserves arithmetic
weak base change.

Arithmetic pullback of every constituent of isobaric data carries an attached
spectral system to its reindexed system, through the exact cuspidal statement
`cuspidalSpectralArithmeticComap`. Together these prove
`IsobaricWeakBaseChangeEquivarianceStatement`, the weak part of Arthur–Clozel,
*Simple algebras, base change, and the advanced theory of the trace formula* (1989),
Chapter 3, Proposition 4.4(iii), printed pp. 210–211, for the weak lifting of
III.1.1, printed p. 199.
-/

noncomputable section

universe uI uJ uK uL uK' uL' uF uE uV uW

set_option autoImplicit false

namespace Langlands.Global.AdelicFunctoriality

open NumberField
open scoped NumberField

section PlaceTransport

/-- The finite-place bijection of the inverse isomorphism is the inverse bijection. -/
theorem finitePlaceEquiv_symm {A : Type uK} {B : Type uL} [Field A] [Field B] (g : A ≃+* B) :
    finitePlaceEquiv g.symm = (finitePlaceEquiv g).symm := by
  apply Equiv.ext
  intro v
  apply (finitePlaceEquiv g).injective
  rw [Equiv.apply_symm_apply, ← Equiv.trans_apply, ← finitePlaceEquiv_trans,
    RingEquiv.self_trans_symm, finitePlaceEquiv_refl, Equiv.refl_apply]

/-- Pushing forward the ideal of a pulled-back place recovers the place. -/
theorem map_finitePlaceEquiv_asIdeal {A : Type uK} {B : Type uL} [Field A] [Field B]
    (g : A ≃+* B) (v : FinitePlace B) :
    (finitePlaceEquiv g v).asIdeal.map (RingOfIntegers.mapRingEquiv g).toRingHom =
      v.asIdeal :=
  Ideal.map_comap_of_surjective _ (RingOfIntegers.mapRingEquiv g).surjective _

variable {K : Type uK} {L : Type uL} {K' : Type uK'} {L' : Type uL'}
  [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [Field K'] [NumberField K'] [Field L'] [NumberField L'] [Algebra K' L']
  (e : K ≃+* K') (f : L ≃+* L')
  (he : ∀ x, f (algebraMap K L x) = algebraMap K' L' (e x))

include he in
omit [NumberField K] [NumberField L] [NumberField K'] [NumberField L'] in
/-- The commuting square restricts to the rings of integers. -/
theorem mapRingEquiv_algebraMap_of_comm (x : 𝓞 K) :
    RingOfIntegers.mapRingEquiv f (algebraMap (𝓞 K) (𝓞 L) x) =
      algebraMap (𝓞 K') (𝓞 L') (RingOfIntegers.mapRingEquiv e x) :=
  RingOfIntegers.ext (he (x : K))

include he in
omit [NumberField K] [NumberField L] [NumberField K'] [NumberField L'] in
/-- A prime of `L'` above a prime `v` of `K'` corresponds under `f` to a prime of `L`
above the prime of `K` corresponding to `v` under `e`. -/
theorem liesOver_finitePlaceEquiv_of_comm (v : FinitePlace K') (w : FinitePlace L')
    [w.asIdeal.LiesOver v.asIdeal] :
    (finitePlaceEquiv f w).asIdeal.LiesOver (finitePlaceEquiv e v).asIdeal := by
  refine ⟨?_⟩
  ext x
  rw [Ideal.mem_under, finitePlaceEquiv_mem, finitePlaceEquiv_mem,
    mapRingEquiv_algebraMap_of_comm e f he, ← Ideal.mem_under,
    Ideal.LiesOver.over (P := w.asIdeal) (p := v.asIdeal)]

include he in
/-- The commuting square preserves residue degrees of primes above a prime. -/
theorem inertiaDeg_finitePlaceEquiv_of_comm (v : FinitePlace K') (w : FinitePlace L')
    [w.asIdeal.LiesOver v.asIdeal] :
    (finitePlaceEquiv f w).asIdeal.inertiaDeg (𝓞 K) = w.asIdeal.inertiaDeg (𝓞 K') := by
  let := liesOver_finitePlaceEquiv_of_comm e f he v w
  rw [Ideal.inertiaDeg_eq_of_isMaximal (finitePlaceEquiv e v).asIdeal,
    Ideal.inertiaDeg_eq_of_isMaximal v.asIdeal]
  let ev := Ideal.quotientEquiv (finitePlaceEquiv e v).asIdeal v.asIdeal
    (RingOfIntegers.mapRingEquiv e) (map_finitePlaceEquiv_asIdeal e v).symm
  let fw := Ideal.quotientEquiv (finitePlaceEquiv f w).asIdeal w.asIdeal
    (RingOfIntegers.mapRingEquiv f) (map_finitePlaceEquiv_asIdeal f w).symm
  apply Algebra.finrank_eq_of_equiv_equiv ev fw
  apply RingHom.ext
  intro x
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
  change Ideal.Quotient.mk w.asIdeal
      (algebraMap (𝓞 K') (𝓞 L') (RingOfIntegers.mapRingEquiv e y)) =
    Ideal.Quotient.mk w.asIdeal (RingOfIntegers.mapRingEquiv f (algebraMap (𝓞 K) (𝓞 L) y))
  rw [mapRingEquiv_algebraMap_of_comm e f he]

include he in
omit [NumberField K] [NumberField K'] in
/-- The commuting square preserves ramification indices of primes above a prime. -/
theorem ramificationIdx_finitePlaceEquiv_of_comm (v : FinitePlace K') (w : FinitePlace L')
    [w.asIdeal.LiesOver v.asIdeal] :
    (finitePlaceEquiv f w).asIdeal.ramificationIdx (𝓞 K) =
      w.asIdeal.ramificationIdx (𝓞 K') := by
  let := liesOver_finitePlaceEquiv_of_comm e f he v w
  let g := RingOfIntegers.mapRingEquiv f
  let m : Ideal (𝓞 L) ≃* Ideal (𝓞 L') :=
    { (Ideal.relIsoOfBijective g.toRingHom g.bijective).symm.toEquiv with
      map_mul' := fun I J => Ideal.map_mul _ _ _ }
  have hmap (I : Ideal (𝓞 L)) : m I = I.map g.toRingHom := rfl
  have hc : g.toRingHom.comp (algebraMap (𝓞 K) (𝓞 L)) =
      (algebraMap (𝓞 K') (𝓞 L')).comp (RingOfIntegers.mapRingEquiv e).toRingHom :=
    RingHom.ext (mapRingEquiv_algebraMap_of_comm e f he)
  rw [Ideal.IsDedekindDomain.ramificationIdx_eq_multiplicity (finitePlaceEquiv e v).asIdeal
        _ (Ideal.map_ne_bot_of_ne_bot (finitePlaceEquiv e v).ne_bot),
      Ideal.IsDedekindDomain.ramificationIdx_eq_multiplicity v.asIdeal
        _ (Ideal.map_ne_bot_of_ne_bot v.ne_bot), ← multiplicity_map_eq m, hmap, hmap,
      map_finitePlaceEquiv_asIdeal f w, Ideal.map_map, hc, ← Ideal.map_map,
      map_finitePlaceEquiv_asIdeal e v]

end PlaceTransport

end Langlands.Global.AdelicFunctoriality

namespace Langlands.Unramified.SpectralSystem

open Langlands.Global Langlands.Global.AdelicFunctoriality
open scoped NumberField

section Reindex

variable {I : Type uI} {J : Type uJ}

/-- A place outside the reindexed exceptional set comes from a place outside the
original exceptional set. -/
theorem symm_not_mem_reindex_exceptional {n : ℕ} {s : SpectralSystem I n} {e : I ≃ J} {v : J}
    (hv : v ∉ (s.reindex e).exceptional) : e.symm v ∉ s.exceptional :=
  fun h => hv (Finset.mem_map.mpr ⟨e.symm v, h, e.apply_symm_apply v⟩)

/-- The reindexed system reads the original Euler polynomial at the corresponding place. -/
theorem reindex_eulerPolynomial {n : ℕ} (s : SpectralSystem I n) (e : I ≃ J) (v : J)
    (hv : v ∉ (s.reindex e).exceptional) :
    (s.reindex e).eulerPolynomial v hv =
      s.eulerPolynomial (e.symm v) (symm_not_mem_reindex_exceptional hv) :=
  rfl

/-- A rank cast keeps all Euler polynomials. -/
theorem sameEulerPolynomials_eqRec {n m : ℕ} (h : n = m) (s : SpectralSystem I n) :
    s.SameEulerPolynomials (h ▸ s : SpectralSystem I m) := by
  subst h
  exact sameEulerPolynomials_refl s

/-- Reindexing along an equivalence preserves agreement of Euler polynomials outside
a finite set. -/
theorem SameEulerPolynomials.reindex {n m : ℕ} {s : SpectralSystem I n}
    {t : SpectralSystem I m} (h : s.SameEulerPolynomials t) (e : I ≃ J) :
    (s.reindex e).SameEulerPolynomials (t.reindex e) := by
  filter_upwards [e.symm.injective.tendsto_cofinite.eventually h] with v hv
  intro hs ht
  exact hv (symm_not_mem_reindex_exceptional hs) (symm_not_mem_reindex_exceptional ht)

/-- The finite sum of reindexed systems has the Euler polynomials of the reindexed
finite sum. -/
theorem finiteSum_reindex_sameEulerPolynomials {ι : Type*} [Fintype ι] {rank : ι → ℕ}
    (s : ∀ j, SpectralSystem I (rank j)) (e : I ≃ J) :
    (finiteSum fun j => (s j).reindex e).SameEulerPolynomials ((finiteSum s).reindex e) :=
  Filter.Eventually.of_forall fun v hv hv' =>
    (finiteSum_eulerPolynomial _ v hv).trans
      (finiteSum_eulerPolynomial s (e.symm v) (symm_not_mem_reindex_exceptional hv')).symm

end Reindex

section WeakBaseChange

variable {K : Type uK} {L : Type uL} {K' : Type uK'} {L' : Type uL'}
  [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [Field K'] [NumberField K'] [Field L'] [NumberField L'] [Algebra K' L']

/-- Arithmetic weak base change is preserved by reindexing both systems along a
commuting square of number-field isomorphisms `e : K ≃+* K'` and `f : L ≃+* L'`.
The system over `L'` is read at `w` through the place `f(w)` of `L`, and `f` matches
the places above each base place together with their ramification indices and
residue degrees. -/
theorem IsArithmeticWeakBaseChangeOf.reindex_of_comm (e : K ≃+* K') (f : L ≃+* L')
    (he : ∀ x, f (algebraMap K L x) = algebraMap K' L' (e x)) {n : ℕ}
    {t : SpectralSystem (FinitePlace L) n} {s : SpectralSystem (FinitePlace K) n}
    (h : t.IsArithmeticWeakBaseChangeOf s) :
    (t.reindex (finitePlaceEquiv f).symm).IsArithmeticWeakBaseChangeOf
      (s.reindex (finitePlaceEquiv e).symm) := by
  filter_upwards [(finitePlaceEquiv e).injective.tendsto_cofinite.eventually h] with v hv
  obtain ⟨hs, ht, hram, heig⟩ := hv
  have above (w : FinitePlacesAbove L' v) :
      (finitePlaceEquiv f w.1).asIdeal.LiesOver (finitePlaceEquiv e v).asIdeal := by
    let := w.2
    exact liesOver_finitePlaceEquiv_of_comm e f he v w.1
  have hs' : v ∉ (s.reindex (finitePlaceEquiv e).symm).exceptional := by
    simpa only [reindex, Finset.mem_map_equiv, Equiv.symm_symm] using hs
  have ht' (w : FinitePlacesAbove L' v) :
      w.1 ∉ (t.reindex (finitePlaceEquiv f).symm).exceptional := by
    simpa only [reindex, Finset.mem_map_equiv, Equiv.symm_symm] using
      ht ⟨finitePlaceEquiv f w.1, above w⟩
  refine ⟨hs', ht', fun w => ?_, fun w => ?_⟩
  · let := w.2
    rw [← ramificationIdx_finitePlaceEquiv_of_comm e f he v w.1]
    exact hram ⟨finitePlaceEquiv f w.1, above w⟩
  · let := w.2
    rw [← inertiaDeg_finitePlaceEquiv_of_comm e f he v w.1]
    exact heig ⟨finitePlaceEquiv f w.1, above w⟩

end WeakBaseChange

section RankCast

variable {I : Type uI} {J : Type uJ} {K : Type uK} {L : Type uL}
  [Field K] [Field L] [NumberField L] [Algebra K L]

/-- Rank casts on both sides do not affect a reindexed weak base change. -/
theorem isArithmeticWeakBaseChangeOf_eqRec_reindex {a b a' b' : ℕ} (h : a = b) (ha : a = a')
    (hb : b = b') (h' : a' = b') (φL : I ≃ FinitePlace L) (φK : J ≃ FinitePlace K)
    {t : SpectralSystem I a} {s : SpectralSystem J b}
    (hst : ((h ▸ t : SpectralSystem I b).reindex φL).IsArithmeticWeakBaseChangeOf
      (s.reindex φK)) :
    (h' ▸ (ha ▸ t.reindex φL : SpectralSystem (FinitePlace L) a') :
        SpectralSystem (FinitePlace L) b').IsArithmeticWeakBaseChangeOf
      (hb ▸ s.reindex φK : SpectralSystem (FinitePlace K) b') := by
  subst h ha hb
  exact hst

end RankCast

end Langlands.Unramified.SpectralSystem

namespace Langlands.Automorphic.IsobaricData

open Langlands.Global Langlands.Global.AdelicFunctoriality Langlands.Unramified
open Langlands.Automorphic.Unramified

variable {K : Type uK} {L : Type uL} [Field K] [NumberField K] [Field L] [NumberField L]
  [CompactSpace (AdeleQuotient K)] [CompactSpace (AdeleQuotient L)]

/-- Arithmetic pullback of every constituent along `e : K ≃+* L` carries an attached
spectral system `s` to the system `s` reindexed along the places, cast to the rank of
the pulled-back data. Each constituent uses the exact cuspidal transport
`cuspidalSpectralArithmeticComap`. -/
theorem HasSpectralSystem.reindex_arithmeticComap (e : K ≃+* L) {D : IsobaricData L}
    {s : SpectralSystem (FinitePlace L) D.rank} (hs : HasSpectralSystem.{uL, uV} D s) :
    HasSpectralSystem.{uK, uV} (D.arithmeticComap e)
      ((rank_arithmeticComap e D).symm ▸ s.reindex (finitePlaceEquiv e) :
        SpectralSystem (FinitePlace K) (D.arithmeticComap e).rank) := by
  obtain ⟨k, σ, hσ, t, ht, hts⟩ := hs
  refine ⟨k, fun j => (σ j).arithmeticComap e, map_arithmeticComap_eq e hσ,
    fun j => (t j).reindex (finitePlaceEquiv e),
    fun j => cuspidalSpectralArithmeticComap.{uK, uL, uV} K L e (σ j).1 (σ j).2 (t j) (ht j),
    ?_⟩
  exact ((SpectralSystem.finiteSum_reindex_sameEulerPolynomials t (finitePlaceEquiv e)).trans
    (hts.reindex (finitePlaceEquiv e))).trans
      (SpectralSystem.sameEulerPolynomials_eqRec _ _)

end Langlands.Automorphic.IsobaricData

namespace Langlands.Automorphic.Unramified

open Langlands.Global Langlands.Global.AdelicFunctoriality Langlands.Unramified

/-- Weak base change of actual isobaric data is equivariant under compatible
automorphisms `τF` of `F` and `τE` of `E`, acting by arithmetic pullback along their
inverses on every constituent. -/
theorem isobaricWeakBaseChangeEquivariance :
    IsobaricWeakBaseChangeEquivarianceStatement.{uF, uE, uV, uW} := by
  intro F E _ _ _ _ _ _ _ τF τE hτ DF DE hbc
  obtain ⟨h, s, t, hs, ht, hst⟩ := hbc
  have hrank : (DE.arithmeticComap τE.symm).rank = (DF.arithmeticComap τF.symm).rank := by
    rw [IsobaricData.rank_arithmeticComap, IsobaricData.rank_arithmeticComap, h]
  have hw := SpectralSystem.IsArithmeticWeakBaseChangeOf.reindex_of_comm τF τE hτ hst
  rw [← finitePlaceEquiv_symm, ← finitePlaceEquiv_symm] at hw
  exact ⟨hrank, _, _, hs.reindex_arithmeticComap τF.symm, ht.reindex_arithmeticComap τE.symm,
    SpectralSystem.isArithmeticWeakBaseChangeOf_eqRec_reindex h _ _ hrank _ _ hw⟩

end Langlands.Automorphic.Unramified
