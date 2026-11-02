import Mathlib.RingTheory.Spectrum.Prime.Topology
import Mathlib.RingTheory.Unramified.Field
import Mathlib.RingTheory.RingHom.Etale

/-! # Ideals of finite closed subsets under étale maps -/

universe u v

open Set Function

namespace Langlands.AlgebraicGeometry.FiniteClosedIdeal

variable {B : Type u} {C : Type v} [CommRing B] [CommRing C]

/-- A finite set of closed points is cut out by the product of its maximal ideals. -/
lemma vanishingIdeal_eq_prod {T : Set (PrimeSpectrum B)} (hT : T.Finite)
    (hclosed : ∀ p ∈ T, IsClosed ({p} : Set (PrimeSpectrum B))) :
    PrimeSpectrum.vanishingIdeal T = ∏ p ∈ hT.toFinset, p.asIdeal := by
  classical
  have hp : (hT.toFinset : Set (PrimeSpectrum B)).Pairwise
      (IsCoprime on PrimeSpectrum.asIdeal) := by
    intro p hp q hq hpq
    let : p.asIdeal.IsMaximal :=
      (PrimeSpectrum.isClosed_singleton_iff_isMaximal p).mp
        (hclosed p (hT.mem_toFinset.mp hp))
    let : q.asIdeal.IsMaximal :=
      (PrimeSpectrum.isClosed_singleton_iff_isMaximal q).mp
        (hclosed q (hT.mem_toFinset.mp hq))
    exact Ideal.isCoprime_of_isMaximal (fun h => hpq (PrimeSpectrum.ext h))
  rw [Ideal.prod_eq_iInf_of_pairwise_isCoprime hp]
  simp only [hT.mem_toFinset]
  rfl

/-- Extension commutes with the intersection defining a finite closed point set,
because these maximal ideals and their extensions are pairwise comaximal. -/
lemma map_vanishingIdeal_eq_iInf (f : B →+* C) {T : Set (PrimeSpectrum B)}
    (hT : T.Finite)
    (hclosed : ∀ p ∈ T, IsClosed ({p} : Set (PrimeSpectrum B))) :
    (PrimeSpectrum.vanishingIdeal T).map f = ⨅ p ∈ T, p.asIdeal.map f := by
  classical
  have hp : (hT.toFinset : Set (PrimeSpectrum B)).Pairwise
      (IsCoprime on fun p => p.asIdeal.map f) := by
    intro p hp q hq hpq
    let : p.asIdeal.IsMaximal :=
      (PrimeSpectrum.isClosed_singleton_iff_isMaximal p).mp
        (hclosed p (hT.mem_toFinset.mp hp))
    let : q.asIdeal.IsMaximal :=
      (PrimeSpectrum.isClosed_singleton_iff_isMaximal q).mp
        (hclosed q (hT.mem_toFinset.mp hq))
    exact (Ideal.isCoprime_of_isMaximal
      (fun h => hpq (PrimeSpectrum.ext h))).map (Ideal.mapHom f)
  rw [vanishingIdeal_eq_prod hT hclosed]
  change (Ideal.mapHom f) (∏ p ∈ hT.toFinset, p.asIdeal) = _
  rw [map_prod]
  change (∏ p ∈ hT.toFinset, p.asIdeal.map f) = _
  rw [Ideal.prod_eq_iInf_of_pairwise_isCoprime hp]
  simp only [hT.mem_toFinset]

/-- Étale extension of the vanishing ideal of finitely many closed points is radical. -/
lemma isRadical_map_vanishingIdeal (f : B →+* C) (hf : f.Etale)
    {T : Set (PrimeSpectrum B)} (hT : T.Finite)
    (hclosed : ∀ p ∈ T, IsClosed ({p} : Set (PrimeSpectrum B))) :
    ((PrimeSpectrum.vanishingIdeal T).map f).IsRadical := by
  let : Algebra B C := f.toAlgebra
  let : Algebra.Etale B C := hf.toAlgebra
  rw [map_vanishingIdeal_eq_iInf f hT hclosed]
  apply Ideal.isRadical_iInf
  intro p
  apply Ideal.isRadical_iInf
  intro hp
  let : p.asIdeal.IsMaximal :=
    (PrimeSpectrum.isClosed_singleton_iff_isMaximal p).mp (hclosed p hp)
  exact Algebra.FormallyUnramified.isRadical_map_isMaximal B C p.asIdeal

/-- The radical ideal obtained by extending the ideal of a finite set of closed points. -/
def extendedRadicalIdeal (f : B →+* C) (hf : f.Etale)
    (T : Set (PrimeSpectrum B)) (hT : T.Finite)
    (hclosed : ∀ p ∈ T, IsClosed ({p} : Set (PrimeSpectrum B))) :
    {I : Ideal C // I.IsRadical} :=
  ⟨(PrimeSpectrum.vanishingIdeal T).map f, isRadical_map_vanishingIdeal f hf hT hclosed⟩

/-- Equal inverse images of a finite closed point set under two étale maps give
equal extended vanishing ideals. -/
lemma map_vanishingIdeal_eq_of_preimage_eq (s t : B →+* C)
    (hs : s.Etale) (ht : t.Etale) {T : Set (PrimeSpectrum B)}
    (hT : T.Finite)
    (hclosed : ∀ p ∈ T, IsClosed ({p} : Set (PrimeSpectrum B)))
    (hinv : PrimeSpectrum.comap s ⁻¹' T = PrimeSpectrum.comap t ⁻¹' T) :
    (PrimeSpectrum.vanishingIdeal T).map s = (PrimeSpectrum.vanishingIdeal T).map t := by
  have hTc : IsClosed T := by
    simpa only [Set.biUnion_of_singleton] using hT.isClosed_biUnion hclosed
  have hzero : PrimeSpectrum.zeroLocus ((PrimeSpectrum.vanishingIdeal T).map s : Set C) =
      PrimeSpectrum.zeroLocus ((PrimeSpectrum.vanishingIdeal T).map t : Set C) := by
    simpa only [Ideal.map, PrimeSpectrum.zeroLocus_span,
      ← PrimeSpectrum.preimage_comap_zeroLocus,
      PrimeSpectrum.zeroLocus_vanishingIdeal_eq_closure, hTc.closure_eq] using hinv
  have hrad := PrimeSpectrum.zeroLocus_eq_iff.mp hzero
  rw [(isRadical_map_vanishingIdeal s hs hT hclosed).radical,
    (isRadical_map_vanishingIdeal t ht hT hclosed).radical] at hrad
  exact hrad

end Langlands.AlgebraicGeometry.FiniteClosedIdeal
