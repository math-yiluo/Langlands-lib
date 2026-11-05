import Langlands.AlgebraicGeometry.LocalTopologicalDimension
import Langlands.AlgebraicGeometry.AffineOpenDimension
import Mathlib.RingTheory.Spectrum.Prime.Chevalley
import Mathlib.RingTheory.Flat.Stability

/-! # Local dimension under flat open spectrum maps -/

noncomputable section

universe u v

open Set Topology TopologicalSpace

namespace Langlands.AlgebraicGeometry.SchemeFiberGeometry

/-- An actual principal localization realizes local dimension at a prime. -/
theorem exists_away_dimension_eq_at
    (A : Type u) [CommRing A] (q : PrimeSpectrum A) :
    ∃ r : A, r ∉ q.asIdeal ∧
      ringKrullDim (Localization.Away r) = topologicalKrullDimAt q := by
  obtain ⟨U, hqU, hU⟩ := exists_open_topologicalKrullDim_eq_at q
  obtain ⟨_, ⟨r, rfl⟩, hqr, hrU⟩ :=
    PrimeSpectrum.isTopologicalBasis_basic_opens.isOpen_iff.mp U.isOpen q hqU
  refine ⟨r, hqr, ?_⟩
  have hd : topologicalKrullDim (PrimeSpectrum.basicOpen r) =
      topologicalKrullDimAt q := by
    apply le_antisymm
    · exact ((Topology.IsEmbedding.inclusion hrU).isInducing.topologicalKrullDim_le).trans_eq hU
    · exact topologicalKrullDimAt_le_open q (PrimeSpectrum.basicOpen r) hqr
  exact (PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim _).symm.trans
    (((localizationAwayBasicOpenHomeomorph r).isHomeomorph.topologicalKrullDim_eq _).trans hd)

/-- Going down lifts all prime chains in a principal open covered by the
actual contraction map. -/
theorem ringKrullDim_away_le_of_basicOpen_subset_range
    (R : Type u) (S : Type v) [CommRing R] [CommRing S] [Algebra R S]
    [Algebra.HasGoingDown R S] (r : R)
    (hr : (PrimeSpectrum.basicOpen r : Set (PrimeSpectrum R)) ⊆
      Set.range (PrimeSpectrum.comap (algebraMap R S))) :
    ringKrullDim (Localization.Away r) ≤ ringKrullDim S := by
  let f := PrimeSpectrum.comap (algebraMap R (Localization.Away r))
  have hf : StrictMono f :=
    (show Monotone f from fun _ _ h => Ideal.comap_mono h).strictMono_of_injective
      (PrimeSpectrum.localization_away_isOpenEmbedding _ r).injective
  change Order.krullDim (PrimeSpectrum (Localization.Away r)) ≤
    Order.krullDim (PrimeSpectrum S)
  rw [Order.krullDim]
  refine iSup_le fun l => ?_
  let c := l.map f hf
  have hlast : c.last ∈ PrimeSpectrum.basicOpen r :=
    (localizationAwayBasicOpenHomeomorph r l.last).property
  obtain ⟨q, hq⟩ := hr hlast
  have : q.asIdeal.LiesOver c.last.asIdeal :=
    ⟨congrArg PrimeSpectrum.asIdeal hq.symm⟩
  obtain ⟨L, hlen, _, _⟩ := Ideal.exists_ltSeries_of_hasGoingDown c q.asIdeal
  have heq : L.length = l.length := hlen
  exact heq ▸ Order.LTSeries.length_le_krullDim L

/-- A flat spectrum map which is open cannot lower local dimension at a point. -/
theorem topologicalKrullDimAt_comap_le_of_flat_of_isOpenMap
    (R : Type u) (S : Type v) [CommRing R] [CommRing S] [Algebra R S]
    [Module.Flat R S]
    (ho : IsOpenMap (PrimeSpectrum.comap (algebraMap R S)))
    (q : PrimeSpectrum S) :
    topologicalKrullDimAt (q.comap (algebraMap R S)) ≤ topologicalKrullDimAt q := by
  obtain ⟨s, hs, hdim⟩ := exists_away_dimension_eq_at S q
  let T := Localization.Away s
  let j := PrimeSpectrum.comap (algebraMap S T)
  let f := PrimeSpectrum.comap (algebraMap R S)
  let e := localizationAwayBasicOpenHomeomorph s
  let z := e.symm ⟨q, hs⟩
  have hz : j z = q := congrArg Subtype.val (e.apply_symm_apply ⟨q, hs⟩)
  have he : PrimeSpectrum.comap (algebraMap R T) = f ∘ j := by
    rw [IsScalarTower.algebraMap_eq R S T, PrimeSpectrum.comap_comp]
  have hopen : IsOpen (Set.range (PrimeSpectrum.comap (algebraMap R T))) := by
    rw [he, Set.range_comp]
    exact ho _ (PrimeSpectrum.localization_away_isOpenEmbedding T s).isOpen_range
  have hmem : f q ∈ Set.range (PrimeSpectrum.comap (algebraMap R T)) :=
    ⟨z, by rw [he]; exact congrArg f hz⟩
  obtain ⟨_, ⟨r, rfl⟩, hqr, hr⟩ :=
    PrimeSpectrum.isTopologicalBasis_basic_opens.isOpen_iff.mp hopen (f q) hmem
  have : Module.Flat R T := Module.Flat.trans R S T
  have hb := ringKrullDim_away_le_of_basicOpen_subset_range R T r hr
  calc
    topologicalKrullDimAt (f q) ≤ topologicalKrullDim (PrimeSpectrum.basicOpen r) :=
      topologicalKrullDimAt_le_open (f q) (PrimeSpectrum.basicOpen r) hqr
    _ = ringKrullDim (Localization.Away r) :=
      ((localizationAwayBasicOpenHomeomorph r).isHomeomorph.topologicalKrullDim_eq _).symm.trans
        (PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim _)
    _ ≤ ringKrullDim T := hb
    _ = topologicalKrullDimAt q := hdim

end Langlands.AlgebraicGeometry.SchemeFiberGeometry
