import Langlands.Geometry.Analytic.QuasiEtaleActionLift.StandardEtaleLift
import Langlands.Geometry.Analytic.AffinoidEtaleLocus
import Langlands.Geometry.Analytic.GeneralizedAffinoid.RationalLaurentNeighborhoods
import Langlands.Geometry.Analytic.GeneralizedAffinoid.RationalRepresentationProof
import Mathlib.RingTheory.Unramified.LocalStructure

/-! # Nearby finite étale lifts over a Laurent neighborhood -/

noncomputable section

universe u

namespace Langlands.Analytic.BoundedAlgHom

open BanachSpectrum PresentedAffinoidAlgebra Topology

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {R S : PresentedAffinoidAlgebra K}

/-- A finite test lifting property for bounded affinoid maps. The reference maps
out of `S` have spectrum image in `L`. Every requested finite test on the lift
can be enforced by a finite test on the perturbed map out of `R`, independently
of the test algebra and the reference map. -/
def HasSpectralLiftsOver (f : BoundedAlgHom K R S) (L : Set (BanachSpectrum S)) : Prop :=
  ∀ (E : Finset S) (ε : ℝ), 0 < ε →
    ∃ (D : Finset R) (δ : ℝ), 0 < δ ∧
      ∀ (B : PresentedAffinoidAlgebra K) (a : BoundedAlgHom K S B) (b : BoundedAlgHom K R B),
        HasImageIn K a L →
        (∀ r ∈ D, SpectralBound (b r - a (f r)) δ) →
        ∃ a' : BoundedAlgHom K S B, a'.comp f = b ∧
          ∀ s ∈ E, SpectralBound (a' s - a s) ε

/-- A standard étale principal localization gives the spectral lifting property
on each Laurent locus where its denominator has a positive lower bound. -/
theorem hasSpectralLiftsOver_of_isStandardEtaleAway (f : BoundedAlgHom K R S)
    (hf : f.IsFiniteBanach) (e : S) (q : ℝ) (hq : 0 < q)
    (hP : letI : Algebra R S := f.toAlgHom.toRingHom.toAlgebra
      Algebra.IsStandardEtale R (Localization.Away e)) :
    f.HasSpectralLiftsOver (RationalChart.lowerBound e q hq).locus := by
  let : Algebra R S := f.toAlgHom.toRingHom.toAlgebra
  let T := Localization.Away e
  have : Algebra.IsStandardEtale R T := hP
  let P : StandardEtalePresentation R T :=
    Algebra.IsStandardEtale.nonempty_standardEtalePresentation.some
  let d := RationalChart.lowerBound e q hq
  have hu : IsUnit (d.baseMap e) := by
    apply (d.algebra.isUnit_iff_forall_spectrum_ne_zero _).mpr
    intro p
    have hp : BanachSpectrum.comap d.baseMap.toBoundedRingHom p ∈ d.locus := by
      rw [← d.range_comap_baseMap]
      exact Set.mem_range_self p
    exact (hq.trans_le ((RationalChart.mem_locus_lowerBound e q hq _).mp hp)).ne'
  let i : S →+* T := algebraMap S T
  have hi (r : R) : i (f r) = algebraMap R T r :=
    (IsScalarTower.algebraMap_apply R S T r).symm
  let k : T →+* d.algebra := IsLocalization.Away.lift e hu
  have hk (s : S) : k (i s) = d.baseMap s := IsLocalization.Away.lift_eq e hu s
  intro E ε hε
  obtain ⟨D, δ, hδ, hlift⟩ :=
    f.exists_spectralLift_of_standardEtalePresentation hf P i hi d.baseMap k hk E hε
  refine ⟨D, δ, hδ, fun B a b ha hb => ?_⟩
  obtain ⟨l, hl, _⟩ := d.existsUnique_factorization B a ha
  have hla (s : S) : l (d.baseMap s) = a s := congrArg (fun m : BoundedAlgHom K S B => m s) hl
  obtain ⟨a', ha', hclose⟩ := hlift B l b (fun r hr => by simpa only [hla] using hb r hr)
  exact ⟨a', ha', fun s hs => by simpa only [hla] using hclose s hs⟩

/-- At a point where a finite Banach affinoid map is étale, there is a Laurent
neighborhood of the point on which the map has uniform spectral lifts. -/
theorem exists_hasSpectralLiftsOver_of_isEtaleAtPoint (f : BoundedAlgHom K R S)
    (hf : f.IsFiniteBanach) (p : BanachSpectrum S) (hp : f.IsEtaleAtPoint p) :
    ∃ d : RationalChart K S, d.locus ∈ 𝓝 p ∧ f.HasSpectralLiftsOver d.locus := by
  let : Algebra R S := f.toAlgHom.toRingHom.toAlgebra
  let : p.kernel.IsPrime := p.kernel_isPrime
  have hfType := hf.finite.finiteType
  have : Algebra.FiniteType R S := hfType
  have : Algebra.FinitePresentation R S := Algebra.FinitePresentation.of_finiteType.mp hfType
  have hpMem : p ∈ f.pointwiseEtaleLocus := hp
  rw [f.pointwiseEtaleLocus_eq_prime_preimage hfType] at hpMem
  have : Algebra.IsEtaleAt R p.kernel := hpMem
  obtain ⟨e, he, hstd⟩ := Algebra.IsEtaleAt.exists_isStandardEtale (R := R) p.kernel
  have hePos : 0 < p e := lt_of_le_of_ne (apply_nonneg p.toMulRingSeminorm _) (Ne.symm he)
  let q := p e / 2
  have hq : 0 < q := div_pos hePos (by norm_num)
  refine ⟨RationalChart.lowerBound e q hq, ?_,
    f.hasSpectralLiftsOver_of_isStandardEtaleAway hf e q hq hstd⟩
  have hopen : IsOpen {x : BanachSpectrum S | q < x e} :=
    isOpen_lt continuous_const (BanachSpectrum.evaluation e).continuous
  have hmem : p ∈ {x : BanachSpectrum S | q < x e} := by
    change p e / 2 < p e
    linarith
  exact Filter.mem_of_superset (hopen.mem_nhds hmem)
    fun x hx => (RationalChart.mem_locus_lowerBound e q hq x).mpr (le_of_lt hx)

end Langlands.Analytic.BoundedAlgHom
