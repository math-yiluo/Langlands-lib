import Langlands.Geometry.Analytic.GeneralizedAffinoid.DomainFlatnessStatement
import Langlands.Geometry.Analytic.GeneralizedAffinoid.DomainRationalCoverProof
import Langlands.Geometry.Analytic.GeneralizedAffinoid.DomainRelativeRepresentation
import Langlands.Geometry.Analytic.GeneralizedAffinoid.RationalChartBaseChange
import Langlands.Geometry.Analytic.GeneralizedAffinoid.DomainSpectrumProof
import Langlands.Geometry.Analytic.GeneralizedAffinoid.SpectrumIdealCriterionProof
import Langlands.Geometry.Analytic.FlatTargetDescent
import Mathlib.RingTheory.RingHom.Flat

/-! # Reduction of domain flatness to rational-chart flatness -/

noncomputable section

universe u v w z

namespace Langlands.Analytic

/-- Flatness descends along a finite family of flat maps which jointly detect
maximal ideals: if every `g i` and every composite `g i ∘ φ` is flat, and every
maximal ideal of the middle ring stays proper in some `C i`, then `φ` is flat. -/
theorem RingHom.flat_of_finite_jointly_faithful
    {R : Type u} {S : Type v} [CommRing R] [CommRing S]
    {ι : Type w} [Fintype ι] {C : ι → Type z} [∀ i, CommRing (C i)]
    (φ : R →+* S) (g : ∀ i, S →+* C i)
    (hcomp : ∀ i, ((g i).comp φ).Flat) (hg : ∀ i, (g i).Flat)
    (hmax : ∀ m : Ideal S, m.IsMaximal → ∃ i, Ideal.map (g i) m ≠ ⊤) :
    φ.Flat := by
  let _ : Algebra R S := φ.toAlgebra
  let _ : ∀ i, Algebra S (C i) := fun i => (g i).toAlgebra
  let _ : ∀ i, Algebra R (C i) := fun i => ((g i).comp φ).toAlgebra
  have : ∀ i, IsScalarTower R S (C i) := fun i =>
    IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  have hRC : ∀ i, Module.Flat R (C i) := fun i => hcomp i
  have hSC : ∀ i, Module.Flat S (C i) := fun i => hg i
  have : Module.Flat R (∀ i, C i) :=
    Module.Flat.of_linearEquiv (DFinsupp.linearEquivFunOnFintype (R := R)).symm
  have : Module.Flat S (∀ i, C i) :=
    Module.Flat.of_linearEquiv (DFinsupp.linearEquivFunOnFintype (R := S)).symm
  have : Module.FaithfullyFlat S (∀ i, C i) := by
    refine ⟨fun m hm htop => ?_⟩
    obtain ⟨i, hi⟩ := hmax m hm
    apply hi
    rw [Ideal.smul_top_eq_map] at htop
    have htop' : Ideal.map (algebraMap S (∀ i, C i)) m = ⊤ := by
      have h1 : (1 : ∀ i, C i) ∈
          (Ideal.map (algebraMap S (∀ i, C i)) m).restrictScalars S := by
        rw [htop]
        trivial
      exact (Ideal.eq_top_iff_one _).mpr h1
    have hmap := congrArg (Ideal.map (Pi.evalRingHom C i)) htop'
    rw [Ideal.map_map, Ideal.map_top] at hmap
    exact hmap
  have := flat_of_faithfullyFlat_target R S (∀ i, C i)
  exact this

namespace PresentedAffinoidAlgebra.Domain

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {A : PresentedAffinoidAlgebra K}

/-- Algebraic flatness of the structural map depends only on the represented
locus: equal loci give a bounded equivalence over the base. -/
theorem flat_baseMap_of_locus_eq (U V : Domain K A) (h : U.locus = V.locus)
    (hU : U.baseMap.toAlgHom.toRingHom.Flat) :
    V.baseMap.toAlgHom.toRingHom.Flat := by
  let e := boundedEquivOfLocusEq U V h
  have heq : V.baseMap.toAlgHom.toRingHom =
      e.toAlgEquiv.toAlgHom.toRingHom.comp U.baseMap.toAlgHom.toRingHom := by
    rw [← boundedEquivOfLocusEq_comp_baseMap U V h]
    rfl
  rw [heq]
  exact hU.comp (RingHom.Flat.of_bijective e.toAlgEquiv.bijective)

/-- If the structural map of every positive-radius rational chart over every
presented affinoid algebra is flat, then so is the structural map of every
full represented affinoid domain. -/
theorem flat_baseMap_of_chartFlat
    (hchart : ∀ (B : PresentedAffinoidAlgebra K) (d : RationalChart K B),
      d.baseMap.toAlgHom.toRingHom.Flat)
    (U : Domain K A) : U.baseMap.toAlgHom.toRingHom.Flat := by
  obtain ⟨n, D, f, hcov⟩ := finiteRationalCover K A U
  have hinj : Function.Injective U.spectrumMap :=
    (spectrumEmbedding K A U).injective
  have hrel : ∀ i, (U.relative (D i).toDomain (f i)).locus =
      U.spectrumMap ⁻¹' (D i).locus := fun i =>
    U.relative_locus_eq_preimage_of_injective hinj (D i).toDomain (f i)
  apply RingHom.flat_of_finite_jointly_faithful (C := fun i => ((D i).algebra : Type u))
    U.baseMap.toAlgHom.toRingHom (fun i => (f i).restriction.toAlgHom.toRingHom)
  · intro i
    have h : ((f i).restriction.comp U.baseMap).toAlgHom.toRingHom.Flat := by
      rw [(f i).comp_baseMap]
      exact hchart A (D i)
    exact h
  · intro i
    let P := RationalChart.pullback U.baseMap (D i)
    have hP : P.toDomain.locus = (U.relative (D i).toDomain (f i)).locus := by
      rw [hrel i]
      exact RationalChart.pullback_locus U.baseMap (D i)
    exact flat_baseMap_of_locus_eq P.toDomain _ hP (hchart U.algebra P)
  · intro m hm
    obtain ⟨x, hx⟩ := exists_spectrum_kernel_of_proper_ideal U.algebra m hm.ne_top
    obtain ⟨i, hi⟩ := hcov (U.spectrumMap x) (U.represents.hasImageIn x)
    have hxrel : x ∈ (U.relative (D i).toDomain (f i)).locus := by
      rw [hrel i]
      exact hi
    obtain ⟨y, rfl⟩ := hxrel
    refine ⟨i, fun htop => y.kernel_isPrime.ne_top (top_unique ?_)⟩
    refine le_trans (le_of_eq htop.symm) ?_
    exact Ideal.map_le_of_le_comap (fun b hb => hx hb)

end PresentedAffinoidAlgebra.Domain

open PresentedAffinoidAlgebra in
/-- Flatness of all rational-chart structural maps (in a fixed universe)
implies the full domain flatness statement. -/
theorem PresentedAffinoidAlgebra.Domain.flatnessStatement_of_chartFlat
    (hchart : ∀ (K : Type u) [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
      (B : PresentedAffinoidAlgebra K) (d : RationalChart K B),
      d.baseMap.toAlgHom.toRingHom.Flat) :
    Domain.FlatnessStatement.{u} := by
  intro K _ _ _ A U
  exact Domain.flat_baseMap_of_chartFlat (hchart K) U

end Langlands.Analytic
