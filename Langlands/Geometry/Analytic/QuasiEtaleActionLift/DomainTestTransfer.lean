import Langlands.Geometry.Analytic.StrictTestDomain.SpectralDisplacement
import Langlands.Geometry.Analytic.GeneralizedAffinoid.DomainCovering
import Langlands.Geometry.Analytic.GeneralizedAffinoid.DomainCancellation
import Langlands.Geometry.Analytic.GeneralizedAffinoid.RationalChartBaseChange

/-! # Transferring spectral tests to represented affinoid domains -/

noncomputable section

universe u

namespace Langlands.Analytic

open BanachSpectrum PresentedAffinoidAlgebra

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {A C : PresentedAffinoidAlgebra K}

/-- Finite spectral tests downstairs imply that a perturbed map factors
through the domain algebra and that the factor satisfies the requested tests. -/
def BoundedAlgHom.HasSpectralTestTransfer (i : BoundedAlgHom K A C) : Prop :=
  ∀ (F : Finset C) (ε : ℝ), 0 < ε →
    ∃ (E : Finset A) (δ : ℝ), 0 < δ ∧
      ∀ (B : PresentedAffinoidAlgebra K) (a : BoundedAlgHom K C B) (b : BoundedAlgHom K A B),
        (∀ s ∈ E, SpectralBound (b s - a (i s)) δ) →
        ∃ b' : BoundedAlgHom K C B, b'.comp i = b ∧
          ∀ t ∈ F, SpectralBound (b' t - a t) ε

namespace PresentedAffinoidAlgebra.Domain

/-- Spectral test transfer for a rational chart implies test transfer for
any represented domain of the same affinoid algebra. -/
theorem hasSpectralTestTransfer_of_rational (U : Domain K A)
    (hRational : ∀ d : RationalChart K A, d.baseMap.HasSpectralTestTransfer) :
    U.baseMap.HasSpectralTestTransfer := by
  classical
  intro F ε hε
  let cover := U.finiteRationalCoverData
  let restriction (i : Fin cover.size) := (cover.map i).restriction
  have hrestriction (i : Fin cover.size) :
      (restriction i).comp U.baseMap = (cover.chart i).baseMap :=
    (cover.map i).comp_baseMap
  choose E δ hδ htest using fun i : Fin cover.size =>
    hRational (cover.chart i) (F.image (restriction i)) ε hε
  let values := insert 1 (Finset.univ.image δ)
  have hvalues : values.Nonempty := ⟨1, Finset.mem_insert_self ..⟩
  let η := values.inf' hvalues id
  have hη : 0 < η := by
    apply (Finset.lt_inf'_iff _).mpr
    intro x hx
    rcases Finset.mem_insert.mp hx with rfl | hx
    · exact zero_lt_one
    · obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hx
      exact hδ i
  have hηδ (i : Fin cover.size) : η ≤ δ i :=
    Finset.inf'_le id (Finset.mem_insert_of_mem (Finset.mem_image_of_mem δ (Finset.mem_univ i)))
  refine ⟨Finset.univ.biUnion E, η, hη, fun B a b hb => ?_⟩
  let pull (i : Fin cover.size) := RationalChart.pullback (a.comp U.baseMap) (cover.chart i)
  let res (i : Fin cover.size) := (pull i).baseMap
  let old (i : Fin cover.size) := RationalChart.pullbackMap (a.comp U.baseMap) (cover.chart i)
  have hold (i : Fin cover.size) :
      (old i).comp (cover.chart i).baseMap = (res i).comp (a.comp U.baseMap) :=
    RationalChart.pullbackMap_comp_baseMap _ _
  have hpull (p : BanachSpectrum B) :
      ∃ i, ∃ q : BanachSpectrum (pull i).algebra,
        BanachSpectrum.comap (res i).toBoundedRingHom q = p := by
    have hp : BanachSpectrum.comap (a.comp U.baseMap).toBoundedRingHom p ∈ U.locus :=
      U.represents.hasImageIn (BanachSpectrum.comap a.toBoundedRingHom p)
    obtain ⟨i, hi⟩ := cover.covers _ hp
    have hi' : p ∈ (pull i).locus := by
      change p ∈ (RationalChart.pullback (a.comp U.baseMap) (cover.chart i)).locus
      rw [RationalChart.pullback_locus]
      exact hi
    rw [← (pull i).range_comap_baseMap] at hi'
    obtain ⟨q, hq⟩ := hi'
    exact ⟨i, q, hq⟩
  have hsmall (i : Fin cover.size) (s : A) (hs : s ∈ E i) :
      SpectralBound ((res i).comp b s - old i ((cover.chart i).baseMap s)) (δ i) := by
    have heq : old i ((cover.chart i).baseMap s) = res i (a (U.baseMap s)) :=
      congrArg (fun m : BoundedAlgHom K A (pull i).algebra => m s) (hold i)
    rw [heq]
    change SpectralBound ((res i).toAlgHom (b s) - (res i).toAlgHom (a (U.baseMap s))) (δ i)
    rw [← map_sub]
    exact ((hb s (Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, hs⟩)).mono (hηδ i)).map
      (res i).toBoundedRingHom
  choose new hnew hnear using fun i : Fin cover.size =>
    htest i (pull i).algebra (old i) ((res i).comp b) (hsmall i)
  have hbImage : HasImageIn K b U.locus := by
    intro p
    obtain ⟨i, q, hp⟩ := hpull p
    have hq := (cover.chart i).represents.hasImageIn
      (BanachSpectrum.comap (new i).toBoundedRingHom q)
    change BanachSpectrum.comap ((new i).comp (cover.chart i).baseMap).toBoundedRingHom q ∈
      (cover.chart i).locus at hq
    rw [hnew i] at hq
    rw [← hp]
    exact (cover.map i).subset hq
  obtain ⟨b', hb', _⟩ := U.represents.2.2 B b hbImage
  have hOldEq (i : Fin cover.size) : (res i).comp a = (old i).comp (restriction i) := by
    apply U.represents.hom_ext
    change (res i).comp (a.comp U.baseMap) = (old i).comp ((restriction i).comp U.baseMap)
    rw [hrestriction, hold]
  have hNewEq (i : Fin cover.size) : (res i).comp b' = (new i).comp (restriction i) := by
    apply U.represents.hom_ext
    change (res i).comp (b'.comp U.baseMap) = (new i).comp ((restriction i).comp U.baseMap)
    rw [hrestriction, hnew, hb']
  refine ⟨b', hb', fun t ht p => ?_⟩
  obtain ⟨i, q, hp⟩ := hpull p
  have hOldAt : res i (a t) = old i (restriction i t) :=
    congrArg (fun m : BoundedAlgHom K U.algebra (pull i).algebra => m t) (hOldEq i)
  have hNewAt : res i (b' t) = new i (restriction i t) :=
    congrArg (fun m : BoundedAlgHom K U.algebra (pull i).algebra => m t) (hNewEq i)
  rw [← hp]
  change q ((res i).toAlgHom (b' t - a t)) ≤ ε
  rw [map_sub]
  change q (res i (b' t) - res i (a t)) ≤ ε
  rw [hOldAt, hNewAt]
  exact hnear i _ (Finset.mem_image_of_mem (restriction i) ht) q

end PresentedAffinoidAlgebra.Domain

end Langlands.Analytic
