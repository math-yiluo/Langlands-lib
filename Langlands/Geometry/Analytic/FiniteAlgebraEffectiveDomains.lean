import Langlands.Geometry.Analytic.GeneralizedAffinoid.FiniteAffinoidAlgebraDescent.EffectiveData
import Langlands.Geometry.Analytic.GeneralizedAffinoid.DomainBaseTransport
import Langlands.Geometry.Analytic.GeneralizedAffinoid.DomainRationalIntersection
import Langlands.Geometry.Analytic.AtlasIntersectionFiniteRecognition

/-! # Full parent domains recovered from effective finite algebra descent -/

noncomputable section

universe u

namespace Langlands.Analytic.PresentedAffinoidAlgebra

open CategoryTheory Set

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]

namespace FiniteAffinoidAlgebraDescent.EffectiveRealization

variable {R : PresentedAffinoidAlgebra K}
  {c : Domain.FiniteCover (Domain.whole K R)} {F : LocalAlgebras c}
  {d : DescentData F} (P : EffectiveRealization d)

/-- The actual parent component map represents precisely the inverse
image of the original base-domain locus, by its full base-change equivalence. -/
theorem localMap_represents (i : Fin c.size) :
    Represents K (P.toMatchingPresentation.localMap i)
      (P.toMatchingPresentation.preimageLocus i) := by
  let Q := P.toMatchingPresentation
  have hr : (c.map i).restriction = (c.obj i).baseMap := (c.map i).comp_baseMap
  have hrep := Domain.represents_pullback Q.baseMap (c.obj i)
  change Represents K (AffinoidPushout.leftMap Q.baseMap (c.obj i).baseMap) (Q.preimageLocus i) at hrep
  rw [← hr] at hrep
  have hpost := hrep.postcomp_equiv (P.comparisonEquiv i)
  rw [P.comparison_eq i, Q.comparison_left i] at hpost
  exact hpost

/-- The entire original component algebra is retained as a full domain
of the constructed parent algebra. -/
def componentDomain (i : Fin c.size) : Domain K P.algebra where
  algebra := F.algebra i
  baseMap := P.toMatchingPresentation.localMap i
  locus := P.toMatchingPresentation.preimageLocus i
  represents := P.localMap_represents i

/-- The actual full parent component domains cover the whole parent,
without requiring a separate spectral coverage hypothesis. -/
def componentCover : Domain.FiniteCover (Domain.whole K P.algebra) where
  size := c.size
  obj := P.componentDomain
  map i := ⟨P.toMatchingPresentation.localMap i, BoundedAlgHom.comp_id _⟩
  covers x _ := c.covers
    (BanachSpectrum.comap P.toMatchingPresentation.baseMap.toBoundedRingHom x) (mem_univ _)

/-- Complete structural-map compatibility gives the exact original
base spectrum image of each parent component. -/
theorem localMap_spectrum_over_base (i : Fin c.size) (x : BanachSpectrum (F.algebra i)) :
    BanachSpectrum.comap P.toMatchingPresentation.baseMap.toBoundedRingHom
      (BanachSpectrum.comap (P.toMatchingPresentation.localMap i).toBoundedRingHom x) =
        (c.obj i).spectrumMap (BanachSpectrum.comap (F.map i).toBoundedRingHom x) := by
  apply BanachSpectrum.ext
  intro r
  exact congrArg (fun z : BoundedAlgHom K R (F.algebra i) => x (z r))
    ((P.toMatchingPresentation.localMap_baseMap i).trans (F.structuralMap_eq i))

/-- On any further original full domain, the unchanged local pushout
restriction remains a full parent domain at exactly the original inverse image. -/
theorem restrictedLocalMap_represents (i : Fin c.size) (E : Domain K R)
    (hi : E.locus ⊆ (c.obj i).locus) :
    Represents K ((F.localMap i E hi).comp (P.toMatchingPresentation.localMap i))
      ((BanachSpectrum.comap P.toMatchingPresentation.baseMap.toBoundedRingHom) ⁻¹' E.locus) := by
  let Q := P.toMatchingPresentation
  let r := Domain.inclusionOfSubset E (c.obj i) hi
  let D := (c.obj i).relative E r
  let W := (BanachSpectrum.comap Q.baseMap.toBoundedRingHom) ⁻¹' E.locus
  have hrep := Domain.represents_pullback (F.map i) D
  change Represents K (F.localMap i E hi)
    ((BanachSpectrum.comap (F.map i).toBoundedRingHom) ⁻¹' D.locus) at hrep
  have hpre : (BanachSpectrum.comap (F.map i).toBoundedRingHom) ⁻¹' D.locus =
      (BanachSpectrum.comap (Q.localMap i).toBoundedRingHom) ⁻¹' W := by
    change (BanachSpectrum.comap (F.map i).toBoundedRingHom) ⁻¹'
      ((c.obj i).relative E r).locus = _
    rw [(c.obj i).relative_locus_eq_preimage_of_injective (c.obj i).spectrumMap_injective E r]
    ext x
    change (c.obj i).spectrumMap (BanachSpectrum.comap (F.map i).toBoundedRingHom x) ∈ E.locus ↔
      BanachSpectrum.comap Q.baseMap.toBoundedRingHom
        (BanachSpectrum.comap (Q.localMap i).toBoundedRingHom x) ∈ E.locus
    rw [P.localMap_spectrum_over_base]
  rw [hpre] at hrep
  have hW : IsClosed W :=
    E.represents.1.preimage (BanachSpectrum.comapContinuous Q.baseMap.toBoundedRingHom).continuous
  have hsub : W ⊆ Q.preimageLocus i := preimage_mono hi
  have htotal := (P.localMap_represents i).comp_preimage hrep hW
  change Represents K ((F.localMap i E hi).comp (Q.localMap i)) (Q.preimageLocus i ∩ W) at htotal
  rw [inter_eq_right.mpr hsub] at htotal
  exact htotal

/-- The two original overlap restrictions agree on the entire parent
algebra by the matching-algebra equations, not by their spectrum action. -/
theorem localMap_overlap (i j : Fin c.size) :
    (d.toPairTransitions.leftRestriction i j).comp (P.toMatchingPresentation.localMap i) =
      (d.toPairTransitions.rightRestriction i j).comp (P.toMatchingPresentation.localMap j) :=
  congrArg (fun z => z.comp P.equiv.toBoundedAlgHom)
    (d.toPairTransitions.projection_overlap i j)

/-- The exact original overlap spectrum image is the literal intersection
of the two full component images in the parent spectrum. -/
theorem overlap_range (i j : Fin c.size) :
    range (BanachSpectrum.comap
      ((d.toPairTransitions.leftRestriction i j).comp
        (P.toMatchingPresentation.localMap i)).toBoundedRingHom) =
      range (BanachSpectrum.comap (P.toMatchingPresentation.localMap i).toBoundedRingHom) ∩
        range (BanachSpectrum.comap (P.toMatchingPresentation.localMap j).toBoundedRingHom) := by
  rw [P.localMap_overlap]
  have hr := (P.restrictedLocalMap_represents j (F.overlap i j) (F.overlapRight i j)).2.1
  change range (BanachSpectrum.comap
    ((F.localMap j (F.overlap i j) (F.overlapRight i j)).comp
      (P.toMatchingPresentation.localMap j)).toBoundedRingHom) = _
  rw [hr, (P.localMap_represents i).2.1, (P.localMap_represents j).2.1]
  rfl

end FiniteAffinoidAlgebraDescent.EffectiveRealization

end Langlands.Analytic.PresentedAffinoidAlgebra
