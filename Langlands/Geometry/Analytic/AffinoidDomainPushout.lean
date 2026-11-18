import Langlands.Geometry.Analytic.AtlasIntersectionFiniteRecognition
import Langlands.Geometry.Analytic.GeneralizedAffinoid.AffinoidPushoutPasting
import Langlands.Geometry.Analytic.GeneralizedAffinoid.DomainBaseChange
import Langlands.Geometry.Analytic.GeneralizedAffinoid.FiniteBanachPushout.Proof

/-! # Restricting an affinoid pushout to a domain of one factor -/

noncomputable section

universe u v

namespace Langlands.Analytic.PresentedAffinoidAlgebra.AffinoidPushout

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {A B C : PresentedAffinoidAlgebra K}
  (f : BoundedAlgHom K A B) (g : BoundedAlgHom K A C)

/-- The comparison to the same bounded pushout with the factors exchanged. -/
def swapMap : BoundedAlgHom K (algebra f g) (algebra g f) :=
  lift f g _ (rightMap g f) (leftMap g f) (condition g f).symm

theorem swapMap_comp_left :
    (swapMap f g).comp (leftMap f g) = rightMap g f :=
  lift_comp_leftMap _ _ _ _ _ _

theorem swapMap_comp_right :
    (swapMap f g).comp (rightMap f g) = leftMap g f :=
  lift_comp_rightMap _ _ _ _ _ _

private theorem swapMap_comp_swapMap :
    (swapMap g f).comp (swapMap f g) = BoundedAlgHom.id K (algebra f g) := by
  apply hom_ext f g
  · rw [BoundedAlgHom.comp_assoc, swapMap_comp_left, swapMap_comp_right, BoundedAlgHom.id_comp]
  · rw [BoundedAlgHom.comp_assoc, swapMap_comp_right, swapMap_comp_left, BoundedAlgHom.id_comp]

/-- Exchanging the factors of a bounded affinoid pushout gives a bounded
algebra equivalence. -/
def swapEquiv : BoundedAlgEquiv K (algebra f g) (algebra g f) :=
  BoundedAlgEquiv.ofHomInv (swapMap f g) (swapMap g f)
    (fun a => congrArg (fun m : BoundedAlgHom K (algebra f g) (algebra f g) => m a)
      (swapMap_comp_swapMap f g))
    (fun a => congrArg (fun m : BoundedAlgHom K (algebra g f) (algebra g f) => m a)
      (swapMap_comp_swapMap g f))

/-- The pushout after restricting the second factor to a domain represents
the inverse image of that domain in the original pushout spectrum. -/
def domainPasting (D : Domain K C) : Domain K (algebra f g) where
  algebra := algebra f (D.baseMap.comp g)
  baseMap := pastingInnerMap f g D.baseMap
  locus := (BanachSpectrum.comap (rightMap f g).toBoundedRingHom) ⁻¹' D.locus
  represents := by
    have h := (D.pullback (rightMap f g)).represents.postcomp_equiv
      (pastingEquiv f g D.baseMap)
    change Represents K ((pastingToDirect f g D.baseMap).comp
        (leftMap (rightMap f g) D.baseMap)) _ at h
    rw [pastingToDirect_comp_left] at h
    exact h

/-- Restriction to a domain of a finite first factor preserves smallness
of the pushout spectrum relative to the second factor spectrum. -/
theorem small_spectrum_of_domain_finiteBanach (D : Domain K B) (hf : f.IsFiniteBanach)
    [Small.{v} (BanachSpectrum C)] :
    Small.{v} (BanachSpectrum (algebra (D.baseMap.comp f) g)) := by
  let : Small.{v} (BanachSpectrum (algebra f g)) :=
    small_spectrum_of_finiteBanachPushout f g finiteBanachPushout hf
  let : Small.{v} (BanachSpectrum (algebra g f)) :=
    small_of_injective (swapEquiv f g).spectrumHomeomorph.injective
  let : Small.{v} (BanachSpectrum (algebra g (D.baseMap.comp f))) :=
    small_of_injective (domainPasting g f D).spectrumMap_injective
  exact small_of_injective (swapEquiv (D.baseMap.comp f) g).spectrumHomeomorph.symm.injective

end Langlands.Analytic.PresentedAffinoidAlgebra.AffinoidPushout
