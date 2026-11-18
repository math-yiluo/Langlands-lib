import Langlands.HarmonicAnalysis.HarishChandraSchwartz.StandardLeviCartanCoverTransport
import Langlands.GroupScheme.Rational.StandardParabolicOrderReduction
import Langlands.GroupScheme.SubgroupFunctor.CentralizerBaseChange

/-! # Retaining the same compatible split component inside a standard Levi -/

noncomputable section

set_option maxRecDepth 4096
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme

namespace Langlands.BruhatTits.SpecialCompact

variable {F : Type u} [Field F]
  {S : CommGroupScheme (Spec (CommRingCat.of F))}
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  (i : S.toGrp ⟶ G) (ν : cocharacterLattice S)
  (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i) (hν : IsGenericCocharacter i ν)
  (J : Set (characterLattice S)) (hJ : J ⊆ simpleRelativeRoots i ν)
  {R : Set (characterLattice S)} (hRJ : R ⊆ J)
  {M : GroupScheme (Spec (CommRingCat.of F))}
  (m : M ⟶ G) (hm : (standardLevi i ν R).IsRepresentedBy m)

local instance componentLeviTransportAffineHom : IsAffineHom (Standard.leviScheme i ν J).X.hom :=
  (Standard.isClosedSubgroup_leviHom i ν J).isAffineHom

/-- Read the same represented inner Levi inside the canonical outer Levi,
using the actual represented-subgroup factorization. -/
def standardLeviComponentRestrictionHom : M ⟶ Standard.leviScheme i ν J :=
  (Standard.isRepresentedBy_leviHom i ν J).factorHom m (by
    rw [hm.2]
    exact standardLevi_mono_of_exists i ν hRJ
      (standardCocharacter F G hG S i hi ν hν R (hRJ.trans hJ)).1)

/-- The restricted embedding composes to the original represented Levi map. -/
theorem standardLeviComponentRestrictionHom_comp :
    standardLeviComponentRestrictionHom i ν hG hi hν J hJ hRJ m hm ≫
      Standard.leviHom i ν J = m := by
  exact (Standard.isRepresentedBy_leviHom i ν J).factorHom_comp _ _

include hG hi hν hJ hRJ in
/-- An ambient compatible component for a nested face is compatible inside
the outer standard Levi, with exactly the same torus A and map q into S. -/
theorem IsCompatibleStandardSplitComponent.leviScheme
    {A : CommGroupScheme (Spec (CommRingCat.of F))} {q : A.toGrp ⟶ S.toGrp}
    (hA : IsCompatibleStandardSplitComponent i ν R A q) :
    IsCompatibleStandardSplitComponent (Standard.leviTorusHom i ν J) ν R A q := by
  obtain ⟨hq, M, m, a, hm, hmc, hM, ha, hcomp⟩ := hA
  let f := standardLeviComponentRestrictionHom i ν hG hi hν J hJ hRJ m hm
  have hfm : f ≫ Standard.leviHom i ν J = m :=
    standardLeviComponentRestrictionHom_comp i ν hG hi hν J hJ hRJ m hm
  have hfamilies := standardLeviStandardFamilies_inter_canonical i ν hG hi hν J R hJ (hRJ.trans hJ)
  have htorus : standardLeviTorusFactor i ν J (Standard.isRepresentedBy_leviHom i ν J) =
      Standard.leviTorusHom i ν J := by
    apply Grp.hom_ext
    exact (Standard.isRepresentedBy_leviHom i ν J).1.right_cancellation _ _
      (congrArg (fun z => z.hom.hom)
        ((standardLeviTorusFactor_comp i ν J (Standard.isRepresentedBy_leviHom i ν J)).trans
          (Standard.leviTorusHom_comp i ν J).symm))
  have hL : standardLevi (Standard.leviTorusHom i ν J) ν R =
      (standardLevi i ν R).comap (Standard.leviHom i ν J) := by
    simpa only [Set.inter_eq_right.mpr hRJ, htorus] using hfamilies.2.1
  refine ⟨hq, M, f, a, ?_, ?_, hM, ha, ?_⟩
  · rw [hL]
    exact (Standard.isRepresentedBy_leviHom i ν J).comap_of_comp hm f hfm
  · exact IsClosedSubgroup.of_comp (Standard.isClosedSubgroup_leviHom i ν J) (by
      rw [hfm]
      exact hmc)
  · have hEq : (a ≫ f) ≫ Standard.leviHom i ν J =
        (q ≫ Standard.leviTorusHom i ν J) ≫ Standard.leviHom i ν J := by
      rw [Category.assoc, hfm, hcomp, Category.assoc, Standard.leviTorusHom_comp]
    have : Mono (Standard.leviHom i ν J).hom.hom :=
      (Standard.isRepresentedBy_leviHom i ν J).1
    apply Grp.hom_ext
    exact (cancel_mono (Standard.leviHom i ν J).hom.hom).mp
      (congrArg (fun z => z.hom.hom) hEq)

end Langlands.BruhatTits.SpecialCompact
