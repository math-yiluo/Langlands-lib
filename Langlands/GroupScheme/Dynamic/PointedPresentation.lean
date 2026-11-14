import Langlands.GroupScheme.Dynamic.PresentationComparison
import Langlands.GroupScheme.RelativeLevi.ParabolicTransport
import Langlands.GroupScheme.RelativeLevi.ParabolicSourceGeometry
import Langlands.GroupScheme.RelativeParabolicNormalizerReduction

/-! # Pointed dynamic presentations of relative parabolics -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme.Dynamic

variable {S : Scheme.{u}} {G P : GroupScheme S}

/-- A presentation on a pointed etale neighbourhood, recovering the specified
ambient residue cocharacter exactly. -/
structure PointedPresentationData (i : P ⟶ G) (s : S)
    (ν : (Gm (Spec (S.residueField s))).toGrp ⟶
      (baseChange (S.fromSpecResidueField s)).obj G) where
  U : Scheme.{u}
  projection : U ⟶ S
  etale : Etale projection
  point : Spec (S.residueField s) ⟶ U
  point_projection : point ≫ projection = S.fromSpecResidueField s
  cocharacter : (Gm U).toGrp ⟶ (baseChange projection).obj G
  presents : SubgroupFunctor.range ((baseChange projection).map i) =
    parabolic cocharacter
  recovers : baseChangeCocharacter point cocharacter ≫
    (Descent.pullbackComparison projection point (S.fromSpecResidueField s)
      point_projection G).hom = ν

private def pointedPresentationOfLiftAndLocal
    (i : P ⟶ G) (s : S)
    (ν : (Gm (Spec (S.residueField s))).toGrp ⟶
      (baseChange (S.fromSpecResidueField s)).obj G)
    (χ₀ : (Gm (Spec (S.residueField s))).toGrp ⟶
      (baseChange (S.fromSpecResidueField s)).obj P)
    (L : HomScheme.PointedEtaleCocharacterLiftData S P s χ₀)
    (N : ParabolicPresentationNeighbourhoodData ((baseChange L.projection).map i)
      L.cocharacter L.residuePoint)
    (hamb : baseChangeCocharacter L.residuePoint
        (L.cocharacter ≫ (baseChange L.projection).map i) ≫
      (Descent.pullbackComparison L.projection L.residuePoint
        (S.fromSpecResidueField s) L.residue_over G).hom = ν) :
    PointedPresentationData i s ν := by
  let p := L.projection
  let q := N.projection
  let r := q ≫ p
  let a := S.fromSpecResidueField s
  have hb : N.point ≫ r = a := by
    rw [← Category.assoc, N.point_projection]
    exact L.residue_over
  let : IsOpenImmersion q := N.isOpenImmersion
  let : Etale p := L.etale
  refine ⟨N.U, r, inferInstance, N.point, hb,
    pullbackCocharacter p q r rfl (L.cocharacter ≫ (baseChange p).map i), ?_, ?_⟩
  · have hh := (range_eq_parabolic_comp_iso_iff _ _
        (Descent.pullbackComparison p q r rfl G)).mpr N.presents
    rw [Descent.pullbackComparison_naturality, SubgroupFunctor.range_iso_comp] at hh
    exact hh
  · exact (pullbackCocharacter_recovers p q r rfl N.point L.residuePoint a
      N.point_projection L.residue_over hb
      (L.cocharacter ≫ (baseChange p).map i)).trans hamb

private def pointedPresentationOfLift (i : P ⟶ G) (hG : IsReductive G)
    (hi : IsRelativeParabolicSubgroup i) (s : S)
    (ν : (Gm (Spec (S.residueField s))).toGrp ⟶
      (baseChange (S.fromSpecResidueField s)).obj G)
    (hν : SubgroupFunctor.range ((baseChange (S.fromSpecResidueField s)).map i) =
      parabolic ν)
    (χ₀ : (Gm (Spec (S.residueField s))).toGrp ⟶
      (baseChange (S.fromSpecResidueField s)).obj P)
    (hχ₀ : χ₀ ≫ (baseChange (S.fromSpecResidueField s)).map i = ν)
    (L : HomScheme.PointedEtaleCocharacterLiftData S P s χ₀) :
    PointedPresentationData i s ν := by
  let a := S.fromSpecResidueField s
  let p := L.projection
  let iU := (baseChange p).map i
  have hiU : IsRelativeParabolicSubgroup iU := hi.baseChange hG p
  have hGU := hG.baseChange p
  let : Smooth ((baseChange p).obj P).X.hom := hiU.smooth
  let : IsAffineHom ((baseChange p).obj P).X.hom := hiU.isAffineHom
  let : GeometricallyConnected ((baseChange p).obj P).X.hom :=
    hiU.geometricallyConnected hGU
  let : Smooth ((baseChange p).obj G).X.hom := hGU.smooth
  let : IsAffineHom ((baseChange p).obj G).X.hom := hGU.isAffineHom
  let : GeometricallyConnected ((baseChange p).obj G).X.hom :=
    hGU.geometricallyConnected
  let : Mono iU.hom.hom := hiU.mono
  let : Mono iU.hom.hom.left := Over.mono_left_of_mono _
  have hamb : baseChangeCocharacter L.residuePoint (L.cocharacter ≫ iU) ≫
      (Descent.pullbackComparison p L.residuePoint a L.residue_over G).hom = ν :=
    (ambient_cocharacter_recovers p L.residuePoint a L.residue_over i
      L.cocharacter χ₀ L.recovers).trans hχ₀
  have hfib := fibre_presentation_of_recovers p L.residuePoint a L.residue_over
    i L.cocharacter ν hν hamb
  let N := parabolicPresentationNeighbourhood iU L.cocharacter L.residuePoint
    (hiU.residueFiber _).isClosedSubgroup hfib
  exact pointedPresentationOfLiftAndLocal i s ν χ₀ L N hamb

/-- Extend any specified dynamic presentation of a relative parabolic residue
fibre to a pointed etale neighbourhood. -/
def pointedPresentation (i : P ⟶ G) (hG : IsReductive G)
    (hi : IsRelativeParabolicSubgroup i) (s : S)
    (ν : (Gm (Spec (S.residueField s))).toGrp ⟶
      (baseChange (S.fromSpecResidueField s)).obj G)
    (hν : SubgroupFunctor.range ((baseChange (S.fromSpecResidueField s)).map i) =
      parabolic ν) : PointedPresentationData i s ν := by
  let : Smooth P.X.hom := hi.smooth
  let : IsAffineHom P.X.hom := hi.isAffineHom
  let a := S.fromSpecResidueField s
  let i₀ := (baseChange a).map i
  let : IsClosedImmersion i₀.hom.hom.left := (hi.residueFiber s).isClosedSubgroup
  let : Mono i₀.hom.hom := Over.mono_of_mono_left _
  have hrepr : (parabolic ν).IsRepresentedBy i₀ := ⟨inferInstance, hν⟩
  let χ₀ := cocharacterToParabolic hrepr
  have hχ₀ : χ₀ ≫ i₀ = ν := cocharacterToParabolic_comp hrepr
  exact pointedPresentationOfLift i hG hi s ν hν χ₀ hχ₀
    (HomScheme.pointedEtaleCocharacterLift S P s χ₀)

end Langlands.GroupScheme.Dynamic
