import Langlands.GroupScheme.RelativeLevi.TorusLeviLocal
import Langlands.GroupScheme.RelativeLevi.LeviCoverDescent
import Langlands.GroupScheme.RelativeLevi.UnipotentRadicalDescent

/-! # Effective descent of prescribed-torus local Levi witnesses -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme.RelativeLevi

namespace TorusDynamicPresentation

variable {S : Scheme.{u}} {G P : GroupScheme S} {T : CommGroupScheme S}
    {i : P ⟶ G} {t : T.toGrp ⟶ P}

/-- A supplied dynamic structure theorem makes a prescribed-torus dynamic
presentation a relative parabolic inclusion. -/
theorem isRelativeParabolicSubgroup (d : TorusDynamicPresentation i t)
    (hDynamic : DynamicRelativeLeviStatement.{u}) (hG : IsReductive G) :
    IsRelativeParabolicSubgroup i := by
  let : Smooth G.X.hom := hG.smooth
  let : IsAffineHom G.X.hom := hG.isAffineHom
  let : LocallyOfFinitePresentation G.X.hom := inferInstance
  let chi := d.cocharacter ≫ t ≫ i
  obtain ⟨U, iU, _, _, hU⟩ := (dynamicBaseRepresentability S G chi).2.1
  obtain ⟨Z, iZ, _, _, hZ⟩ := (dynamicBaseRepresentability S G chi).2.2
  exact (hDynamic S G P U Z chi i iU iZ hG d.represents hU hZ).1

end TorusDynamicPresentation

namespace EtaleTorusLeviData

variable {S : Scheme.{u}} {G P : GroupScheme S} {T : CommGroupScheme S}
    {i : P ⟶ G} {t : T.toGrp ⟶ P}

/-- Descend matching local Levi ranges to an actual global Levi representative.
The dynamic and radical structure statements remain explicit inputs. -/
def leviRepresentative (D : EtaleTorusLeviData i t)
    (hDynamic : DynamicRelativeLeviStatement.{u})
    (hRadical : RelativeUnipotentRadicalStatement.{u})
    (hG : IsReductive G) (hP : IsRelativeParabolicSubgroup i)
    (hmatch : SubgroupFunctor.CoverDescent.IsMatching D.cover
      (fun a => SubgroupFunctor.range (D.witness a).inclusion)) :
    LeviRepresentative (SubgroupFunctor.CoverDescent.subgroup D.cover
      (fun a => SubgroupFunctor.range (D.witness a).inclusion)) := by
  apply Classical.choice
  let : IsAffineHom P.X.hom := hP.isAffineHom
  obtain ⟨U, r, hr, _⟩ := hRadical S G P i hG hP
  choose Uloc rloc hrloc hMul using
    (fun a : D.cover.I₀ => (D.witness a).isLevi.exists_unipotentRadical)
  have hU : ∀ a, SubgroupFunctor.range ((baseChange (D.cover.f a)).map r) =
      SubgroupFunctor.range (rloc a) := by
    intro a
    let : Etale (D.cover.f a) := D.cover.map_prop a
    have hGa := hG.baseChange (D.cover.f a)
    have hPa := (D.presentation a).isRelativeParabolicSubgroup hDynamic hGa
    obtain ⟨U0, r0, _, huniq⟩ := hRadical (D.cover.X a)
      ((baseChange (D.cover.f a)).obj G) ((baseChange (D.cover.f a)).obj P)
      ((baseChange (D.cover.f a)).map i) hGa hPa
    exact (huniq _ _ (hr.baseChange_etale (D.cover.f a))).trans
      (huniq _ _ (hrloc a)).symm
  have hrep : ∀ a, (SubgroupFunctor.range (D.witness a).inclusion).IsRepresentedBy
      (D.witness a).inclusion := by
    intro a
    let : IsClosedImmersion (D.witness a).inclusion.hom.hom.left :=
      (D.witness a).isLevi.isClosedSubgroup
    exact ⟨Over.mono_of_mono_left _, rfl⟩
  exact ⟨leviRepresentativeOfEtaleCover D.cover r hr
    (fun a => SubgroupFunctor.range (D.witness a).inclusion) hmatch
    (fun a => (D.witness a).group) Uloc
    (fun a => (D.witness a).inclusion) rloc hrep
    (fun a => (D.witness a).isLevi.isClosedSubgroup)
    (fun a => (hrloc a).isClosedSubgroup)
    (fun a => (D.witness a).isLevi.smooth) hMul hU⟩

end EtaleTorusLeviData

end Langlands.GroupScheme.RelativeLevi
