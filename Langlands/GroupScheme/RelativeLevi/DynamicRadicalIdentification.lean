import Langlands.GroupScheme.RelativeLevi.DynamicRadicalComparison
import Langlands.GroupScheme.RelativeLevi.DynamicStatement

/-! # Identifying a relative radical in an ambient dynamic presentation -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme.RelativeLevi

variable {S : Scheme.{u}} {G P N U : GroupScheme S}

/-- Under the dynamic relative Levi theorem, any relative radical of a
represented dynamic parabolic is isomorphic to the ambient dynamic unipotent
representative, compatibly with their maps to the ambient group. -/
def dynamicParabolicRadicalComparison
    (hdynamic : DynamicRelativeLeviStatement.{u})
    (hG : IsReductive G) (χ : (Gm S).toGrp ⟶ G)
    {iP : P ⟶ G} {iU : U ⟶ G}
    (hP : (Dynamic.parabolic χ).IsRepresentedBy iP)
    (hU : (Dynamic.unipotent χ).IsRepresentedBy iU)
    (n : N ⟶ P) (hn : IsRelativeUnipotentRadical n) :
    {e : N ≅ U // e.hom ≫ iU = n ≫ iP} := by
  let : Smooth G.X.hom := hG.smooth
  let : IsAffineHom G.X.hom := hG.isAffineHom
  have hrad : ∀ (r : U ⟶ P), r ≫ iP = iU → IsRelativeUnipotentRadical r := by
    obtain ⟨Z, iZ, _, _, hZ⟩ := (dynamicBaseRepresentability S G χ).2.2
    exact (hdynamic S G P U Z χ iP iU iZ hG hP hU hZ).2.1
  have hle : SubgroupFunctor.range iU ≤ Dynamic.parabolic χ := by
    rw [hU.2]
    exact Dynamic.unipotent_le_parabolic χ
  let r : U ⟶ P := hP.factorHom iU hle
  have hfac : r ≫ iP = iU := hP.factorHom_comp iU hle
  let e := dynamicParabolicRadicalIso χ hP hU r hfac n hn (hrad r hfac)
  refine ⟨e, ?_⟩
  calc
    e.hom ≫ iU = e.hom ≫ r ≫ iP := by rw [hfac]
    _ = n ≫ iP := by
      rw [← Category.assoc, dynamicParabolicRadicalIso_hom_comp]

/-- A relative radical has precisely the ambient dynamic identity-limit
subgroup as its image on every relative test scheme. -/
theorem radical_ambient_range_eq_of_dynamic_parabolic
    (hdynamic : DynamicRelativeLeviStatement.{u})
    (hG : IsReductive G) (χ : (Gm S).toGrp ⟶ G)
    {iP : P ⟶ G} (hP : (Dynamic.parabolic χ).IsRepresentedBy iP)
    (n : N ⟶ P) (hn : IsRelativeUnipotentRadical n) :
    SubgroupFunctor.range (n ≫ iP) = Dynamic.unipotent χ := by
  let : Smooth G.X.hom := hG.smooth
  let : IsAffineHom G.X.hom := hG.isAffineHom
  obtain ⟨U, iU, _, _, hU⟩ := (dynamicBaseRepresentability S G χ).2.1
  let e := dynamicParabolicRadicalComparison hdynamic hG χ hP hU n hn
  rw [← e.2, SubgroupFunctor.range_iso_comp, hU.2]

/-- The ambient composite of any relative radical represents the dynamic
identity-limit subgroup of the ambient cocharacter. -/
theorem isRepresentedBy_unipotent_of_relativeRadical
    (hdynamic : DynamicRelativeLeviStatement.{u})
    (hG : IsReductive G) (χ : (Gm S).toGrp ⟶ G)
    {iP : P ⟶ G} (hP : (Dynamic.parabolic χ).IsRepresentedBy iP)
    (n : N ⟶ P) (hn : IsRelativeUnipotentRadical n) :
    (Dynamic.unipotent χ).IsRepresentedBy (n ≫ iP) := by
  let : Mono iP.hom.hom := hP.1
  let : IsClosedImmersion n.hom.hom.left := hn.isClosedSubgroup
  let : Mono n.hom.hom := Over.mono_of_mono_left _
  exact ⟨by rw [Grp.comp_hom_hom]; infer_instance,
    radical_ambient_range_eq_of_dynamic_parabolic hdynamic hG χ hP n hn⟩

end Langlands.GroupScheme.RelativeLevi
