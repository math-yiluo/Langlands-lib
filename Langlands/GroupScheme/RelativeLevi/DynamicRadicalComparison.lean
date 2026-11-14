import Langlands.GroupScheme.RelativeLevi.UnipotentRadicalRigidity
import Langlands.GroupScheme.Dynamic.NormalizedLimits
import Langlands.GroupScheme.Dynamic.RepresentedStructure
import Langlands.GroupScheme.SubgroupFunctor.IntersectionNormalizer

/-! # Comparing relative radicals of a represented dynamic parabolic -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme

namespace Dynamic

variable {S : Scheme.{u}} {G P U : GroupScheme S}
    (χ : (Gm S).toGrp ⟶ G) {iP : P ⟶ G}

/-- A cocharacter lifts to any representative of its dynamic parabolic. -/
def parabolicCocharacter (hP : (parabolic χ).IsRepresentedBy iP) :
    (Gm S).toGrp ⟶ P :=
  hP.factorHom χ ((range_le_centralizer χ).trans (centralizer_le_parabolic χ))

/-- The lifted cocharacter has the prescribed ambient composite. -/
theorem parabolicCocharacter_comp (hP : (parabolic χ).IsRepresentedBy iP) :
    parabolicCocharacter χ hP ≫ iP = χ :=
  hP.factorHom_comp _ _

/-- A representative of the ambient identity-limit subgroup represents the
identity-limit subgroup of the lifted cocharacter in the parabolic. -/
theorem isRepresentedBy_unipotent_parabolic_factor
    (hP : (parabolic χ).IsRepresentedBy iP) (hPc : IsClosedSubgroup iP)
    (χP : (Gm S).toGrp ⟶ P) (hχ : χP ≫ iP = χ)
    {iU : U ⟶ G} (hU : (unipotent χ).IsRepresentedBy iU)
    (r : U ⟶ P) (hr : r ≫ iP = iU) :
    (unipotent χP).IsRepresentedBy r := by
  let : Mono iP.hom.hom := hP.1
  let : Mono iU.hom.hom := hU.1
  have hfac : r.hom.hom ≫ iP.hom.hom = iU.hom.hom := by
    rw [← Grp.comp_hom_hom, hr]
  refine ⟨mono_of_mono_fac hfac, ?_⟩
  have hrange : SubgroupFunctor.range (r ≫ iP) =
      SubgroupFunctor.range iP ⊓ unipotent χ := by
    rw [hr, hU.2, hP.2]
    exact SubgroupFunctor.ext fun T =>
      (inf_eq_right.mpr (unipotent_le_parabolic χ T)).symm
  have h := SubgroupFunctor.range_eq_comap_of_range_comp_eq_inf
    r iP (unipotent χ) hrange
  rw [← hχ, ← unipotent_eq_comap_of_isClosedSubgroup χP iP hPc] at h
  exact h

end Dynamic

namespace RelativeLevi

variable {S : Scheme.{u}} {G P N U : GroupScheme S}

/-- The comparison with a dynamic relative radical needs only the ambient
dynamic presentation: the cocharacter and radical are lifted into P internally. -/
def dynamicParabolicRadicalIso
    [IsAffineHom G.X.hom] [LocallyOfFinitePresentation G.X.hom]
    (χ : (Gm S).toGrp ⟶ G) {iP : P ⟶ G} {iU : U ⟶ G}
    (hP : (Dynamic.parabolic χ).IsRepresentedBy iP)
    (hU : (Dynamic.unipotent χ).IsRepresentedBy iU)
    (r : U ⟶ P) (hrcomp : r ≫ iP = iU)
    (n : N ⟶ P)
    (hn : IsRelativeUnipotentRadical n) (hr : IsRelativeUnipotentRadical r) :
    N ≅ U := by
  have hPc : IsClosedSubgroup iP := by
    obtain ⟨P', iP', hc, _, hP'⟩ :=
      (dynamicBaseRepresentability S G χ).1
    exact hP.isClosedSubgroup hP' hc
  let : IsClosedImmersion iP.hom.hom.left := hPc
  let : IsAffineHom P.X.hom := by
    rw [← Over.w iP.hom.hom]
    infer_instance
  exact dynamicRadicalIso n r (Dynamic.parabolicCocharacter χ hP) hn hr
    (Dynamic.isRepresentedBy_unipotent_parabolic_factor χ hP hPc
      _ (Dynamic.parabolicCocharacter_comp χ hP) hU r hrcomp)

/-- The comparison commutes with the two inclusions into the parabolic. -/
theorem dynamicParabolicRadicalIso_hom_comp
    [IsAffineHom G.X.hom] [LocallyOfFinitePresentation G.X.hom]
    (χ : (Gm S).toGrp ⟶ G) {iP : P ⟶ G} {iU : U ⟶ G}
    (hP : (Dynamic.parabolic χ).IsRepresentedBy iP)
    (hU : (Dynamic.unipotent χ).IsRepresentedBy iU)
    (r : U ⟶ P) (hrcomp : r ≫ iP = iU)
    (n : N ⟶ P)
    (hn : IsRelativeUnipotentRadical n) (hr : IsRelativeUnipotentRadical r) :
    (dynamicParabolicRadicalIso χ hP hU r hrcomp n hn hr).hom ≫ r = n :=
  SubgroupFunctor.IsRepresentedBy.isoOfIsRepresentedBy_hom_comp _ _

end RelativeLevi

end Langlands.GroupScheme
