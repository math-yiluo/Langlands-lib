import Langlands.GroupScheme.RelativeLevi.DynamicReductiveQuotient
import Langlands.GroupScheme.RelativeLevi.DynamicRadicalIdentification
import Langlands.GroupScheme.RelativeLevi.UnipotentRadicalDescent
import Langlands.GroupScheme.NormalQuotientReductiveGluing

/-! # Relative reductive quotients from pointwise dynamic presentations -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

namespace RelativeLevi

/-- Given the dynamic relative Levi theorem, pointwise etale dynamic
presentations of a relative parabolic give its reductive quotient by any
supplied relative unipotent radical. -/
theorem exists_reductiveQuotient_of_pointwise_dynamic
    (hdynamic : DynamicRelativeLeviStatement.{u})
    {S : Scheme.{u}} {G P U : GroupScheme S} (i : P ⟶ G) (r : U ⟶ P)
    (hG : IsReductive G) (hP : IsRelativeParabolicSubgroup i)
    (hU : IsRelativeUnipotentRadical r)
    (hlocal : ∀ s : S, ∃ (T : Scheme.{u}) (b : T ⟶ S), Etale b ∧
      (∃ t : T, b.base t = s) ∧
      ∃ χ : (Gm T).toGrp ⟶ (GroupScheme.baseChange b).obj G,
        (Dynamic.parabolic χ).IsRepresentedBy ((GroupScheme.baseChange b).map i)) :
    ∃ (M : GroupScheme S) (q : P ⟶ M), IsReductive M ∧
      RelativeRoot.IsFppfQuotient (SubgroupFunctor.range r) q := by
  let : Smooth P.X.hom := hP.smooth
  let : IsAffineHom P.X.hom := hP.isAffineHom
  let : IsClosedImmersion r.hom.hom.left := hU.isClosedSubgroup
  let : Mono r.hom.hom := Over.mono_of_mono_left _
  apply NormalQuotient.exists_reductive_fppfQuotient_of_pointwise_etale
    r hU.smooth hU.isNormal
  intro s
  obtain ⟨T, b, hb, hs, χ, hPb⟩ := hlocal s
  let : Etale b := hb
  have hGb : IsReductive ((GroupScheme.baseChange b).obj G) := hG.baseChange b
  have hUb : IsRelativeUnipotentRadical ((GroupScheme.baseChange b).map r) :=
    hU.baseChange_etale b
  have hUdyn := isRepresentedBy_unipotent_of_relativeRadical
    hdynamic hGb χ hPb ((GroupScheme.baseChange b).map r) hUb
  obtain ⟨Q, q, hQ, hq⟩ := dynamicReductiveQuotient T _ _ _ χ
    ((GroupScheme.baseChange b).map i) ((GroupScheme.baseChange b).map r)
    hGb hPb hUdyn
  exact ⟨T, b, Q, q, hb, hs, hQ, hq⟩

end RelativeLevi

/-- Conditional quotient existence over every scheme, with the dynamic
relative Levi theorem and pointwise etale dynamic presentations explicit. -/
def RelativeParabolicReductiveQuotientLocalDynamicStatement : Prop :=
  DynamicRelativeLeviStatement.{u} →
    ∀ (S : Scheme.{u}) (G P U : GroupScheme S) (i : P ⟶ G) (r : U ⟶ P),
      IsReductive G → IsRelativeParabolicSubgroup i → IsRelativeUnipotentRadical r →
      (∀ s : S, ∃ (T : Scheme.{u}) (b : T ⟶ S), Etale b ∧
        (∃ t : T, b.base t = s) ∧
        ∃ χ : (Gm T).toGrp ⟶ (GroupScheme.baseChange b).obj G,
          (Dynamic.parabolic χ).IsRepresentedBy ((GroupScheme.baseChange b).map i)) →
      ∃ (M : GroupScheme S) (q : P ⟶ M), IsReductive M ∧
        RelativeRoot.IsFppfQuotient (SubgroupFunctor.range r) q

/-- Identify the pulled-back radical with the contracting subgroup, form the
local limit-map quotients and descend them with their reductivity. -/
theorem relativeParabolicReductiveQuotientLocalDynamic :
    RelativeParabolicReductiveQuotientLocalDynamicStatement.{u} := by
  intro hdynamic S G P U i r hG hP hU hlocal
  exact RelativeLevi.exists_reductiveQuotient_of_pointwise_dynamic
    hdynamic i r hG hP hU hlocal

end Langlands.GroupScheme
