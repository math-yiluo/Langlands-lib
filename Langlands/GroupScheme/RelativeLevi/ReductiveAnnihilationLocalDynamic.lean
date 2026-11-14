import Langlands.GroupScheme.FppfHomLocality
import Langlands.GroupScheme.RelativeLevi.DynamicReductiveAnnihilation
import Langlands.GroupScheme.RelativeLevi.DynamicRadicalIdentification
import Langlands.GroupScheme.RelativeLevi.UnipotentRadicalDescent

/-! # Relative radical annihilation from pointwise dynamic presentations -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

namespace RelativeLevi

/-- Given the dynamic relative Levi theorem, pointwise etale dynamic
presentations imply that every surjection to a reductive group kills the
supplied relative unipotent radical. -/
theorem annihilates_radical_of_pointwise_dynamic
    (hdynamic : DynamicRelativeLeviStatement.{u})
    {S : Scheme.{u}} {G P U : GroupScheme S} (i : P ⟶ G) (r : U ⟶ P)
    (hG : IsReductive G) (hP : IsRelativeParabolicSubgroup i)
    (hU : IsRelativeUnipotentRadical r)
    (hlocal : ∀ s : S, ∃ (T : Scheme.{u}) (b : T ⟶ S), Etale b ∧
      (∃ t : T, b.base t = s) ∧
      ∃ χ : (Gm T).toGrp ⟶ (GroupScheme.baseChange b).obj G,
        (Dynamic.parabolic χ).IsRepresentedBy ((GroupScheme.baseChange b).map i))
    {H : GroupScheme S} (f : P ⟶ H)
    (hH : IsReductive H) (hf : Surjective f.hom.hom.left) :
    r ≫ f = 0 := by
  let : IsAffineHom P.X.hom := hP.isAffineHom
  apply comp_eq_zero_of_pointwise_etale_baseChange r f
  intro s
  obtain ⟨T, b, hb, hs, χ, hPb⟩ := hlocal s
  let : Etale b := hb
  have hGb : IsReductive ((GroupScheme.baseChange b).obj G) := hG.baseChange b
  let : Smooth ((GroupScheme.baseChange b).obj G).X.hom := hGb.smooth
  let : IsAffineHom ((GroupScheme.baseChange b).obj G).X.hom := hGb.isAffineHom
  have hUb : IsRelativeUnipotentRadical ((GroupScheme.baseChange b).map r) :=
    hU.baseChange_etale b
  have hUdyn := isRepresentedBy_unipotent_of_relativeRadical
    hdynamic hGb χ hPb ((GroupScheme.baseChange b).map r) hUb
  have hfb : Surjective ((GroupScheme.baseChange b).map f).hom.hom.left :=
    MorphismProperty.overPullbackMap (P := @Surjective) b f.hom.hom hf
  exact ⟨T, b, hb, hs, Dynamic.annihilates_contracting_subgroup χ hPb hUdyn
    ((GroupScheme.baseChange b).map f) (hH.baseChange b) hfb⟩

end RelativeLevi

/-- Conditional radical annihilation over every scheme, with the dynamic
relative Levi theorem and pointwise etale dynamic presentations explicit. -/
def RelativeParabolicReductiveAnnihilationLocalDynamicStatement : Prop :=
  DynamicRelativeLeviStatement.{u} →
    ∀ (S : Scheme.{u}) (G P U : GroupScheme S) (i : P ⟶ G) (r : U ⟶ P),
      IsReductive G → IsRelativeParabolicSubgroup i → IsRelativeUnipotentRadical r →
      (∀ s : S, ∃ (T : Scheme.{u}) (b : T ⟶ S), Etale b ∧
        (∃ t : T, b.base t = s) ∧
        ∃ χ : (Gm T).toGrp ⟶ (GroupScheme.baseChange b).obj G,
          (Dynamic.parabolic χ).IsRepresentedBy ((GroupScheme.baseChange b).map i)) →
      ∀ (H : GroupScheme S) (f : P ⟶ H),
        IsReductive H → Surjective f.hom.hom.left → r ≫ f = 0

/-- Identify the radical with the contracting subgroup on each neighborhood,
apply dynamic annihilation and descend the actual zero composite. -/
theorem relativeParabolicReductiveAnnihilationLocalDynamic :
    RelativeParabolicReductiveAnnihilationLocalDynamicStatement.{u} := by
  intro hdynamic S G P U i r hG hP hU hlocal H f hH hf
  exact RelativeLevi.annihilates_radical_of_pointwise_dynamic
    hdynamic i r hG hP hU hlocal f hH hf

end Langlands.GroupScheme
