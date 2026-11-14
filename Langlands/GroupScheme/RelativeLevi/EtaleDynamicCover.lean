import Langlands.GroupScheme.RelativeLevi.UnipotentRadicalUniqueness

/-! # Etale dynamic covers from pointwise presentations -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme.RelativeLevi

variable {S : Scheme.{u}} {G P N U : GroupScheme S}

/-- Choose one etale dynamic neighbourhood for each base point. The resulting
family is an etale cover carrying the supplied all-test presentations. -/
def etaleDynamicCoverOfPointwise (iP : P ⟶ G)
    (hlocal : ∀ s : S, ∃ (T : Scheme.{u}) (f : T ⟶ S), Etale f ∧
      (∃ t : T, f.base t = s) ∧
      ∃ χ : (Gm T).toGrp ⟶ (baseChange f).obj G,
        (Dynamic.parabolic χ).IsRepresentedBy ((baseChange f).map iP)) :
    {𝒰 : Scheme.Cover.{u} (Scheme.precoverage @Etale) S //
      ∀ j, ∃ χ : (Gm (𝒰.X j)).toGrp ⟶ (baseChange (𝒰.f j)).obj G,
        (Dynamic.parabolic χ).IsRepresentedBy ((baseChange (𝒰.f j)).map iP)} := by
  classical
  choose T f hf hpoint χ hχ using hlocal
  let 𝒰 : Scheme.Cover.{u} (Scheme.precoverage @Etale) S :=
    Scheme.Cover.mkOfCovers S T f (fun s => ⟨s, hpoint s⟩) hf
  exact ⟨𝒰, fun j => ⟨χ j, hχ j⟩⟩

/-- Pointwise etale dynamic presentations suffice for equality of any two
supplied relative radicals. -/
theorem radical_range_eq_of_pointwise_dynamic
    (hdynamic : DynamicRelativeLeviStatement.{u}) (hG : IsReductive G)
    [IsAffineHom P.X.hom] (iP : P ⟶ G)
    (hlocal : ∀ s : S, ∃ (T : Scheme.{u}) (f : T ⟶ S), Etale f ∧
      (∃ t : T, f.base t = s) ∧
      ∃ χ : (Gm T).toGrp ⟶ (baseChange f).obj G,
        (Dynamic.parabolic χ).IsRepresentedBy ((baseChange f).map iP))
    (n : N ⟶ P) (r : U ⟶ P)
    (hn : IsRelativeUnipotentRadical n) (hr : IsRelativeUnipotentRadical r) :
    SubgroupFunctor.range n = SubgroupFunctor.range r :=
  let d := etaleDynamicCoverOfPointwise iP hlocal
  radical_range_eq_of_etale_dynamicCover hdynamic hG iP d.1 d.2 n r hn hr

/-- The compatible isomorphism between supplied relative radicals obtained
from pointwise etale dynamic presentations. -/
def radicalIsoOfPointwiseDynamic
    (hdynamic : DynamicRelativeLeviStatement.{u}) (hG : IsReductive G)
    [IsAffineHom P.X.hom] (iP : P ⟶ G)
    (hlocal : ∀ s : S, ∃ (T : Scheme.{u}) (f : T ⟶ S), Etale f ∧
      (∃ t : T, f.base t = s) ∧
      ∃ χ : (Gm T).toGrp ⟶ (baseChange f).obj G,
        (Dynamic.parabolic χ).IsRepresentedBy ((baseChange f).map iP))
    (n : N ⟶ P) (r : U ⟶ P)
    (hn : IsRelativeUnipotentRadical n) (hr : IsRelativeUnipotentRadical r) :
    {e : N ≅ U // e.hom ≫ r = n} :=
  let d := etaleDynamicCoverOfPointwise iP hlocal
  radicalIsoOfEtaleDynamicCover hdynamic hG iP d.1 d.2 n r hn hr

end Langlands.GroupScheme.RelativeLevi
