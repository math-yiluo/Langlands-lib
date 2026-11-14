import Langlands.GroupScheme.RelativeLevi.DynamicRadicalIdentification
import Langlands.GroupScheme.RelativeLevi.UnipotentRadicalDescent
import Langlands.GroupScheme.SubgroupFunctor.EtaleComparison
import Langlands.GroupScheme.Reductive.BaseChange

/-! # Uniqueness of relative radicals from etale-local dynamics -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme.RelativeLevi

variable {S : Scheme.{u}} {G P N U : GroupScheme S}

/-- Two relative radicals of a represented dynamic parabolic have the same
image on every test scheme. -/
theorem radical_range_eq_of_dynamic_parabolic
    (hdynamic : DynamicRelativeLeviStatement.{u})
    (hG : IsReductive G) (χ : (Gm S).toGrp ⟶ G)
    {iP : P ⟶ G} (hP : (Dynamic.parabolic χ).IsRepresentedBy iP)
    (n : N ⟶ P) (r : U ⟶ P)
    (hn : IsRelativeUnipotentRadical n) (hr : IsRelativeUnipotentRadical r) :
    SubgroupFunctor.range n = SubgroupFunctor.range r := by
  let hN := isRepresentedBy_unipotent_of_relativeRadical hdynamic hG χ hP n hn
  let hU := isRepresentedBy_unipotent_of_relativeRadical hdynamic hG χ hP r hr
  let e : N ≅ U := hN.isoOfIsRepresentedBy hU
  have he : e.hom ≫ (r ≫ iP) = n ≫ iP :=
    hN.isoOfIsRepresentedBy_hom_comp hU
  let : Mono iP.hom.hom := hP.1
  have hcomp : e.hom ≫ r = n := hP.hom_ext (by simpa only [Category.assoc] using he)
  rw [← hcomp, SubgroupFunctor.range_iso_comp]

/-- Etale-local dynamic presentations detect uniqueness of supplied relative
radicals over an arbitrary base. -/
theorem radical_range_eq_of_etale_dynamicCover
    (hdynamic : DynamicRelativeLeviStatement.{u})
    (hG : IsReductive G) [IsAffineHom P.X.hom] (iP : P ⟶ G)
    (𝒰 : Scheme.Cover.{u} (Scheme.precoverage @Etale) S)
    (hlocal : ∀ j, ∃ χ : (Gm (𝒰.X j)).toGrp ⟶ (baseChange (𝒰.f j)).obj G,
      (Dynamic.parabolic χ).IsRepresentedBy ((baseChange (𝒰.f j)).map iP))
    (n : N ⟶ P) (r : U ⟶ P)
    (hn : IsRelativeUnipotentRadical n) (hr : IsRelativeUnipotentRadical r) :
    SubgroupFunctor.range n = SubgroupFunctor.range r := by
  let : IsClosedImmersion n.hom.hom.left := hn.isClosedSubgroup
  let : IsClosedImmersion r.hom.hom.left := hr.isClosedSubgroup
  let : Mono n.hom.hom := Over.mono_of_mono_left _
  let : Mono r.hom.hom := Over.mono_of_mono_left _
  apply SubgroupFunctor.range_eq_of_baseChange_etaleCover 𝒰 n r
  intro j
  let : Etale (𝒰.f j) := 𝒰.map_prop j
  obtain ⟨χ, hχ⟩ := hlocal j
  exact radical_range_eq_of_dynamic_parabolic hdynamic (hG.baseChange (𝒰.f j)) χ hχ
    _ _ (hn.baseChange_etale (𝒰.f j)) (hr.baseChange_etale (𝒰.f j))

/-- The unique compatible comparison of two supplied relative radicals when
an etale cover of the parabolic has dynamic presentations. -/
def radicalIsoOfEtaleDynamicCover
    (hdynamic : DynamicRelativeLeviStatement.{u})
    (hG : IsReductive G) [IsAffineHom P.X.hom] (iP : P ⟶ G)
    (𝒰 : Scheme.Cover.{u} (Scheme.precoverage @Etale) S)
    (hlocal : ∀ j, ∃ χ : (Gm (𝒰.X j)).toGrp ⟶ (baseChange (𝒰.f j)).obj G,
      (Dynamic.parabolic χ).IsRepresentedBy ((baseChange (𝒰.f j)).map iP))
    (n : N ⟶ P) (r : U ⟶ P)
    (hn : IsRelativeUnipotentRadical n) (hr : IsRelativeUnipotentRadical r) :
    {e : N ≅ U // e.hom ≫ r = n} := by
  let : IsClosedImmersion n.hom.hom.left := hn.isClosedSubgroup
  let : IsClosedImmersion r.hom.hom.left := hr.isClosedSubgroup
  let : Mono n.hom.hom := Over.mono_of_mono_left _
  let : Mono r.hom.hom := Over.mono_of_mono_left _
  let hN : (SubgroupFunctor.range r).IsRepresentedBy n :=
    ⟨inferInstance, radical_range_eq_of_etale_dynamicCover hdynamic hG iP 𝒰 hlocal n r hn hr⟩
  let hU : (SubgroupFunctor.range r).IsRepresentedBy r := ⟨inferInstance, rfl⟩
  exact ⟨hN.isoOfIsRepresentedBy hU, hN.isoOfIsRepresentedBy_hom_comp hU⟩

end Langlands.GroupScheme.RelativeLevi
