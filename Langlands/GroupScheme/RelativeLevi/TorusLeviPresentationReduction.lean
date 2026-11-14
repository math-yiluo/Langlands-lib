import Langlands.GroupScheme.RelativeLevi.TorusLeviDynamicLocal
import Langlands.GroupScheme.RelativeLevi.UnipotentRadicalExistence
import Langlands.GroupScheme.RelativeLevi.TorusLeviGluing
import Langlands.GroupScheme.RelativeLevi.TorusLeviStatement

/-! # Prescribed-torus Levi descent from local dynamic presentations -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme.RelativeLevi

namespace EtaleTorusLeviData

variable {S : Scheme.{u}} {G P : GroupScheme S} {T : CommGroupScheme S}
    {i : P ⟶ G} {t : T.toGrp ⟶ P}

/-- Construct the global radical and descend the local Levi witnesses on
the same cover, using the proved dynamic structure theorem. -/
def leviRepresentativeFromDynamic (D : EtaleTorusLeviData i t)
    (hG : IsReductive G) [IsAffineHom P.X.hom] :
    LeviRepresentative (SubgroupFunctor.CoverDescent.subgroup D.cover
      (fun a => SubgroupFunctor.range (D.witness a).inclusion)) := by
  apply Classical.choice
  have hlocal : ∀ a : D.cover.I₀,
      ∃ chi : (Gm (D.cover.X a)).toGrp ⟶ (baseChange (D.cover.f a)).obj G,
        (Dynamic.parabolic chi).IsRepresentedBy ((baseChange (D.cover.f a)).map i) := by
    intro a
    exact ⟨(D.presentation a).cocharacter ≫ (baseChange (D.cover.f a)).map t ≫
      (baseChange (D.cover.f a)).map i, (D.presentation a).represents⟩
  let R := radicalOfEtaleDynamicCover dynamicRelativeLevi hG i D.cover hlocal
  choose Uloc rloc hrloc hMul using
    (fun a : D.cover.I₀ => (D.witness a).isLevi.exists_unipotentRadical)
  have hU : ∀ a, SubgroupFunctor.range ((baseChange (D.cover.f a)).map R.2.val) =
      SubgroupFunctor.range (rloc a) := by
    intro a
    let : Etale (D.cover.f a) := D.cover.map_prop a
    exact radical_range_eq_of_dynamic_parabolic dynamicRelativeLevi
      (hG.baseChange (D.cover.f a))
      ((D.presentation a).cocharacter ≫ (baseChange (D.cover.f a)).map t ≫
        (baseChange (D.cover.f a)).map i)
      (D.presentation a).represents _ _
      (R.2.property.baseChange_etale (D.cover.f a)) (hrloc a)
  have hrep : ∀ a, (SubgroupFunctor.range (D.witness a).inclusion).IsRepresentedBy
      (D.witness a).inclusion := by
    intro a
    let : IsClosedImmersion (D.witness a).inclusion.hom.hom.left :=
      (D.witness a).isLevi.isClosedSubgroup
    exact ⟨Over.mono_of_mono_left _, rfl⟩
  exact ⟨leviRepresentativeOfEtaleCover D.cover R.2.val R.2.property
    (fun a => SubgroupFunctor.range (D.witness a).inclusion)
    (D.isMatchingFromDynamic hG) (fun a => (D.witness a).group) Uloc
    (fun a => (D.witness a).inclusion) rloc hrep
    (fun a => (D.witness a).isLevi.isClosedSubgroup)
    (fun a => (hrloc a).isClosedSubgroup)
    (fun a => (D.witness a).isLevi.smooth) hMul hU⟩

end EtaleTorusLeviData

/-- Construct the local data with only the prescribed-torus presentation
statement as an unproved structure input. -/
def torusLeviEtaleDataFromPresentation
    (hPresentation : RelativeTorusDynamicPresentationStatement.{u})
    {S : Scheme.{u}} {G P : GroupScheme S} {T : CommGroupScheme S}
    (i : P ⟶ G) (t : T.toGrp ⟶ P) (hG : IsReductive G)
    (hP : IsRelativeParabolicSubgroup i) (hT : RelativeTorus.IsTorus T.toGrp)
    (ht : IsClosedSubgroup t) (hmax : IsFibrewiseMaximalTorus t) :
    EtaleTorusLeviData i t := by
  apply Classical.choice
  obtain ⟨𝒰, h𝒰⟩ := hPresentation S G P i T t hG hP hT ht hmax
  let d : ∀ a : 𝒰.I₀,
      TorusDynamicPresentation ((GroupScheme.baseChange (𝒰.f a)).map i)
        (T := (CommGroupScheme.baseChange (𝒰.f a)).obj T)
        ((GroupScheme.baseChange (𝒰.f a)).map t) :=
    fun a => ⟨(h𝒰 a).choose, (h𝒰 a).choose_spec⟩
  exact ⟨⟨𝒰, d, fun a => (d a).witnessFromDynamic (hG.baseChange (𝒰.f a))⟩⟩

/-- Construct the unique global Levi containing a prescribed maximal torus,
conditional only on prescribed-torus dynamic presentations. -/
def torusLeviWitnessFromPresentation
    (hPresentation : RelativeTorusDynamicPresentationStatement.{u})
    {S : Scheme.{u}} {G P : GroupScheme S} {T : CommGroupScheme S}
    (i : P ⟶ G) (t : T.toGrp ⟶ P) (hG : IsReductive G)
    (hP : IsRelativeParabolicSubgroup i) (hT : RelativeTorus.IsTorus T.toGrp)
    (ht : IsClosedSubgroup t) (hmax : IsFibrewiseMaximalTorus t) :
    TorusLeviWitness t := by
  let : IsAffineHom P.X.hom := hP.isAffineHom
  let D := torusLeviEtaleDataFromPresentation hPresentation i t hG hP hT ht hmax
  exact D.witnessOfLeviRepresentative (D.leviRepresentativeFromDynamic hG)

/-- Prescribed-torus dynamic presentations imply the unchanged arbitrary-base
maximal-torus Levi statement. -/
theorem relativeTorusLevi_of_dynamicPresentation
    (hPresentation : RelativeTorusDynamicPresentationStatement.{u}) :
    RelativeTorusLeviStatement.{u} := by
  intro S G P i T t hG hP hT ht hmax
  let w := torusLeviWitnessFromPresentation hPresentation i t hG hP hT ht hmax
  exact ⟨w.group, w.inclusion, w.isLevi, w.contains, w.unique⟩

end Langlands.GroupScheme.RelativeLevi
