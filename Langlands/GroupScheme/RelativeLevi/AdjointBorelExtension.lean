import Langlands.GroupScheme.RelativeLevi.AdjointTorusStabilizer
import Langlands.GroupScheme.SectionedQuotientExtension

/-! # The sectioned adjoint Borel extension with its original radical -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace RelativeLevi

variable {S : Scheme.{u}} {G B A : GroupScheme S}
    (i : B ⟶ G) (q : G ⟶ A) (a : AutomorphicAction A G)
    (T : CommGroupScheme S) (t : T.toGrp ⟶ B)

/-- Actual Borel and torus stabilizer quotients, with the original Borel
radical and the factorization of the whole ambient kernel through the torus. -/
structure AdjointBorelExtensionData where
  borel : SubgroupFunctor.QuotientSubgroupData i q
    (a.subgroupStabilizer (SubgroupFunctor.range i))
  torus : SubgroupFunctor.QuotientSubgroupData t borel.projection
    ((a.restrict borel.inclusion).subgroupStabilizer (SubgroupFunctor.range (t ≫ i)))
  retraction : FppfRetractionData t
  centerToTorus : kernel q ⟶ T.toGrp
  centerToTorus_comp : centerToTorus ≫ (t ≫ i) = kernelι q
  borel_quotient : RelativeRoot.IsFppfQuotient
    (SubgroupFunctor.range (centerToTorus ≫ t)) borel.projection
  torus_quotient : RelativeRoot.IsFppfQuotient
    (SubgroupFunctor.range centerToTorus) torus.projection

namespace AdjointBorelExtensionData

variable {i q a T t} (d : AdjointBorelExtensionData i q a T t)

/-- The actual descended Borel projection onto the actual torus quotient. -/
def projection : d.borel.group ⟶ d.torus.group :=
  SectionedQuotientExtension.hom d.retraction.projection t d.centerToTorus
    d.borel.projection d.torus.projection d.retraction.section_eq
    d.borel_quotient d.torus_quotient

@[reassoc]
theorem projection_fac :
    d.borel.projection ≫ d.projection =
      d.retraction.projection ≫ d.torus.projection :=
  SectionedQuotientExtension.fac _ _ _ _ _ _ _ _

/-- The actual torus stabilizer inclusion splits the descended projection. -/
theorem section_eq : d.torus.inclusion ≫ d.projection = 𝟙 d.torus.group := by
  let : Flat d.torus.projection.hom.hom.left := d.torus.flat
  let : Surjective d.torus.projection.hom.hom.left := d.torus.surjective
  let : LocallyOfFinitePresentation d.torus.projection.hom.hom.left :=
    d.torus.locallyOfFinitePresentation
  let : Epi d.torus.projection.hom.hom := Over.epi_of_epi_left _
  let : Epi d.torus.projection :=
    (Grp.forget _).epi_of_epi_map (inferInstanceAs (Epi d.torus.projection.hom.hom))
  apply (cancel_epi d.torus.projection).mp
  rw [← Category.assoc, ← d.torus.square, Category.assoc, d.projection_fac,
    ← Category.assoc, d.retraction.section_eq, Category.id_comp, Category.comp_id]

/-- The original radical still embeds in the adjoint Borel quotient. -/
theorem radical_mono :
    Mono (d.retraction.radicalInclusion ≫ d.borel.projection).hom.hom := by
  let : Mono d.retraction.radicalInclusion.hom.hom :=
    d.retraction.isRelativeUnipotentRadical.isClosedSubgroup.mono_overHom
  exact SectionedQuotientExtension.inclusion_mono _ _ _ _ _
    d.retraction.section_eq d.retraction.isFppfQuotient d.borel_quotient

/-- The descended map is an fppf quotient by the original, unchanged radical. -/
theorem isFppfQuotient :
    RelativeRoot.IsFppfQuotient
      (SubgroupFunctor.range (d.retraction.radicalInclusion ≫ d.borel.projection))
      d.projection := by
  let : Mono d.retraction.radicalInclusion.hom.hom :=
    d.retraction.isRelativeUnipotentRadical.isClosedSubgroup.mono_overHom
  exact SectionedQuotientExtension.isFppfQuotient _ _ _ _ _ _
    d.retraction.section_eq d.retraction.isFppfQuotient
    d.borel_quotient d.torus_quotient

/-- A separated quotient target makes the unchanged radical a closed subgroup. -/
theorem radical_isClosedSubgroup [IsSeparated d.torus.group.X.hom] :
    IsClosedSubgroup (d.retraction.radicalInclusion ≫ d.borel.projection) := by
  let : Mono d.retraction.radicalInclusion.hom.hom :=
    d.retraction.isRelativeUnipotentRadical.isClosedSubgroup.mono_overHom
  exact SectionedQuotientExtension.inclusion_isClosedSubgroup _ _ _ _ _ _
    d.retraction.section_eq d.retraction.isFppfQuotient
    d.borel_quotient d.torus_quotient

end AdjointBorelExtensionData
end RelativeLevi

section OverRing

variable {R : Type u} [CommRing R]
    {G B A : GroupScheme (Spec (CommRingCat.of R))}
    {i : B ⟶ G} (hi : IsRelativeBorelSubgroup i) (hG : IsReductive G)
    (q : G ⟶ A) (hq : RelativeRoot.IsFppfQuotient (center G) q)
    (a : AutomorphicAction A G)
    (ha : a.restrict q = AutomorphicAction.conjugation (𝟙 G))
    (T : CommGroupScheme (Spec (CommRingCat.of R))) (t : T.toGrp ⟶ B)
    (hT : RelativeTorus.IsTorus T.toGrp)
    (htG : IsClosedSubgroup (t ≫ i))
    (hmax : IsFibrewiseMaximalTorus (t ≫ i))

include hi hG hq ha hT htG hmax in
private theorem adjointBorelExtensionData_nonempty :
    Nonempty (RelativeLevi.AdjointBorelExtensionData i q a T t) := by
  let dB := hi.adjointStabilizerData hG q hq a ha
  let dT := hi.adjointTorusStabilizerData hG q hq a ha T t hT htG hmax
  let rd := hi.maximalTorusFppfRetractionData hG T t hT htG hmax
  let : Mono i.hom.hom := hi.1.mono
  let : Mono (t ≫ i).hom.hom := htG.mono_overHom
  have hz : IsCentral (kernelι q) := by
    apply (isCentral_iff_range_le_center _).mpr
    exact hq.2.2.2.le
  let z := relativeMaximalTorusCentralFactor hG hT (t ≫ i) htG hmax (kernelι q) hz
  have hf : z ≫ (t ≫ i) = kernelι q :=
    relativeMaximalTorusCentralFactor_comp hG hT (t ≫ i) htG hmax (kernelι q) hz
  have hB : RelativeRoot.IsFppfQuotient
      (SubgroupFunctor.range (z ≫ t)) dB.projection := by
    refine ⟨dB.flat, dB.surjective, dB.locallyOfFinitePresentation, ?_⟩
    rw [dB.kernel_eq]
    exact SubgroupFunctor.comap_range_of_factor i (kernelι q) (z ≫ t)
      (by rw [Category.assoc]; exact hf)
  have hT' : RelativeRoot.IsFppfQuotient
      (SubgroupFunctor.range z) dT.projection := by
    refine ⟨dT.flat, dT.surjective, dT.locallyOfFinitePresentation, ?_⟩
    rw [dT.kernel_eq, dB.kernel_eq, ← SubgroupFunctor.comap_comp]
    exact SubgroupFunctor.comap_range_of_factor (t ≫ i) (kernelι q) z hf
  exact ⟨⟨dB, dT, rd, z, hf, hB, hT'⟩⟩

/-- Construct the sectioned adjoint Borel extension with its original
unipotent radical from a supplied maximal torus in the Borel. -/
def IsRelativeBorelSubgroup.adjointBorelExtensionData :
    RelativeLevi.AdjointBorelExtensionData i q a T t :=
  Classical.choice
    (adjointBorelExtensionData_nonempty hi hG q hq a ha T t hT htG hmax)

end OverRing
end Langlands.GroupScheme
