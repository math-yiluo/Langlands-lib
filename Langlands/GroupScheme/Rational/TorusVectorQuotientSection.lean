import Langlands.GroupScheme.Rational.TorusVectorRetractionDescent

/-! # Complementary sections from retractions of commutative extensions -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.TorusVectorExtension

open RelativeRoot

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

section Retraction

variable {S : Scheme.{u}} {E Z Q : GroupScheme S}
    [IsCommMonObj E.X] (z : Z ⟶ E) [Mono z.hom.hom]
    (p : E ⟶ Q) [QuasiCompact p.hom.hom.left]
    (hq : IsFppfQuotient (SubgroupFunctor.range z) p)
    (r : E ⟶ Z) (hr : z ≫ r = 𝟙 Z)

include hq hr

/-- The complementary endomorphism to a retraction descends to a quotient section. -/
theorem exists_section_of_retraction :
    ∃ s : Q ⟶ E, p ≫ s = 𝟙 E / (r ≫ z) ∧ s ≫ p = 𝟙 Q := by
  let : Flat p.hom.hom.left := hq.1
  let : Surjective p.hom.hom.left := hq.2.1
  have hz : (SubgroupFunctor.range z).IsRepresentedBy z := ⟨inferInstance, rfl⟩
  let e := hq.kernelIso hz
  have he : e.hom ≫ kernelι p = z := hq.kernelIso_hom_comp hz
  have hkill : kernelι p ≫ (𝟙 E / (r ≫ z)) = 0 := by
    apply (cancel_epi e.hom).mp
    rw [comp_zero, ← Category.assoc, he]
    change z ≫ (𝟙 E / (r ≫ z)) = 1
    rw [GrpObj.comp_div, Category.comp_id, ← Category.assoc, hr,
      Category.id_comp, div_self']
  let s := FpqcHomDescent.hom p (𝟙 E / (r ≫ z)) hkill
  have hs : p ≫ s = 𝟙 E / (r ≫ z) := FpqcHomDescent.fac p _ hkill
  refine ⟨s, hs, ?_⟩
  apply FppfQuotientComparison.hom_ext hq
  rw [← Category.assoc, hs, Category.comp_id]
  have hzp : z ≫ p = 0 := by
    rw [← he, Category.assoc, FppfQuotientComparison.kernel_comp hq hq, comp_zero]
  have hzp' : z.hom.hom ≫ p.hom.hom = 1 :=
    congrArg (fun a => a.hom.hom) hzp
  apply Grp.hom_ext
  change (𝟙 E.X / (r.hom.hom ≫ z.hom.hom)) ≫ p.hom.hom = p.hom.hom
  rw [GrpObj.div_comp, Category.id_comp, Category.assoc, hzp',
    MonObj.comp_one, div_one]

/-- A chosen actual quotient section complementary to the specified retraction. -/
def sectionOfRetraction : Q ⟶ E :=
  Classical.choose (exists_section_of_retraction z p hq r hr)

@[reassoc]
theorem projection_sectionOfRetraction :
    p ≫ sectionOfRetraction z p hq r hr = 𝟙 E / (r ≫ z) :=
  (Classical.choose_spec (exists_section_of_retraction z p hq r hr)).1

@[reassoc]
theorem sectionOfRetraction_projection :
    sectionOfRetraction z p hq r hr ≫ p = 𝟙 Q :=
  (Classical.choose_spec (exists_section_of_retraction z p hq r hr)).2

end Retraction

/-- A commutative affine central-torus extension of a vector group splits over its field. -/
theorem exists_split_of_vector_quotient
    {k : Type u} [Field k]
    {E Z Q : GroupScheme (Spec (CommRingCat.of k))}
    [IsAffineHom E.X.hom] [IsCommMonObj E.X] {n : ℕ}
    (hZ : IsTorus Z) (hV : IsVectorGroupOfDimension Q n)
    (z : Z ⟶ E) (hz : IsClosedSubgroup z) (hc : IsCentral z)
    (p : E ⟶ Q) (hq : IsFppfQuotient (SubgroupFunctor.range z) p) :
    ∃ (r : E ⟶ Z) (s : Q ⟶ E),
      z ≫ r = 𝟙 Z ∧ s ≫ p = 𝟙 Q ∧ p ≫ s = 𝟙 E / (r ≫ z) := by
  have : IsClosedImmersion z.hom.hom.left := hz
  have : Mono z.hom.hom := Over.mono_of_mono_left _
  have : IsAffineHom Q.X.hom := hV.isAffineHom
  have : IsAffine E.X.left := isAffine_of_isAffineHom E.X.hom
  have : IsAffine Q.X.left := isAffine_of_isAffineHom Q.X.hom
  obtain ⟨r, hr⟩ := exists_retraction_of_vector_quotient hZ hV z hz hc p hq
  obtain ⟨s, hs, hsp⟩ := exists_section_of_retraction z p hq r hr
  exact ⟨r, s, hr, hsp, hs⟩

end Langlands.GroupScheme.TorusVectorExtension
