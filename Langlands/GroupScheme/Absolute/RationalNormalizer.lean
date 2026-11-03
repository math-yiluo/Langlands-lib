import Langlands.GroupScheme.Absolute.RationalSubgroupContainment
import Langlands.GroupScheme.Absolute.BorelTransport
import Langlands.GroupScheme.Rational.TorusNormalizer
import Langlands.AlgebraicGeometry.SmoothReducedProof

/-! # Normalizer membership detected on algebraically closed field points -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

namespace SubgroupFunctor

variable {S : Scheme.{u}} {G : GroupScheme S}

/-- Membership in the all-test normalizer at the base implies membership in
the abstract normalizer of the base points. -/
theorem normalizer_carrier_base_le (F : SubgroupFunctor G) :
    F.normalizer.carrier (Over.mk (𝟙 S)) ≤
      Subgroup.normalizer (F.carrier (Over.mk (𝟙 S)) :
        Set (Over.mk (𝟙 S) ⟶ G.X)) := by
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · exact fun hx => conj_mem_of_mem_normalizer hg hx
  · intro hx
    have h := ((F.normalizer.carrier _).inv_mem hg)
    have h' := conj_mem_of_mem_normalizer h hx
    simpa only [inv_inv, inv_mul_cancel_left, mul_inv_cancel_right, mul_assoc,
      inv_mul_cancel, mul_one] using h'

variable {k : Type u} [Field k] [IsAlgClosed k]
  {G H : GroupScheme (Spec (CommRingCat.of k))} {i : H ⟶ G}

/-- For a reduced finite-type source and closed target, a rational normalizing
point gives containment of the conjugated subgroup on every test scheme. -/
theorem range_comp_innerIso_le_of_algClosed_normalizer
    [IsReduced H.X.left] [LocallyOfFiniteType H.X.hom]
    (hi : IsClosedSubgroup i)
    {g : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X}
    (hg : g ∈ Subgroup.normalizer
      ((range i).carrier (Over.mk (𝟙 (Spec (CommRingCat.of k)))) :
        Set (Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X))) :
    range (i ≫ (G.innerIso g).hom) ≤ range i := by
  apply range_le_of_algClosed_points hi
  intro x hx
  obtain ⟨y, rfl⟩ := mem_range.mp hx
  have h := (Subgroup.mem_normalizer_iff.mp hg (y ≫ i.hom.hom)).mp ⟨y, rfl⟩
  change y ≫ (i ≫ (G.innerIso g).hom).hom.hom ∈ (range i).carrier _
  rwa [Grp.comp_hom_hom, ← Category.assoc, comp_innerIso_hom, constantPoint_self]

/-- For a reduced source locally of finite type and a closed embedding over
an algebraically closed field, rational normalizer membership is the
all-test normalizer condition. No smoothness of the normalizer is needed. -/
theorem normalizer_range_carrier_base_eq_algClosed_points
    [IsReduced H.X.left] [LocallyOfFiniteType H.X.hom]
    (hi : IsClosedSubgroup i) :
    (range i).normalizer.carrier (Over.mk (𝟙 (Spec (CommRingCat.of k)))) =
      Subgroup.normalizer
        ((range i).carrier (Over.mk (𝟙 (Spec (CommRingCat.of k)))) :
          Set (Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X)) := by
  apply le_antisymm (normalizer_carrier_base_le _)
  intro g hg V a x hx
  obtain ⟨t, rfl⟩ := mem_range.mp hx
  constructor
  · have h := range_comp_innerIso_le_of_algClosed_normalizer hi hg V ⟨t, rfl⟩
    change t ≫ (i ≫ (G.innerIso g).hom).hom.hom ∈ (range i).carrier V at h
    rw [Grp.comp_hom_hom, ← Category.assoc, comp_innerIso_hom] at h
    simpa only [comp_eq_constantPoint a g] using h
  · have h := range_comp_innerIso_le_of_algClosed_normalizer hi
      ((Subgroup.normalizer _).inv_mem hg) V ⟨t, rfl⟩
    change t ≫ (i ≫ (G.innerIso g⁻¹).hom).hom.hom ∈ (range i).carrier V at h
    rw [Grp.comp_hom_hom, ← Category.assoc, comp_innerIso_hom] at h
    simpa only [constantPoint_inv, inv_inv, comp_eq_constantPoint a g] using h

end SubgroupFunctor

variable {k : Type u} [Field k] [IsAlgClosed k]
  {G B : GroupScheme (Spec (CommRingCat.of k))} {i : B ⟶ G}

/-- The Borel automorphism induced by an abstract normalizing rational point. -/
def IsBorelSubgroup.conjugatingIsoOfMemNormalizer
    (hi : IsBorelSubgroup i)
    {g : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X}
    (hg : g ∈ Subgroup.normalizer
      ((SubgroupFunctor.range i).carrier (Over.mk (𝟙 (Spec (CommRingCat.of k)))) :
        Set (Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X))) :
    B ≅ B := by
  have : Smooth B.X.hom := hi.smooth
  have : IsReduced B.X.left :=
    Langlands.AlgebraicGeometry.SmoothReducedProof.isReduced_of_smooth_over_field
      k B.X.left B.X.hom
  have h := SubgroupFunctor.range_comp_innerIso_le_of_algClosed_normalizer
    hi.isClosedSubgroup hg
  have : IsClosedImmersion i.hom.hom.left := hi.isClosedSubgroup
  have hr : (SubgroupFunctor.range i).IsRepresentedBy i :=
    ⟨Over.mono_of_mono_left _, rfl⟩
  exact hi.conjugatingIsoOfFactor hi g (hr.factorHom _ h)
    (hr.factorHom_comp _ h)

/-- The induced Borel automorphism intertwines its embedding with conjugation. -/
theorem IsBorelSubgroup.conjugatingIsoOfMemNormalizer_hom_comp
    (hi : IsBorelSubgroup i)
    {g : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X}
    (hg : g ∈ Subgroup.normalizer
      ((SubgroupFunctor.range i).carrier (Over.mk (𝟙 (Spec (CommRingCat.of k)))) :
        Set (Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X))) :
    i ≫ (G.innerIso g).hom = (hi.conjugatingIsoOfMemNormalizer hg).hom ≫ i := by
  dsimp only [IsBorelSubgroup.conjugatingIsoOfMemNormalizer]
  exact hi.conjugatingIsoOfFactor_hom_comp hi g _ _

/-- An abstract normalizing point of a Borel's rational image induces an
actual automorphism of the Borel compatible with inner conjugation. -/
theorem IsBorelSubgroup.exists_conjugatingIso_of_mem_normalizer
    (hi : IsBorelSubgroup i)
    {g : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X}
    (hg : g ∈ Subgroup.normalizer
      ((SubgroupFunctor.range i).carrier (Over.mk (𝟙 (Spec (CommRingCat.of k)))) :
        Set (Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X))) :
    ∃ φ : B ≅ B, i ≫ (G.innerIso g).hom = φ.hom ≫ i :=
  ⟨hi.conjugatingIsoOfMemNormalizer hg,
    hi.conjugatingIsoOfMemNormalizer_hom_comp hg⟩

end Langlands.GroupScheme
