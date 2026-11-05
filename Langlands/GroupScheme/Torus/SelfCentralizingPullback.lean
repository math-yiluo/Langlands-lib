import Langlands.GroupScheme.SubgroupIntersection
import Langlands.GroupScheme.Dynamic.Functoriality
import Langlands.GroupScheme.Rational.LeviFactorization
import Langlands.GroupScheme.Torus.MaximalTransport

/-! # Full pullbacks identified by a self-centralizing subgroup -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

section Base

variable {S : Scheme.{u}} {C H : GroupScheme S}
    {A T : CommGroupScheme S}
    (p : C ⟶ H) (i : T.toGrp ⟶ H) (j : A.toGrp ⟶ C)
    (f : A.toGrp ⟶ T.toGrp)
    (hcomm : j ≫ p = f ≫ i)
    (hself : torusCentralizer j = SubgroupFunctor.range j)
    (hcent : SubgroupFunctor.range (subgroupIntersectionFst p i) ≤ torusCentralizer j)

include hcomm hself hcent

/-- A subgroup mapping into a commutative target subgroup is its full preimage
if the preimage centralizes it and its whole centralizer is itself. -/
theorem range_subgroupIntersectionFst_eq_of_selfCentralizing :
    SubgroupFunctor.range (subgroupIntersectionFst p i) = SubgroupFunctor.range j := by
  apply le_antisymm
  · simpa only [hself] using hcent
  · let l : A.toGrp ⟶ subgroupIntersection p i := pullback.lift j f hcomm
    have hl : l ≫ subgroupIntersectionFst p i = j := pullback.lift_fst _ _ _
    intro U x hx
    obtain ⟨a, rfl⟩ := SubgroupFunctor.mem_range.mp hx
    refine SubgroupFunctor.mem_range.mpr ⟨a ≫ l.hom.hom, ?_⟩
    rw [Category.assoc, ← Grp.comp_hom_hom, hl]

/-- The actual full group-scheme pullback is the supplied self-centralizing
subgroup, compatibly with both inclusions into the source. -/
def selfCentralizingSubgroupIntersectionIso
    (hi : IsClosedSubgroup i) (hj : IsClosedSubgroup j) :
    subgroupIntersection p i ≅ A.toGrp := by
  have : IsClosedImmersion (subgroupIntersectionFst p i).hom.hom.left :=
    isClosedSubgroup_subgroupIntersectionFst p hi
  have : IsClosedImmersion j.hom.hom.left := hj
  exact SubgroupFunctor.IsRepresentedBy.isoOfIsRepresentedBy
    (F := SubgroupFunctor.range j)
    ⟨Over.mono_of_mono_left _,
      range_subgroupIntersectionFst_eq_of_selfCentralizing p i j f hcomm hself hcent⟩
    ⟨Over.mono_of_mono_left _, rfl⟩

@[reassoc]
theorem selfCentralizingSubgroupIntersectionIso_hom_comp
    (hi : IsClosedSubgroup i) (hj : IsClosedSubgroup j) :
    (selfCentralizingSubgroupIntersectionIso p i j f hcomm hself hcent hi hj).hom ≫ j =
      subgroupIntersectionFst p i := by
  exact SubgroupFunctor.IsRepresentedBy.isoOfIsRepresentedBy_hom_comp _ _

@[reassoc]
theorem selfCentralizingSubgroupIntersectionIso_inv_comp
    (hi : IsClosedSubgroup i) (hj : IsClosedSubgroup j) :
    (selfCentralizingSubgroupIntersectionIso p i j f hcomm hself hcent hi hj).inv ≫
      subgroupIntersectionFst p i = j := by
  rw [← selfCentralizingSubgroupIntersectionIso_hom_comp p i j f hcomm hself hcent hi hj,
    Iso.inv_hom_id_assoc]

end Base

section Reflection

variable {S : Scheme.{u}} {C D H : GroupScheme S}
    {A T : CommGroupScheme S}
    (π : C ⟶ D) (d : D ⟶ H) (i : T.toGrp ⟶ H)
    (j : A.toGrp ⟶ C) (f : A.toGrp ⟶ T.toGrp)

/-- Reflection of the centralizer through the first map, and monicity of the
second map, force the full pullback of a commutative subgroup to centralize `j`. -/
theorem range_subgroupIntersectionFst_le_torusCentralizer_of_reflection
    [Mono d.hom.hom]
    (hcomm : j ≫ π ≫ d = f ≫ i)
    (hreflect : (torusCentralizer (j ≫ π)).comap π = torusCentralizer j) :
    SubgroupFunctor.range (subgroupIntersectionFst (π ≫ d) i) ≤ torusCentralizer j := by
  intro U x hx
  rw [← hreflect]
  change x ≫ π.hom.hom ∈ (torusCentralizer (j ≫ π)).carrier U
  obtain ⟨y, hy⟩ := SubgroupFunctor.mem_range.mp hx
  have hxy : x ≫ (π ≫ d).hom.hom =
      (y ≫ (subgroupIntersectionSnd (π ≫ d) i).hom.hom) ≫ i.hom.hom := by
    rw [← hy, Category.assoc, ← Grp.comp_hom_hom,
      subgroupIntersection_condition, Grp.comp_hom_hom, ← Category.assoc]
  intro V a t
  apply (commute_iff_eq _ _).mpr
  apply (cancel_mono d.hom.hom).mp
  have hc : Commute
      (a ≫ (y ≫ (subgroupIntersectionSnd (π ≫ d) i).hom.hom))
      (t ≫ f.hom.hom) := Commute.all _ _
  have hh := congrArg (fun z : V ⟶ T.X => z ≫ i.hom.hom) hc.eq
  simpa only [MonObj.mul_comp, Category.assoc, ← Grp.comp_hom_hom, hcomm, hxy] using hh

end Reflection

section Field

variable {k : Type u} [Field k]
    {C D H : GroupScheme (Spec (CommRingCat.of k))}
    {A T : CommGroupScheme (Spec (CommRingCat.of k))}

/-- A closed self-centralizing source torus identifies the entire pullback
of a commutative target subgroup, once centralizer reflection is supplied. -/
theorem isTorus_subgroupIntersection_of_selfCentralizing_of_reflection
    (π : C ⟶ D) (d : D ⟶ H) [Mono d.hom.hom]
    (i : T.toGrp ⟶ H) (j : A.toGrp ⟶ C) (f : A.toGrp ⟶ T.toGrp)
    (hA : IsTorus A.toGrp) (hi : IsClosedSubgroup i) (hj : IsClosedSubgroup j)
    (hcomm : j ≫ π ≫ d = f ≫ i)
    (hself : torusCentralizer j = SubgroupFunctor.range j)
    (hreflect : (torusCentralizer (j ≫ π)).comap π = torusCentralizer j) :
    IsTorus (subgroupIntersection (π ≫ d) i) := by
  have hcent := range_subgroupIntersectionFst_le_torusCentralizer_of_reflection
    π d i j f hcomm hreflect
  exact IsTorus.of_iso
    (selfCentralizingSubgroupIntersectionIso (π ≫ d) i j f
      (by simpa only [Category.assoc] using hcomm) hself hcent hi hj) hA

end Field

end Langlands.GroupScheme
