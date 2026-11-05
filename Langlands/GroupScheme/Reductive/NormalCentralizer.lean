import Langlands.GroupScheme.FieldFixedSubgroupRepresentabilityProof

/-! # The full centralizer of a normal subgroup -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

section Base

variable {S : Scheme.{u}} {H G A : GroupScheme S}

/-- Fixed points of conjugation commute with the acting subgroup after every
change of test scheme. -/
theorem mem_conjugation_fixedSubgroup_iff (j : H ⟶ G)
    {T : Over S} (g : T ⟶ G.X) :
    g ∈ (AutomorphicAction.conjugation j).fixedSubgroup.carrier T ↔
      ∀ (T' : Over S) (b : T' ⟶ T) (h : T' ⟶ H.X),
        Commute (h ≫ j.hom.hom) (b ≫ g) := by
  constructor
  · intro hg T' b h
    have e := hg T' b h
    rw [AutomorphicAction.conjugation_act] at e
    exact (mul_inv_eq_iff_eq_mul.mp e)
  · intro hg T' b h
    rw [AutomorphicAction.conjugation_act, (hg T' b h).eq, mul_inv_cancel_right]

/-- The full centralizer of a normal subgroup is normal on every test scheme. -/
theorem conjugation_fixedSubgroup_isNormal (j : H ⟶ G)
    (hj : (SubgroupFunctor.range j).IsNormal) :
    (AutomorphicAction.conjugation j).fixedSubgroup.IsNormal := by
  intro T g x _ hx
  rw [mem_conjugation_fixedSubgroup_iff] at hx ⊢
  intro T' b h
  have hn := hj T' (b ≫ g)⁻¹ (h ≫ j.hom.hom) (Subgroup.mem_top _)
    (SubgroupFunctor.mem_range.mpr ⟨h, rfl⟩)
  obtain ⟨h', hh'⟩ := SubgroupFunctor.mem_range.mp hn
  have hc := hx T' b h'
  rw [hh'] at hc
  have he := congrArg (fun z => (b ≫ g) * z * (b ≫ g)⁻¹) hc.eq
  change (h ≫ j.hom.hom) * (b ≫ (g * x * g⁻¹)) =
    (b ≫ (g * x * g⁻¹)) * (h ≫ j.hom.hom)
  rw [MonObj.comp_mul, MonObj.comp_mul, GrpObj.comp_inv]
  simpa only [inv_inv, mul_assoc, mul_inv_cancel_left, inv_mul_cancel_left,
    mul_inv_cancel_right, inv_mul_cancel_right, mul_inv_cancel, mul_one] using he

/-- An actual subgroup map factors through the full centralizer precisely when
its image commutes with the acting subgroup on all tests. -/
theorem range_le_conjugation_fixedSubgroup_iff (j : H ⟶ G) (a : A ⟶ G) :
    SubgroupFunctor.range a ≤ (AutomorphicAction.conjugation j).fixedSubgroup ↔
      ∀ (T : Over S) (h : T ⟶ H.X) (x : T ⟶ A.X),
        Commute (h ≫ j.hom.hom) (x ≫ a.hom.hom) := by
  constructor
  · intro ha T h x
    have hx := ha T (SubgroupFunctor.mem_range.mpr ⟨x, rfl⟩)
    simpa only [Category.id_comp] using
      (mem_conjugation_fixedSubgroup_iff j _).mp hx T (𝟙 T) h
  · intro ha T x hx
    obtain ⟨y, rfl⟩ := SubgroupFunctor.mem_range.mp hx
    rw [mem_conjugation_fixedSubgroup_iff]
    intro T' b h
    simpa only [Category.assoc] using ha T' h (b ≫ y)

end Base

section Field

variable {k : Type u} [Field k]
variable {H G : GroupScheme (Spec (CommRingCat.of k))}

/-- A normal affine subgroup has a closed normal full centralizer. The
representative and the commutation comparison retain all test schemes. -/
theorem exists_closed_normal_centralizer [IsAffineHom H.X.hom]
    (j : H ⟶ G) (hj : (SubgroupFunctor.range j).IsNormal) :
    ∃ (K : GroupScheme (Spec (CommRingCat.of k))) (i : K ⟶ G),
      IsClosedSubgroup i ∧
      SubgroupFunctor.range i = (AutomorphicAction.conjugation j).fixedSubgroup ∧
      (SubgroupFunctor.range i).IsNormal ∧
      (∀ (T : Over (Spec (CommRingCat.of k))) (h : T ⟶ H.X) (x : T ⟶ K.X),
        Commute (h ≫ j.hom.hom) (x ≫ i.hom.hom)) := by
  obtain ⟨K, i, hi, hiClosed⟩ := fieldFixedSubgroupRepresentability k H G
    inferInstance (AutomorphicAction.conjugation j)
  refine ⟨K, i, hiClosed, hi.2, ?_, ?_⟩
  · rw [hi.2]
    exact conjugation_fixedSubgroup_isNormal j hj
  · apply (range_le_conjugation_fixedSubgroup_iff j i).mp
    rw [hi.2]

/-- An actual representative of the closed normal full centralizer, retaining
its comparison with the all-test fixed subgroup. -/
structure ClosedNormalCentralizer (j : H ⟶ G) where
  /-- The group scheme representing the full centralizer. -/
  group : GroupScheme (Spec (CommRingCat.of k))
  /-- Its inclusion into the ambient group. -/
  inclusion : group ⟶ G
  isClosedSubgroup : IsClosedSubgroup inclusion
  range_eq : SubgroupFunctor.range inclusion =
    (AutomorphicAction.conjugation j).fixedSubgroup
  isNormal : (SubgroupFunctor.range inclusion).IsNormal
  commute : ∀ (T : Over (Spec (CommRingCat.of k))) (h : T ⟶ H.X) (x : T ⟶ group.X),
    Commute (h ≫ j.hom.hom) (x ≫ inclusion.hom.hom)

/-- Choose the full centralizer representative supplied by fixed-subgroup
representability, with its proved normality and all-test comparisons. -/
def closedNormalCentralizer [IsAffineHom H.X.hom]
    (j : H ⟶ G) (hj : (SubgroupFunctor.range j).IsNormal) :
    ClosedNormalCentralizer j :=
  Classical.choice (by
    obtain ⟨K, i, hi, hr, hn, hc⟩ := exists_closed_normal_centralizer j hj
    exact ⟨⟨K, i, hi, hr, hn, hc⟩⟩)

end Field

end Langlands.GroupScheme
