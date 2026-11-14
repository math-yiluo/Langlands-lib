import Langlands.GroupScheme.Rational.LeviRetraction
import Langlands.GroupScheme.ConjugacyBaseChange
import Langlands.GroupScheme.InnerAutomorphismHom
import Langlands.GroupScheme.Rational.MaximalTorusParameterExistenceProof

/-! # Algebraic reductions for conjugacy of relative Levi subgroups -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.RelativeLevi

variable {S : Scheme.{u}} {P L L' U : GroupScheme S}

/-- A point over a relative test scheme conjugates two represented subgroup
functors if the corresponding membership equivalence holds after every further
restriction. -/
def IsRangeConjugator (l : L ⟶ P) (l' : L' ⟶ P) {T : Over S}
    (g : T ⟶ P.X) : Prop :=
  ∀ (V : Over S) (a : V ⟶ T) (x : V ⟶ P.X),
    x ∈ (SubgroupFunctor.range l').carrier V ↔
      (a ≫ g)⁻¹ * x * (a ≫ g) ∈ (SubgroupFunctor.range l).carrier V

/-- An all-test conjugator remains a conjugator after restriction. -/
theorem IsRangeConjugator.comp {l : L ⟶ P} {l' : L' ⟶ P} {T V : Over S}
    {g : T ⟶ P.X} (hg : IsRangeConjugator l l' g) (a : V ⟶ T) :
    IsRangeConjugator l l' (a ≫ g) := by
  intro W b x
  simpa only [Category.assoc] using hg W (b ≫ a) x

/-- For a point over the base, the all-test predicate is exactly equality with
the range conjugated by its inner automorphism. -/
theorem isRangeConjugator_iff_range_eq (l : L ⟶ P) (l' : L' ⟶ P)
    (g : Over.mk (𝟙 S) ⟶ P.X) :
    IsRangeConjugator l l' g ↔ SubgroupFunctor.range l' =
      SubgroupFunctor.range (l ≫ (P.innerIso g).hom) := by
  constructor
  · intro hg
    ext V x
    rw [MaximalTorusParameterExistence.mem_range_comp_innerIso_iff]
    exact hg V (Over.homMk V.hom (by simp)) x
  · intro hg V a x
    have ha : a = Over.homMk V.hom (by simp) := by
      exact CategoryTheory.SemiCartesianMonoidalCategory.toUnit_unique a _
    rw [ha]
    change x ∈ (SubgroupFunctor.range l').carrier V ↔
      (P.constantPoint g V)⁻¹ * x * P.constantPoint g V ∈
        (SubgroupFunctor.range l).carrier V
    rw [hg, MaximalTorusParameterExistence.mem_range_comp_innerIso_iff]

/-- A conjugate of a complement by a point of the whole group is already a
conjugate by a point of its normal factor, over the original base. -/
theorem exists_radicalPoint_range_conjugate (l : L ⟶ P) (r : U ⟶ P)
    [IsIso (subgroupMultiplication l r)] (hn : (SubgroupFunctor.range r).IsNormal)
    (g : Over.mk (𝟙 S) ⟶ P.X) :
    ∃ n : Over.mk (𝟙 S) ⟶ U.X,
      SubgroupFunctor.range (l ≫ (P.innerIso g).hom) =
        SubgroupFunctor.range (l ≫ (P.innerIso (n ≫ r.hom.hom)).hom) := by
  let a := leviComponent l r g
  let v := g * (a ≫ l.hom.hom)⁻¹
  have hv : v ≫ (leviRetraction l r hn).hom.hom = 1 := by
    dsimp only [v]
    rw [MonObj.mul_comp, GrpObj.inv_comp, comp_leviRetraction,
      comp_leviRetraction, leviComponent_comp_levi]
    exact mul_inv_cancel a
  obtain ⟨n, hn⟩ := SubgroupFunctor.mem_range.mp
    ((comp_leviRetraction_eq_one_iff l r hn v).mp hv)
  have hg : g = (n ≫ r.hom.hom) * (a ≫ l.hom.hom) := by
    rw [hn]
    dsimp only [v]
    group
  refine ⟨n, ?_⟩
  calc
    SubgroupFunctor.range (l ≫ (P.innerIso g).hom) =
        SubgroupFunctor.range ((L.innerIso a).hom ≫
          (l ≫ (P.innerIso (n ≫ r.hom.hom)).hom)) := by
      congr 1
      rw [hg, innerIso_mul_hom, ← Category.assoc,
        ← innerIso_hom_comp, Category.assoc]
    _ = _ := SubgroupFunctor.range_iso_comp _ _

/-- An equality with any conjugate of the complement therefore gives an
equality with a conjugate under the specified normal factor. -/
theorem exists_radicalPoint_of_range_conjugate (l : L ⟶ P) (r : U ⟶ P)
    [IsIso (subgroupMultiplication l r)] (hn : (SubgroupFunctor.range r).IsNormal)
    (l' : L' ⟶ P) (g : Over.mk (𝟙 S) ⟶ P.X)
    (hg : SubgroupFunctor.range l' = SubgroupFunctor.range (l ≫ (P.innerIso g).hom)) :
    ∃ n : Over.mk (𝟙 S) ⟶ U.X,
      SubgroupFunctor.range l' =
        SubgroupFunctor.range (l ≫ (P.innerIso (n ≫ r.hom.hom)).hom) := by
  obtain ⟨n, hn⟩ := exists_radicalPoint_range_conjugate l r hn g
  exact ⟨n, hg.trans hn⟩

end Langlands.GroupScheme.RelativeLevi
