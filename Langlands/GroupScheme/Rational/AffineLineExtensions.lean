import Langlands.GroupScheme.Rational.AffineLineRigidity
import Langlands.GroupScheme.CentralIsogeny.Basic

/-! # Affine-line constancy under subgroups and extensions -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

variable {k : Type u} [Field k]
    {G H Q : GroupScheme (Spec (CommRingCat.of k))}

local notation "A" => AffineLine.scheme (Spec (CommRingCat.of k))
local notation "z" => AffineLine.zeroSection (Spec (CommRingCat.of k))

/-- Normalize an actual affine-line map by its value at the zero section. -/
def affineLineDifference (a : A ⟶ G.X) : A ⟶ G.X :=
  a / (toUnit A ≫ (z ≫ a))

/-- The normalized map takes the identity value at zero. -/
theorem zeroSection_comp_affineLineDifference (a : A ⟶ G.X) :
    z ≫ affineLineDifference a = 1 := by
  rw [affineLineDifference, GrpObj.comp_div]
  simp only [← Category.assoc, comp_toUnit, toUnit_unit, Category.id_comp, div_self']

/-- Normalization is compatible with every actual group homomorphism. -/
theorem affineLineDifference_comp (a : A ⟶ G.X) (q : G ⟶ Q) :
    affineLineDifference a ≫ q.hom.hom = affineLineDifference (a ≫ q.hom.hom) := by
  simp only [affineLineDifference, GrpObj.div_comp, Category.assoc]

/-- The normalized map is the identity exactly when the map is constant at zero. -/
theorem affineLineDifference_eq_one_iff (a : A ⟶ G.X) :
    affineLineDifference a = 1 ↔ a = toUnit A ≫ (z ≫ a) := by
  exact div_eq_one

namespace HasConstantAffineLineMaps

/-- A constant affine-line map has its canonical value at the zero section. -/
theorem eq_to_zeroSection (hG : HasConstantAffineLineMaps G) (a : A ⟶ G.X) :
    a = toUnit A ≫ (z ≫ a) := by
  obtain ⟨c, hc⟩ := hG a
  rw [hc]
  simp only [← Category.assoc, comp_toUnit, toUnit_unit, Category.id_comp]

/-- Every normalized affine-line map into a constant target is the identity. -/
theorem affineLineDifference_eq_one (hG : HasConstantAffineLineMaps G)
    (a : A ⟶ G.X) : affineLineDifference a = 1 :=
  (affineLineDifference_eq_one_iff a).mpr (hG.eq_to_zeroSection a)

/-- Constancy pulls back along any monic relative scheme morphism. -/
theorem of_mono (hG : HasConstantAffineLineMaps G) (j : H.X ⟶ G.X) [Mono j] :
    HasConstantAffineLineMaps H := by
  intro a
  refine ⟨z ≫ a, ?_⟩
  apply (cancel_mono j).mp
  simpa only [Category.assoc] using hG.eq_to_zeroSection (a ≫ j)

/-- Constancy passes to every actual closed subgroup. -/
theorem of_closed_subgroup (hG : HasConstantAffineLineMaps G) (j : H ⟶ G)
    (hj : IsClosedSubgroup j) : HasConstantAffineLineMaps H := by
  let : IsClosedImmersion j.hom.hom.left := hj
  let : Mono j.hom.hom := Over.mono_of_mono_left _
  exact hG.of_mono j.hom.hom

/-- Constancy in an actual kernel and its target implies constancy in the source.
More generally, the kernel may be covered on all relative tests by the range of
any supplied constant group. -/
theorem of_kernel_range_le (hQ : HasConstantAffineLineMaps Q) (q : G ⟶ Q)
    (j : H ⟶ G)
    (hker : SubgroupFunctor.range (kernelι q) ≤ SubgroupFunctor.range j)
    (hH : HasConstantAffineLineMaps H) : HasConstantAffineLineMaps G := by
  intro a
  have hd : affineLineDifference a ≫ q.hom.hom = 1 := by
    rw [affineLineDifference_comp]
    exact hQ.affineLineDifference_eq_one _
  obtain ⟨b, hb⟩ := SubgroupFunctor.mem_range.mp
    (hker A ((mem_range_kernelι_iff q _).mpr hd))
  have hd1 : affineLineDifference a = 1 := by
    calc
      affineLineDifference a = b ≫ j.hom.hom := hb.symm
      _ = (toUnit A ≫ (z ≫ b)) ≫ j.hom.hom :=
        congrArg (fun c => c ≫ j.hom.hom) (hH.eq_to_zeroSection b)
      _ = toUnit A ≫ (z ≫ affineLineDifference a) := by
        rw [Category.assoc, Category.assoc, hb]
      _ = 1 := by rw [zeroSection_comp_affineLineDifference, MonObj.comp_one]
  exact ⟨z ≫ a, (affineLineDifference_eq_one_iff a).mp hd1⟩

/-- Actual affine-line constancy is stable under extensions of group schemes. -/
theorem of_kernel (hQ : HasConstantAffineLineMaps Q) (q : G ⟶ Q)
    (hK : HasConstantAffineLineMaps (kernel q)) : HasConstantAffineLineMaps G :=
  hQ.of_kernel_range_le q (kernelι q) le_rfl hK

end HasConstantAffineLineMaps

end Langlands.GroupScheme
