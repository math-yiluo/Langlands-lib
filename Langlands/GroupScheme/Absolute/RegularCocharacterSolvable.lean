import Langlands.GroupScheme.Absolute.AlgebraicClosurePoint
import Langlands.GroupScheme.Dynamic.UnipotentSolvable
import Langlands.GroupScheme.Absolute.Borel
import Langlands.AbelianScheme.KernelBaseChange

/-! # Solvability of closed subgroups representing dynamic parabolic subgroups -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

variable {k : Type u} [Field k] {G : GroupScheme (Spec (CommRingCat.of k))}

/-- A group scheme over `k` is solvable when its group of points over `Spec k̄ → Spec k` is
solvable. -/
theorem isSolvableGroupScheme_of_isSolvable_points {H : GroupScheme (Spec (CommRingCat.of k))}
    (h : Group.IsSolvable (algebraicClosurePoint k ⟶ H.X)) : IsSolvableGroupScheme H :=
  Group.isSolvable_of_isSolvable_injective
    (f := (baseChangePointsEquiv (toAlgebraicClosure k) H
      (Over.mk (𝟙 (Spec (CommRingCat.of (AlgebraicClosure k)))))).toMonoidHom)
    (baseChangePointsEquiv (toAlgebraicClosure k) _ _).injective

/-- If `i : B ⟶ G` represents a subgroup functor `F`, the points of `B` over `U` embed into
the points of `F` over `U`. -/
theorem isSolvable_points_of_isRepresentedBy {B : GroupScheme (Spec (CommRingCat.of k))}
    {F : SubgroupFunctor G} {i : B ⟶ G} (hi : F.IsRepresentedBy i)
    (U : Over (Spec (CommRingCat.of k))) (hF : Group.IsSolvable (F.carrier U)) :
    Group.IsSolvable (U ⟶ B.X) := by
  have hmem : ∀ x : U ⟶ B.X, x ≫ i.hom.hom ∈ F.carrier U := by
    intro x
    rw [← hi.2]
    exact ⟨x, rfl⟩
  let f : (U ⟶ B.X) →* F.carrier U :=
    { toFun := fun x => ⟨x ≫ i.hom.hom, hmem x⟩
      map_one' := Subtype.ext (MonObj.one_comp _)
      map_mul' := fun x y => Subtype.ext (MonObj.mul_comp _ _ _) }
  have hinj : Function.Injective f := by
    intro x y hxy
    have := hi.1
    exact (cancel_mono i.hom.hom).1 (congrArg Subtype.val hxy)
  exact Group.isSolvable_of_isSolvable_injective hinj

/-- Let `G` be affine and locally of finite type over a field `k`, let `χ` be a cocharacter of
`G`, and let `i : B ⟶ G` represent `P(χ)`. If the points of `Z(χ)` over `Spec k̄` form a
solvable group, then `B` is solvable. -/
theorem isSolvableGroupScheme_of_isRepresentedBy_parabolic [IsAffineHom G.X.hom]
    [LocallyOfFiniteType G.X.hom] (χ : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ G)
    {B : GroupScheme (Spec (CommRingCat.of k))} {i : B ⟶ G}
    (hi : (Dynamic.parabolic χ).IsRepresentedBy i)
    (hZ : Group.IsSolvable ((Dynamic.centralizer χ).carrier (algebraicClosurePoint k))) :
    IsSolvableGroupScheme B := by
  apply isSolvableGroupScheme_of_isSolvable_points
  apply isSolvable_points_of_isRepresentedBy hi
  have := Dynamic.isSolvable_unipotent_carrier χ (algebraicClosurePoint k)
  exact Dynamic.isSolvable_parabolic_carrier χ (algebraicClosurePoint k)

/-- If the dynamic centralizer of `χ` lies in the range of a homomorphism from a commutative
group scheme, its points form a commutative, hence solvable, group. -/
theorem isSolvable_centralizer_carrier_of_le_range {T : CommGroupScheme (Spec (CommRingCat.of k))}
    (χ : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ G) {j : T.toGrp ⟶ G}
    (h : Dynamic.centralizer χ ≤ SubgroupFunctor.range j) (U : Over (Spec (CommRingCat.of k))) :
    Group.IsSolvable ((Dynamic.centralizer χ).carrier U) := by
  apply Group.isSolvable_of_comm
  intro x y
  obtain ⟨a, ha⟩ := SubgroupFunctor.mem_range.1 (h U x.2)
  obtain ⟨b, hb⟩ := SubgroupFunctor.mem_range.1 (h U y.2)
  apply Subtype.ext
  change (x : U ⟶ G.X) * y = y * x
  rw [← ha, ← hb, ← MonObj.mul_comp, ← MonObj.mul_comp]
  congr 1
  exact mul_comm (G := U ⟶ T.X) a b

/-- With `G`, `χ` and `i : B ⟶ G` as in `isSolvableGroupScheme_of_isRepresentedBy_parabolic`,
`B` is solvable as soon as `Z(χ)` lies in the range of a homomorphism from a commutative group
scheme. -/
theorem isSolvableGroupScheme_of_isRepresentedBy_parabolic_of_le_range [IsAffineHom G.X.hom]
    [LocallyOfFiniteType G.X.hom] (χ : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ G)
    {T : CommGroupScheme (Spec (CommRingCat.of k))} {j : T.toGrp ⟶ G}
    (h : Dynamic.centralizer χ ≤ SubgroupFunctor.range j)
    {B : GroupScheme (Spec (CommRingCat.of k))} {i : B ⟶ G}
    (hi : (Dynamic.parabolic χ).IsRepresentedBy i) :
    IsSolvableGroupScheme B :=
  isSolvableGroupScheme_of_isRepresentedBy_parabolic χ hi
    (isSolvable_centralizer_carrier_of_le_range χ h _)

end Langlands.GroupScheme
