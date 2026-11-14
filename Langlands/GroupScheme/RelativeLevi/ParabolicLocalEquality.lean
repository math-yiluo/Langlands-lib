import Langlands.GroupScheme.RelativeLevi.ParabolicLieContainmentStatement
import Langlands.GroupScheme.SubgroupFunctor.FpqcDescent

/-! # Local equality of relative parabolics from one residue fibre -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

namespace SubgroupFunctor

variable {S S' S'' : Scheme.{u}} {G : GroupScheme S}

/-- A containment after restriction remains true on every further restriction,
with the composite base map written directly. -/
theorem baseChange_le_of_factorization
    (b : S' ⟶ S) (c : S'' ⟶ S') (d : S'' ⟶ S) (h : c ≫ b = d)
    {F F' : SubgroupFunctor G}
    (hle : F.baseChange b ≤ F'.baseChange b) :
    F.baseChange d ≤ F'.baseChange d := by
  intro U x hx
  let U' : Over S' := Over.mk (U.hom ≫ c)
  let e : (Over.map b).obj U' ≅ (Over.map d).obj U :=
    Over.isoMk (Iso.refl _) (by
      change (𝟙 U.left) ≫ (U.hom ≫ d) = (U.hom ≫ c) ≫ b
      rw [Category.id_comp, Category.assoc, h])
  let z := baseChangePointsEquiv d G U x
  let y := (baseChangePointsEquiv b G U').symm (e.hom ≫ z)
  have hy : y ∈ (F.baseChange b).carrier U' := by
    change baseChangePointsEquiv b G U' y ∈ F.carrier _
    dsimp only [y]
    rw [MulEquiv.apply_symm_apply]
    exact F.comp_mem e.hom hx
  have hy' := hle U' hy
  change baseChangePointsEquiv b G U' y ∈ F'.carrier _ at hy'
  dsimp only [y] at hy'
  rw [MulEquiv.apply_symm_apply] at hy'
  change z ∈ F'.carrier _
  exact by
    simpa only [Iso.inv_hom_id_assoc] using F'.comp_mem e.inv hy'

end SubgroupFunctor

variable {S : Scheme.{u}} {G P Q : GroupScheme S}
  (i : P ⟶ G) (j : Q ⟶ G) (T : CommGroupScheme S) (t : T.toGrp ⟶ G)

/-- Assuming Lie-containment spreading, equality of two parabolic residue
fibres containing a common maximal torus spreads to an open neighbourhood. -/
theorem relativeParabolic_exists_open_range_eq_of_residueFiber_range_eq
    (hLie : RelativeParabolicLieContainmentStatement.{u})
    (hG : IsReductive G)
    (hi : IsRelativeParabolicSubgroup i) (hj : IsRelativeParabolicSubgroup j)
    (hT : RelativeTorus.IsTorus T.toGrp) (ht : IsClosedSubgroup t)
    (hmax : IsFibrewiseMaximalTorus t)
    (hti : SubgroupFunctor.range t ≤ SubgroupFunctor.range i)
    (htj : SubgroupFunctor.range t ≤ SubgroupFunctor.range j)
    (s : S)
    (hfib : SubgroupFunctor.range (RelativeLevi.residueFiberHom i s) =
      SubgroupFunctor.range (RelativeLevi.residueFiberHom j s)) :
    ∃ V : S.Opens, s ∈ V ∧
      SubgroupFunctor.range ((baseChange V.ι).map i) =
        SubgroupFunctor.range ((baseChange V.ι).map j) := by
  have := hG.isAffineHom
  obtain ⟨V, hsV, hV⟩ :=
    hLie S G Q P j i T t s hG hj hi hT ht hmax htj hti (by rw [hfib])
  obtain ⟨W, hsW, hW⟩ :=
    hLie S G P Q i j T t s hG hi hj hT ht hmax hti htj (by rw [hfib])
  refine ⟨V ⊓ W, ⟨hsV, hsW⟩, le_antisymm ?_ ?_⟩
  · rw [SubgroupFunctor.range_baseChangeHom, SubgroupFunctor.range_baseChangeHom] at hV ⊢
    exact SubgroupFunctor.baseChange_le_of_factorization V.ι
      (S.homOfLE inf_le_left) (V ⊓ W).ι (by simp) hV
  · rw [SubgroupFunctor.range_baseChangeHom, SubgroupFunctor.range_baseChangeHom] at hW ⊢
    exact SubgroupFunctor.baseChange_le_of_factorization W.ι
      (S.homOfLE inf_le_right) (V ⊓ W).ι (by simp) hW

/-- Choose an open neighbourhood with the proved equality of restricted
parabolics. The Lie-containment premise remains explicit. -/
def relativeParabolicLocalEquality
    (hLie : RelativeParabolicLieContainmentStatement.{u})
    (hG : IsReductive G)
    (hi : IsRelativeParabolicSubgroup i) (hj : IsRelativeParabolicSubgroup j)
    (hT : RelativeTorus.IsTorus T.toGrp) (ht : IsClosedSubgroup t)
    (hmax : IsFibrewiseMaximalTorus t)
    (hti : SubgroupFunctor.range t ≤ SubgroupFunctor.range i)
    (htj : SubgroupFunctor.range t ≤ SubgroupFunctor.range j)
    (s : S)
    (hfib : SubgroupFunctor.range (RelativeLevi.residueFiberHom i s) =
      SubgroupFunctor.range (RelativeLevi.residueFiberHom j s)) :
    {V : S.Opens // s ∈ V ∧
      SubgroupFunctor.range ((baseChange V.ι).map i) =
        SubgroupFunctor.range ((baseChange V.ι).map j)} :=
  let h := relativeParabolic_exists_open_range_eq_of_residueFiber_range_eq
    i j T t hLie hG hi hj hT ht hmax hti htj s hfib
  ⟨h.choose, h.choose_spec⟩

end Langlands.GroupScheme
