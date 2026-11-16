import Langlands.GroupScheme.Rational.RootConeGroupBaseChange
import Langlands.GroupScheme.SplitExistence.ExtPoints

/-! # Descent of a smooth subgroup intersection from algebraic-closure points -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

section Points

variable {B B' : Scheme.{u}} (b : B' ⟶ B)
    {G H : GroupScheme B} (f : H ⟶ G)

/-- The base-point comparison commutes with a group homomorphism. -/
theorem baseChangeBasePointsEquiv_comp_hom
    (x : Over.mk (𝟙 B') ⟶ ((GroupScheme.baseChange b).obj H).X) :
    baseChangeBasePointsEquiv b G (x ≫ ((GroupScheme.baseChange b).map f).hom.hom) =
      baseChangeBasePointsEquiv b H x ≫ f.hom.hom := by
  apply Over.OverMorphism.ext
  rw [baseChangeBasePointsEquiv_left]
  change (x.left ≫ ((Over.pullback b).map f.hom.hom).left) ≫
    pullback.fst G.X.hom b = (baseChangeBasePointsEquiv b H x).left ≫ f.hom.hom.left
  rw [baseChangeBasePointsEquiv_left]
  simp only [Category.assoc, Over.pullback_map_left, pullback.lift_fst]

/-- The base-point comparison preserves membership in a represented subgroup. -/
theorem baseChangeBasePointsEquiv_mem_range
    (g : Over.mk (𝟙 B') ⟶ ((GroupScheme.baseChange b).obj G).X) :
    g ∈ (SubgroupFunctor.range ((GroupScheme.baseChange b).map f)).carrier
        (Over.mk (𝟙 B')) ↔
      baseChangeBasePointsEquiv b G g ∈ (SubgroupFunctor.range f).carrier (Over.mk b) := by
  rw [SubgroupFunctor.mem_range, SubgroupFunctor.mem_range]
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨baseChangeBasePointsEquiv b H x, (baseChangeBasePointsEquiv_comp_hom b f x).symm⟩
  · rintro ⟨x, hx⟩
    refine ⟨(baseChangeBasePointsEquiv b H).symm x, ?_⟩
    apply (baseChangeBasePointsEquiv b G).injective
    rw [baseChangeBasePointsEquiv_comp_hom, MulEquiv.apply_symm_apply, hx]

end Points

section Descent

variable {k K : Type u} [Field k] [Field K] [Algebra k K] [IsAlgClosed K]
    {G H₁ H₂ H₃ : GroupScheme (Spec (CommRingCat.of k))}
    {h₁ : H₁ ⟶ G} {h₂ : H₂ ⟶ G} {h₃ : H₃ ⟶ G}

/-- For a smooth intersection, containment in a closed subgroup can be checked
on the base points after one algebraically closed extension. -/
theorem subgroupIntersection_le_of_baseChangePoints
    [Smooth (subgroupIntersection h₁ h₂).X.hom] (hc₃ : IsClosedSubgroup h₃)
    (hpoints :
      (SubgroupFunctor.range ((GroupScheme.baseChange (algebraBaseMap k K)).map h₁)).carrier
          (Over.mk (𝟙 (Spec (CommRingCat.of K)))) ⊓
        (SubgroupFunctor.range ((GroupScheme.baseChange (algebraBaseMap k K)).map h₂)).carrier
          (Over.mk (𝟙 (Spec (CommRingCat.of K)))) ≤
        (SubgroupFunctor.range ((GroupScheme.baseChange (algebraBaseMap k K)).map h₃)).carrier
          (Over.mk (𝟙 (Spec (CommRingCat.of K))))) :
    SubgroupFunctor.range h₁ ⊓ SubgroupFunctor.range h₂ ≤ SubgroupFunctor.range h₃ := by
  let I := subgroupIntersection h₁ h₂
  let q := subgroupIntersectionHom h₁ h₂
  let b := algebraBaseMap k K
  have : GeometricallyReduced I.X.hom :=
    Langlands.AlgebraicGeometry.SmoothReducedProof.geometricallyReduced_of_smooth _
  have : IsReduced I.X.left :=
    GeometricallyReduced.isReduced_of_flat_of_isLocallyNoetherian I.X.hom
  rw [← range_subgroupIntersectionHom h₁ h₂]
  apply SplitExistence.range_le_of_extPoints K hc₃
  intro x
  let g := x ≫ q.hom.hom
  have hg : g ∈ (SubgroupFunctor.range h₁ ⊓ SubgroupFunctor.range h₂).carrier
      (SplitExistence.extPoint K) := by
    rw [← range_subgroupIntersectionHom h₁ h₂]
    exact ⟨x, rfl⟩
  let gK := (baseChangeBasePointsEquiv b G).symm g
  have hgK : baseChangeBasePointsEquiv b G gK = g :=
    (baseChangeBasePointsEquiv b G).apply_symm_apply g
  have hg₁ := (baseChangeBasePointsEquiv_mem_range b h₁ gK).mpr (hgK ▸ hg.1)
  have hg₂ := (baseChangeBasePointsEquiv_mem_range b h₂ gK).mpr (hgK ▸ hg.2)
  have hg₃ := (baseChangeBasePointsEquiv_mem_range b h₃ gK).mp (hpoints ⟨hg₁, hg₂⟩)
  rw [hgK] at hg₃
  exact hg₃

end Descent

end Langlands.GroupScheme
