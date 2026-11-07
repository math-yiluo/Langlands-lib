import Langlands.GroupScheme.Absolute.RationalSubgroupContainment
import Langlands.GroupScheme.Rational.LocalFieldDensity
import Langlands.AlgebraicGeometry.SmoothReducedProof

/-! # Closed subgroup containment from dense rational points -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Langlands.AlgebraicGeometry.PointTopology
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.SubgroupFunctor

variable {k : Type u} [Field k]
  {G H K : GroupScheme (Spec (CommRingCat.of k))}
  {i : H ⟶ G} {j : K ⟶ G}

/-- A reduced source with dense rational points detects containment in a
closed subgroup on rational points. -/
theorem range_le_of_dense_rationalPoints [IsReduced H.X.left]
    (hH : HasDenseRationalPoints k H.X) (hj : IsClosedSubgroup j)
    (h : (range i).carrier (Over.mk (𝟙 (Spec (CommRingCat.of k)))) ≤
      (range j).carrier (Over.mk (𝟙 (Spec (CommRingCat.of k))))) :
    range i ≤ range j := by
  let f := i.hom.hom.left
  let g := j.hom.hom.left
  let p := pullback.fst f g
  have : IsClosedImmersion g := hj
  have hpclosed : IsClosed (Set.range p) := p.isClosedEmbedding.isClosed_range
  have hpdense : Dense (Set.range p) := by
    apply hH.mono
    intro x hx
    obtain ⟨a, z, rfl⟩ := Set.mem_iUnion.mp hx
    obtain ⟨b, hb⟩ := h ⟨a, rfl⟩
    rw [Scheme.Pullback.range_fst]
    change ∃ y, g y = f (a.left z)
    refine ⟨b.left z, ?_⟩
    exact congrArg
      (fun q : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X => q.left z) hb
  have hprange : Set.range p = Set.univ :=
    hpclosed.closure_eq.symm.trans hpdense.closure_eq
  have : Surjective p := ⟨Set.range_eq_univ.mp hprange⟩
  have : IsIso p := isIso_of_isClosedImmersion_of_surjective p
  let a := inv p ≫ pullback.snd f g
  have ha : a ≫ g = f := by
    dsimp [a]
    rw [Category.assoc, ← pullback.condition, ← Category.assoc,
      IsIso.inv_hom_id, Category.id_comp]
  let b : H.X ⟶ K.X := Over.homMk a (by
    rw [← Over.w j.hom.hom, ← Category.assoc, ha]
    exact Over.w i.hom.hom)
  have hb : b ≫ j.hom.hom = i.hom.hom := by
    apply Over.OverMorphism.ext
    exact ha
  rintro U x ⟨y, rfl⟩
  change U ⟶ H.X at y
  refine ⟨y ≫ b, ?_⟩
  change (y ≫ b) ≫ j.hom.hom = y ≫ i.hom.hom
  rw [Category.assoc, hb]

/-- The containment criterion for a smooth connected affine source over an
actual nonarchimedean local field. -/
theorem range_le_of_localField_points
    [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    [Smooth H.X.hom] [IsAffineHom H.X.hom] [ConnectedSpace H.X.left]
    (hj : IsClosedSubgroup j)
    (h : (range i).carrier (Over.mk (𝟙 (Spec (CommRingCat.of k)))) ≤
      (range j).carrier (Over.mk (𝟙 (Spec (CommRingCat.of k))))) :
    range i ≤ range j := by
  have : IsReduced H.X.left :=
    Langlands.AlgebraicGeometry.SmoothReducedProof.isReduced_of_smooth_over_field k _ H.X.hom
  exact range_le_of_dense_rationalPoints
    (hasDenseRationalPoints_of_localField k H) hj h

end Langlands.GroupScheme.SubgroupFunctor
