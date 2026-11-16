import Langlands.GroupScheme.Rational.SemigroupIntersectionGeometry
import Langlands.GroupScheme.Rational.SemigroupRealizationProof

/-! # Smooth intersections and their exact ambient Lie images -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.RelativeRoot

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {k : Type u} [Field k]
    {S : CommGroupScheme (Spec (CommRingCat.of k))}
    {G : GroupScheme (Spec (CommRingCat.of k))}
    [IsAffineHom G.X.hom] [Smooth G.X.hom]
    (b : AutomorphicAction S.toGrp G) (hS : IsSplitTorus S.toGrp)
    (A B : AddSubsemigroup (characterLattice S))

include hS

/-- Any supplied closed presentations of two semigroup functors have a smooth
scheme-theoretic intersection. -/
theorem smooth_subgroupIntersection_semigroup
    {H K : GroupScheme (Spec (CommRingCat.of k))} [Smooth H.X.hom]
    (j : H ⟶ G) (l : K ⟶ G)
    (hj : (semigroupSubgroup b A).IsRepresentedBy j)
    (hl : (semigroupSubgroup b B).IsRepresentedBy l)
    (hjc : IsClosedSubgroup j) (hlc : IsClosedSubgroup l) :
    Smooth (subgroupIntersection j l).X.hom := by
  let : IsAffineHom H.X.hom := hjc.isAffineHom
  let c := b.onRepresentedSubgroup j hj (semigroupSubgroup_isStable b A)
  have heq : ∀ (T : Over (Spec (CommRingCat.of k))) (s : T ⟶ S.X) (x : T ⟶ H.X),
      c.act s x ≫ j.hom.hom = b.act s (x ≫ j.hom.hom) :=
    fun _ s x => b.onRepresentedSubgroup_act_comp j hj
      (semigroupSubgroup_isStable b A) s x
  exact smooth_semigroup_comap_representative b c j heq semigroupRealization hS hjc B
    (subgroupIntersectionFst j l) (hl.comap_subgroupIntersectionFst hlc j)
    (isClosedSubgroup_subgroupIntersectionFst j hlc)

/-- The full all-test intersection of two semigroup subgroups is smooth and closed. -/
theorem isSmoothClosed_semigroupSubgroup_inf :
    IsSmoothClosed (semigroupSubgroup b A ⊓ semigroupSubgroup b B) := by
  obtain ⟨H, j, hj, hjc, hjs, _⟩ := isSmoothConnectedClosed_semigroupSubgroup b hS A
  obtain ⟨K, l, hl, hlc, _, _⟩ := isSmoothConnectedClosed_semigroupSubgroup b hS B
  let : Smooth H.X.hom := hjs
  have hrep : (semigroupSubgroup b A ⊓ semigroupSubgroup b B).IsRepresentedBy
      (subgroupIntersectionHom j l) := by
    rw [← hj.2, ← hl.2]
    exact isRepresentedBy_subgroupIntersectionHom hjc hlc
  exact ⟨subgroupIntersection j l, subgroupIntersectionHom j l, hrep,
    isClosedSubgroup_subgroupIntersectionHom hjc hlc,
    smooth_subgroupIntersection_semigroup b hS A B j l hj hl hjc hlc⟩

/-- The Lie image of the actual intersection consists exactly of the ambient
weight spaces selected by both semigroups. -/
theorem hasLieImage_semigroupSubgroup_inf :
    HasLieImage (semigroupSubgroup b A ⊓ semigroupSubgroup b B)
      (semigroupWeightSpan b (A ⊓ B)) := by
  let F := semigroupSubgroup b A ⊓ semigroupSubgroup b B
  obtain ⟨H, j, hj, hjc, hjs⟩ := isSmoothClosed_semigroupSubgroup_inf b hS A B
  let : IsAffineHom H.X.hom := hjc.isAffineHom
  let : Smooth H.X.hom := hjs
  have hstable : b.IsStable F := by
    intro T s x hx
    exact ⟨semigroupSubgroup_isStable b A T s x hx.1,
      semigroupSubgroup_isStable b B T s x hx.2⟩
  have hLieA := hasLieImage_semigroupSubgroup b hS A
  have hLieB := hasLieImage_semigroupSubgroup b hS B
  have hsupportA : actionWeightSupport b F ⊆ A :=
    actionWeightSupport_subset_of_tangentSubmodule_le b hS A F
      ((tangentSubmodule_mono
        (show F ≤ semigroupSubgroup b A from fun _ _ hx => hx.1)).trans_eq
        ((hasLieImage_iff_tangentSubmodule_eq _ _).mp hLieA))
  have hsupportB : actionWeightSupport b F ⊆ B :=
    actionWeightSupport_subset_of_tangentSubmodule_le b hS B F
      ((tangentSubmodule_mono
        (show F ≤ semigroupSubgroup b B from fun _ _ hx => hx.2)).trans_eq
        ((hasLieImage_iff_tangentSubmodule_eq _ _).mp hLieB))
  apply (hasLieImage_iff_tangentSubmodule_eq _ _).mpr
  apply le_antisymm
  · exact (actionWeightSupport_subset_iff_tangentSubmodule_le b hS j hj hstable
      (A ⊓ B)).mp (fun a ha => ⟨hsupportA ha, hsupportB ha⟩)
  · rw [← (hasLieImage_iff_tangentSubmodule_eq _ _).mp
      (hasLieImage_semigroupSubgroup b hS (A ⊓ B))]
    apply tangentSubmodule_mono
    intro T x hx
    exact ⟨semigroupSubgroup_mono b inf_le_left T hx,
      semigroupSubgroup_mono b inf_le_right T hx⟩

end Langlands.GroupScheme.RelativeRoot
