import Langlands.GroupScheme.RepresentedSubgroup
import Langlands.GroupScheme.Rational.WeightSemigroup
import Langlands.GroupScheme.Rational.RootSubgroupStructureStatement
import Langlands.GroupScheme.Lie.SubgroupEqualityStatement
import Langlands.GroupScheme.Lie.SubgroupEqualityProof
import Langlands.GroupScheme.Rational.SemigroupClosure
import Langlands.GroupScheme.Rational.SemigroupWeightSupport

/-! # Included represented subgroups with the same actual Lie image -/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

namespace SubgroupFunctor.IsRepresentedBy

variable {B : Scheme.{u}} {G H H' : GroupScheme B}
    {F F' : SubgroupFunctor G} {j : H ⟶ G} {j' : H' ⟶ G}

/-- The canonical morphism between representatives of included all-test
subgroup functors. -/
def homOfLe (hj : F.IsRepresentedBy j) (hj' : F'.IsRepresentedBy j')
    (h : F ≤ F') : H ⟶ H' :=
  hj.lift hj' (fun T => Subgroup.inclusion (h T)) (fun _ _ => rfl)

/-- The induced morphism commutes with the two ambient inclusions. -/
theorem homOfLe_comp (hj : F.IsRepresentedBy j) (hj' : F'.IsRepresentedBy j')
    (h : F ≤ F') : hj.homOfLe hj' h ≫ j' = j :=
  hj.lift_comp_eq hj' _ (fun _ _ => rfl) (fun _ _ => rfl)

/-- On every test the induced morphism lifts the given ambient inclusion. -/
theorem homOfLe_comp_apply (hj : F.IsRepresentedBy j) (hj' : F'.IsRepresentedBy j')
    (h : F ≤ F') {T : Over B} (x : T ⟶ H.X) :
    (x ≫ (hj.homOfLe hj' h).hom.hom) ≫ j'.hom.hom = x ≫ j.hom.hom := by
  rw [Category.assoc, ← Grp.comp_hom_hom, homOfLe_comp]

/-- The morphism between closed representatives is itself a closed immersion. -/
theorem homOfLe_isClosedSubgroup (hj : F.IsRepresentedBy j)
    (hj' : F'.IsRepresentedBy j') (h : F ≤ F')
    (hc : IsClosedSubgroup j) (hc' : IsClosedSubgroup j') :
    IsClosedSubgroup (hj.homOfLe hj' h) := by
  have : IsClosedImmersion j'.hom.hom.left := hc'
  have hcomp : (hj.homOfLe hj' h).hom.hom.left ≫ j'.hom.hom.left =
      j.hom.hom.left :=
    congrArg (fun q : H ⟶ G => q.hom.hom.left) (homOfLe_comp hj hj' h)
  have : IsClosedImmersion
      ((hj.homOfLe hj' h).hom.hom.left ≫ j'.hom.hom.left) := hcomp.symm ▸ hc
  exact IsClosedImmersion.of_comp_isClosedImmersion _ j'.hom.hom.left

end SubgroupFunctor.IsRepresentedBy

namespace RelativeRoot

variable {k : Type u} [Field k]
    {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The general full-Lie closed-subgroup theorem implies equality of included
smooth connected closed all-test subgroups with the same actual Lie image.
The structural theorem remains an explicit premise. -/
theorem eq_of_le_of_hasLieImage
    (hEquality : LieSubgroupEqualityStatement.{u})
    {F F' : SubgroupFunctor G}
    (hF : IsSmoothConnectedClosed F) (hF' : IsSmoothConnectedClosed F')
    (h : F ≤ F') {W : Submodule k (Additive (lieKernel G k))}
    (hLie : HasLieImage F W) (hLie' : HasLieImage F' W) : F = F' := by
  obtain ⟨H, j, hj, hc, hs, hconn⟩ := hF
  obtain ⟨H', j', hj', hc', hs', hconn'⟩ := hF'
  have : Smooth H.X.hom := hs
  have : Smooth H'.X.hom := hs'
  have : ConnectedSpace H'.X.left := hconn'
  have : IsClosedImmersion j'.hom.hom.left := hc'
  have : IsAffineHom H'.X.hom := by
    rw [← j'.hom.hom.w]
    infer_instance
  have : Mono j.hom.hom := hj.1
  have : Mono j'.hom.hom := hj'.1
  let f : H ⟶ H' := hj.homOfLe hj' h
  have hf : f ≫ j' = j := hj.homOfLe_comp hj' h
  have hfc : IsClosedSubgroup f := hj.homOfLe_isClosedSubgroup hj' h hc hc'
  have hfull : ∀ X : lieKernel H' k,
      ∃ Y : lieKernel H k, Y.val ≫ f.hom.hom = X.val := by
    intro X
    let XG : lieKernel G k := ⟨X.val ≫ j'.hom.hom, by
      change Lie.reduction G (X.val ≫ j'.hom.hom) = 1
      dsimp only [Lie.reduction, Lie.affineMap_apply]
      rw [← Category.assoc]
      change Lie.reduction H' X.val ≫ j'.hom.hom = 1
      rw [X.property, MonObj.one_comp]⟩
    have hXG : XG.val ∈ F'.carrier _ := by
      rw [← hj'.2]
      exact SubgroupFunctor.mem_range.mpr ⟨X.val, rfl⟩
    have hXW : Additive.ofMul XG ∈ W := (hLie' _).mp hXG
    have hXF := (hLie (Additive.ofMul XG)).mpr hXW
    rw [← hj.2] at hXF
    obtain ⟨y, hy⟩ := SubgroupFunctor.mem_range.mp hXF
    have hy0 : Lie.reduction H y = 1 := by
      apply (cancel_mono j.hom.hom).mp
      rw [MonObj.one_comp]
      dsimp only [Lie.reduction, Lie.affineMap_apply]
      rw [Category.assoc, hy]
      exact XG.property
    refine ⟨⟨y, hy0⟩, ?_⟩
    apply (cancel_mono j'.hom.hom).mp
    rw [Category.assoc, ← Grp.comp_hom_hom, hf]
    exact hy
  have hrange : SubgroupFunctor.range f = ⊤ :=
    hEquality k H' H f hfc hfull
  apply le_antisymm h
  intro T x hx
  rw [← hj'.2] at hx
  obtain ⟨z, rfl⟩ := SubgroupFunctor.mem_range.mp hx
  have hz : z ∈ (SubgroupFunctor.range f).carrier T := by
    rw [hrange]
    exact Subgroup.mem_top _
  obtain ⟨y, hy⟩ := SubgroupFunctor.mem_range.mp hz
  rw [← hy, Category.assoc, ← Grp.comp_hom_hom, hf, ← hj.2]
  exact SubgroupFunctor.mem_range.mpr ⟨y, rfl⟩

/-- Included smooth connected closed subgroup functors with the same actual Lie
image are equal, by the published full-Lie closed-subgroup theorem. -/
theorem IsSmoothConnectedClosed.eq_of_le_of_hasLieImage
    {F F' : SubgroupFunctor G}
    (hF : IsSmoothConnectedClosed F) (hF' : IsSmoothConnectedClosed F')
    (h : F ≤ F') {W : Submodule k (Additive (lieKernel G k))}
    (hLie : HasLieImage F W) (hLie' : HasLieImage F' W) : F = F' :=
  _root_.Langlands.GroupScheme.RelativeRoot.eq_of_le_of_hasLieImage
    lieSubgroupEquality hF hF' h hLie hLie'

section Semigroup

variable [LocallyOfFiniteType G.X.hom]
    {S : CommGroupScheme (Spec (CommRingCat.of k))}
    (b : AutomorphicAction S.toGrp G) (hS : IsSplitTorus S.toGrp)
    (A : AddSubsemigroup (characterLattice S))

include hS

/-- A smooth connected invariant closed subgroup whose tangent lies in the
selected weight span is an admissible generator, hence lies in the actual
generated semigroup subgroup on every test. -/
theorem le_semigroupSubgroup_of_tangentSubmodule_le
    {F : SubgroupFunctor G} (hF : IsSmoothConnectedClosed F)
    (hstable : b.IsStable F)
    (hLie : tangentSubmodule F ≤ semigroupWeightSpan b A) :
    F ≤ semigroupSubgroup b A :=
  generator_le_semigroupSubgroup b A F
    ⟨hF, hstable, actionWeightSupport_subset_of_tangentSubmodule_le b hS A F hLie⟩

/-- Exact Lie image supplies the support bound needed for the generator
inclusion; no realization of the generated functor is assumed. -/
theorem le_semigroupSubgroup_of_hasLieImage
    {F : SubgroupFunctor G} (hF : IsSmoothConnectedClosed F)
    (hstable : b.IsStable F)
    (hLie : HasLieImage F (semigroupWeightSpan b A)) :
    F ≤ semigroupSubgroup b A :=
  le_semigroupSubgroup_of_tangentSubmodule_le b hS A hF hstable
    (le_of_eq ((hasLieImage_iff_tangentSubmodule_eq F _).mp hLie))

/-- Exact Lie image of the generated subgroup suffices for its full maximality
equivalence. Its own smooth representability is not needed for this step. -/
theorem semigroupSubgroup_maximality_of_hasLieImage
    (hLie : HasLieImage (semigroupSubgroup b A) (semigroupWeightSpan b A))
    (F : SubgroupFunctor G) (hF : IsSmoothConnectedClosed F) (hstable : b.IsStable F) :
    actionWeightSupport b F ⊆ A ↔ F ≤ semigroupSubgroup b A :=
  semigroupSubgroup_maximality_of_support b A
    (actionWeightSupport_subset_of_tangentSubmodule_le b hS A _
      (le_of_eq ((hasLieImage_iff_tangentSubmodule_eq _ _).mp hLie)))
    F hF hstable

/-- Once the generated subgroup has a smooth connected closed realization and
the exact Lie image, any smooth connected invariant closed subgroup with that
Lie image equals it. The two geometric properties of the generated subgroup
remain explicit premises. -/
theorem eq_semigroupSubgroup_of_hasLieImage
    (hgenerated : IsSmoothConnectedClosed (semigroupSubgroup b A))
    (hgeneratedLie : HasLieImage (semigroupSubgroup b A) (semigroupWeightSpan b A))
    {F : SubgroupFunctor G} (hF : IsSmoothConnectedClosed F)
    (hstable : b.IsStable F) (hLie : HasLieImage F (semigroupWeightSpan b A)) :
    F = semigroupSubgroup b A :=
  hF.eq_of_le_of_hasLieImage hgenerated
    (le_semigroupSubgroup_of_hasLieImage b hS A hF hstable hLie) hLie hgeneratedLie

end Semigroup

end RelativeRoot
end Langlands.GroupScheme
