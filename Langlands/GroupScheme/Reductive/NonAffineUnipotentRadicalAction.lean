import Langlands.GroupScheme.Reductive.NormalUnipotentRadicalInclusion
import Mathlib.AlgebraicGeometry.PullbackCarrier

/-! # Smooth automorphic actions on radicals without affine hypotheses -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
  CategoryTheory.CartesianMonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

variable {k : Type u} [Field k] [IsAlgClosed k]

/-- A morphism from a reduced locally finite-type scheme factors through a
closed subgroup if every rational point does. The morphism need not be a
group homomorphism, and neither scheme need be affine. -/
theorem IsClosedSubgroup.exists_overFactor_of_algClosed_points
    {G U : GroupScheme (Spec (CommRingCat.of k))} {i : U ⟶ G}
    (hi : IsClosedSubgroup i)
    {Z : Over (Spec (CommRingCat.of k))}
    [IsReduced Z.left] [LocallyOfFiniteType Z.hom] (f : Z ⟶ G.X)
    (h : ∀ z : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ Z,
      z ≫ f ∈ (SubgroupFunctor.range i).carrier
        (Over.mk (𝟙 (Spec (CommRingCat.of k))))) :
    ∃ a : Z ⟶ U.X, a ≫ i.hom.hom = f := by
  let g := i.hom.hom.left
  let p := pullback.fst f.left g
  have : IsClosedImmersion g := hi
  have : JacobsonSpace Z.left := LocallyOfFiniteType.jacobsonSpace Z.hom
  have hpclosed : IsClosed (Set.range p) := p.isClosedEmbedding.isClosed_range
  have hppts : closedPoints Z.left ⊆ Set.range p := by
    intro x hx
    let z : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ Z :=
      Over.homMk (pointOfClosedPoint Z.hom x hx)
        (pointOfClosedPoint_comp Z.hom x hx)
    obtain ⟨y, hy⟩ := SubgroupFunctor.mem_range.mp (h z)
    rw [Scheme.Pullback.range_fst]
    change ∃ t, g t = f.left x
    refine ⟨y.left (IsLocalRing.closedPoint k), ?_⟩
    have he := congrArg
      (fun a : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X =>
        a.left (IsLocalRing.closedPoint k)) hy
    change g (y.left (IsLocalRing.closedPoint k)) =
      f.left (pointOfClosedPoint Z.hom x hx (IsLocalRing.closedPoint k)) at he
    exact he.trans (congrArg f.left
      (pointOfClosedPoint_apply Z.hom x hx (IsLocalRing.closedPoint k)))
  have hprange : Set.range p = Set.univ := by
    apply Set.Subset.antisymm (Set.subset_univ _)
    rw [← closure_closedPoints (X := Z.left)]
    exact closure_minimal hppts hpclosed
  have : Surjective p := ⟨Set.range_eq_univ.mp hprange⟩
  have : IsIso p := isIso_of_isClosedImmersion_of_surjective p
  let a := inv p ≫ pullback.snd f.left g
  have ha : a ≫ g = f.left := by
    dsimp [a]
    rw [Category.assoc, ← pullback.condition, ← Category.assoc,
      IsIso.inv_hom_id, Category.id_comp]
  refine ⟨Over.homMk a (by
    rw [← Over.w i.hom.hom, ← Category.assoc, ha]
    exact Over.w f), ?_⟩
  exact Over.OverMorphism.ext ha

variable {H G U : GroupScheme (Spec (CommRingCat.of k))}
  [Smooth H.X.hom] {i : U ⟶ G}

/-- A smooth group acting by automorphisms preserves a represented radical
on every scheme test, without affine or connected ambient hypotheses. -/
theorem IsUnipotentRadical.isStable_of_smooth
    (hi : IsUnipotentRadical i) (a : AutomorphicAction H G) :
    a.IsStable (SubgroupFunctor.range i) := by
  have : Smooth U.X.hom := hi.smooth
  have : Smooth (H.X ⊗ U.X).hom := smooth_tensor H.X U.X inferInstance hi.smooth
  have : IsReduced (H.X ⊗ U.X).left :=
    Langlands.AlgebraicGeometry.SmoothReducedProof.isReduced_of_smooth_over_field
      k (H.X ⊗ U.X).left (H.X ⊗ U.X).hom
  let F : H.X ⊗ U.X ⟶ G.X :=
    a.act (fst H.X U.X) (snd H.X U.X ≫ i.hom.hom)
  obtain ⟨d, hd⟩ := hi.isClosedSubgroup.exists_overFactor_of_algClosed_points F (by
    intro z
    let h := z ≫ fst H.X U.X
    let x := z ≫ snd H.X U.X
    have hu : toUnit (Over.mk (𝟙 (Spec (CommRingCat.of k)))) = 𝟙 _ :=
      toUnit_unique _ _
    have heq : SubgroupFunctor.range (i ≫ (a.sectionIso h).hom) =
        SubgroupFunctor.range i := (hi.comp_iso (a.sectionIso h)).range_eq hi
    rw [← heq]
    apply SubgroupFunctor.mem_range.mpr
    refine ⟨x, ?_⟩
    rw [Grp.comp_hom_hom, ← Category.assoc, a.comp_sectionIso_hom, hu,
      Category.id_comp]
    change a.act h (x ≫ i.hom.hom) =
      z ≫ a.act (fst H.X U.X) (snd H.X U.X ≫ i.hom.hom)
    rw [a.naturality, ← Category.assoc])
  intro T h g hg
  obtain ⟨x, rfl⟩ := SubgroupFunctor.mem_range.mp hg
  refine SubgroupFunctor.mem_range.mpr ⟨lift h x ≫ d, ?_⟩
  rw [Category.assoc, hd]
  change lift h x ≫ a.act (fst H.X U.X) (snd H.X U.X ≫ i.hom.hom) = _
  rw [a.naturality, lift_fst, lift_snd_assoc]

/-- The actual induced action on a supplied radical under a smooth acting
group, allowing a nonaffine ambient group. -/
def IsUnipotentRadical.actionOfSmooth
    (hi : IsUnipotentRadical i) (a : AutomorphicAction H G) :
    AutomorphicAction H U := by
  have : IsClosedImmersion i.hom.hom.left := hi.isClosedSubgroup
  have : Mono i.hom.hom := Over.mono_of_mono_left _
  exact a.onRepresentedSubgroup i ⟨inferInstance, rfl⟩ (hi.isStable_of_smooth a)

/-- The induced action preserves the actual inclusion. -/
theorem IsUnipotentRadical.actionOfSmooth_isEquivariant
    (hi : IsUnipotentRadical i) (a : AutomorphicAction H G)
    {T : Over (Spec (CommRingCat.of k))} (h : T ⟶ H.X) (x : T ⟶ U.X) :
    (hi.actionOfSmooth a).act h x ≫ i.hom.hom =
      a.act h (x ≫ i.hom.hom) :=
  a.onRepresentedSubgroup_act_comp i _ (hi.isStable_of_smooth a) h x

end Langlands.GroupScheme
