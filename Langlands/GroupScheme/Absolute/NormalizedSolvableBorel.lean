import Langlands.GroupScheme.Absolute.NormalUnipotentBorelContainmentProof
import Langlands.GroupScheme.Absolute.BorelContaining
import Langlands.GroupScheme.Torus.HeightExistence
import Mathlib.Algebra.Group.Subgroup.Pointwise

/-! # A common Borel for a normalized pair of connected solvable subgroups -/

noncomputable section
universe u
open CategoryTheory AlgebraicGeometry Opposite
open scoped CategoryTheory.MonObj Pointwise

namespace Langlands.GroupScheme

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

/-- Solvability of a join only requires normalization by the second factor. -/
theorem isSolvable_sup_of_le_normalizer {G : Type*} [Group G] (N K : Subgroup G)
    (hNK : K ≤ Subgroup.normalizer N) [Group.IsSolvable N] [Group.IsSolvable K] :
    Group.IsSolvable ↥(N ⊔ K) := by
  let S := N ⊔ K
  have hN : N ≤ S := le_sup_left
  have hK : K ≤ S := le_sup_right
  have : (N.subgroupOf S).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hN).2 (sup_le N.le_normalizer hNK)
  have : Group.IsSolvable (N.subgroupOf S) :=
    Group.isSolvable_of_isSolvable_injective
      (f := (Subgroup.subgroupOfEquivOfLe hN).toMonoidHom)
      (Subgroup.subgroupOfEquivOfLe hN).injective
  have : Group.IsSolvable (K.subgroupOf S) :=
    Group.isSolvable_of_isSolvable_injective
      (f := (Subgroup.subgroupOfEquivOfLe hK).toMonoidHom)
      (Subgroup.subgroupOfEquivOfLe hK).injective
  have hs := isSolvable_sup_of_normal (N.subgroupOf S) (K.subgroupOf S)
  rw [← Subgroup.subgroupOf_sup hN hK, Subgroup.subgroupOf_self] at hs
  exact Group.isSolvable_of_surjective
    (f := (⊤ : Subgroup S).subtype) (fun x => ⟨⟨x, trivial⟩, rfl⟩)

/-- A normalized join has the expected two-factor decomposition. -/
theorem mem_sup_of_le_normalizer {G : Type*} [Group G] {N K : Subgroup G}
    (hNK : K ≤ Subgroup.normalizer N) {x : G} (hx : x ∈ N ⊔ K) :
    ∃ n ∈ N, ∃ z ∈ K, n * z = x := by
  have he := Subgroup.coe_mul_of_right_le_normalizer_left N K hNK
  change x ∈ ((N ⊔ K : Subgroup G) : Set G) at hx
  rw [he] at hx
  exact hx

section SolvablePair

variable {k : Type u} [Field k] [IsAlgClosed k]
    {G U T : GroupScheme (Spec (CommRingCat.of k))}
    [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
    [Smooth U.X.hom] [ConnectedSpace U.X.left]
    [Smooth T.X.hom] [ConnectedSpace T.X.left]
    (i : U ⟶ G) (j : T ⟶ G)
    (hU : IsSolvableGroupScheme U) (hT : IsSolvableGroupScheme T)
    (hn : (SubgroupFunctor.range i).IsNormalizedBy (SubgroupFunctor.range j))

include hU hT hn in
/-- The smooth connected solvable envelope of a normalized pair lies in a Borel,
with actual factor maps for both of the supplied inclusions. -/
theorem exists_isBorelSubgroup_containing_normalized_solvable :
    ∃ (B : GroupScheme (Spec (CommRingCat.of k))) (b : B ⟶ G),
      IsBorelSubgroup b ∧
        (∃ f : U ⟶ B, f ≫ b = i) ∧ (∃ g : T ⟶ B, g ≫ b = j) := by
  have : IsReduced U.X.left :=
    Langlands.AlgebraicGeometry.SmoothReducedProof.isReduced_of_smooth_over_field
      k U.X.left U.X.hom
  have : IsReduced T.X.left :=
    Langlands.AlgebraicGeometry.SmoothReducedProof.isReduced_of_smooth_over_field
      k T.X.left T.X.hom
  let N := (SubgroupFunctor.range i).carrier (Over.mk (𝟙 (Spec (CommRingCat.of k))))
  let K := (SubgroupFunctor.range j).carrier (Over.mk (𝟙 (Spec (CommRingCat.of k))))
  have hNK : K ≤ Subgroup.normalizer N := by
    rw [Subgroup.le_normalizer_iff]
    intro t ht n hn'
    exact hn _ t n ht hn'
  have hNsolv : Group.IsSolvable N := by
    have : Group.IsSolvable ((yonedaGrp.obj U).obj
        (op (Over.mk (𝟙 (Spec (CommRingCat.of k)))))) :=
      (isSolvableGroupScheme_iff_isSolvable_points U).1 hU
    exact @Group.isSolvable_of_surjective _ _ _ _ _
      (MonoidHom.rangeRestrict_surjective ((yonedaGrp.map i).app (op _)).hom) this
  have hKsolv : Group.IsSolvable K := by
    have : Group.IsSolvable ((yonedaGrp.obj T).obj
        (op (Over.mk (𝟙 (Spec (CommRingCat.of k)))))) :=
      (isSolvableGroupScheme_iff_isSolvable_points T).1 hT
    exact @Group.isSolvable_of_surjective _ _ _ _ _
      (MonoidHom.rangeRestrict_surjective ((yonedaGrp.map j).app (op _)).hom) this
  have hΓsolv : Group.IsSolvable ↥(N ⊔ K) := isSolvable_sup_of_le_normalizer N K hNK
  obtain ⟨Z, ζ, hζ, hZs, hZrange⟩ := rationalPointClosureSubgroup k G (N ⊔ K)
  have : Smooth Z.X.hom := hZs
  have : IsClosedImmersion ζ.hom.hom.left := hζ
  have hmem : ∀ x, x ∈ pointClosureSubgroup G (N ⊔ K) →
      x ∈ (SubgroupFunctor.range ζ).carrier
        (Over.mk (𝟙 (Spec (CommRingCat.of k)))) :=
    fun x hx => mem_range_of_location_mem hζ (by rw [hZrange]; exact hx)
  have hmem' : ∀ y : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ Z.X,
      y ≫ ζ.hom.hom ∈ pointClosureSubgroup G (N ⊔ K) := by
    intro y
    rw [mem_pointClosureSubgroup, ← hZrange]
    exact ⟨_, rfl⟩
  have hZsolv : IsSolvableGroupScheme Z := by
    rw [isSolvableGroupScheme_iff_isSolvable_points]
    have := isSolvable_pointClosureSubgroup (H := G) (N ⊔ K)
    have : Mono ζ.hom.hom := Over.mono_of_mono_left _
    let f₀ : (Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ Z.X) →*
        (Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X) :=
      ((yonedaGrp.map ζ).app (op _)).hom
    exact Group.isSolvable_of_isSolvable_injective (f := f₀.codRestrict _ hmem')
      (fun y y' h => (cancel_mono ζ.hom.hom).1 (congrArg Subtype.val h))
  -- The closure is connected because the two connected factors generate it.
  have hZc : ConnectedSpace Z.X.left := by
    choose φ hφ using exists_comp_eq_mul_left (H := G)
    let A := Set.range i.hom.hom.left
    let B : N → Set G.X.left := fun a => Set.range (j.hom.hom ≫ φ a).left
    have hA : _root_.IsPreconnected A := isPreconnected_range i.hom.hom.left.continuous
    have hB : ∀ a, _root_.IsPreconnected (B a) :=
      fun a => isPreconnected_range (j.hom.hom ≫ φ a).left.continuous
    have hAB : ∀ a : N,
        (a : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X).left
          (IsLocalRing.closedPoint k) ∈ A ∩ B a := by
      intro a
      obtain ⟨y, hy⟩ := SubgroupFunctor.mem_range.1 a.2
      have h1 : (1 : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ T.X) ≫
          j.hom.hom ≫ φ a = a := by
        rw [← Category.assoc, hφ, MonObj.one_comp, mul_one]
      refine ⟨⟨y.left (IsLocalRing.closedPoint k), ?_⟩,
        ⟨(1 : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ T.X).left
          (IsLocalRing.closedPoint k), ?_⟩⟩
      · change (y ≫ i.hom.hom).left (IsLocalRing.closedPoint k) = _
        rw [hy]
      · change ((1 : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ T.X) ≫
            j.hom.hom ≫ φ a).left (IsLocalRing.closedPoint k) = _
        rw [h1]
    obtain ⟨u₀⟩ : Nonempty U.X.left := inferInstance
    have hY : _root_.IsPreconnected (⋃ a : N, B a ∪ A) :=
      isPreconnected_iUnion
        ⟨i.hom.hom.left u₀, Set.mem_iInter.2 fun _ => Or.inr ⟨u₀, rfl⟩⟩
        fun a => IsPreconnected.union _ (hAB a).2 (hAB a).1 (hB a) hA
    have hYsub : (⋃ a : N, B a ∪ A) ⊆ closure (rationalPointImage G
        ((N ⊔ K : Subgroup _) :
          Set (Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X))) := by
      refine Set.iUnion_subset fun a => Set.union_subset ?_ ?_
      · refine range_left_subset_closure _ fun y => ?_
        rw [← Category.assoc, hφ]
        exact (N ⊔ K).mul_mem (Subgroup.mem_sup_left a.2)
          (Subgroup.mem_sup_right (SubgroupFunctor.mem_range.2 ⟨y, rfl⟩))
      · exact range_left_subset_closure _ fun y =>
          Subgroup.mem_sup_left (SubgroupFunctor.mem_range.2 ⟨y, rfl⟩)
    have hsubY : rationalPointImage G ((N ⊔ K : Subgroup _) :
        Set (Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X)) ⊆
          ⋃ a : N, B a ∪ A := by
      rintro _ ⟨x, hx, rfl⟩
      obtain ⟨n, hn', z, hz, rfl⟩ := mem_sup_of_le_normalizer hNK hx
      obtain ⟨y, rfl⟩ := SubgroupFunctor.mem_range.1 hz
      refine Set.mem_iUnion.2
        ⟨⟨n, hn'⟩, Or.inl ⟨y.left (IsLocalRing.closedPoint k), ?_⟩⟩
      change (y ≫ j.hom.hom ≫ φ n).left (IsLocalRing.closedPoint k) = _
      rw [← Category.assoc, hφ]
    have hcl' := hY.subset_closure hYsub (closure_mono hsubY)
    rw [← hZrange, ← Set.image_univ,
      ζ.hom.hom.left.isClosedEmbedding.isInducing.isPreconnected_image] at hcl'
    have : PreconnectedSpace Z.X.left := ⟨hcl'⟩
    exact ⟨⟨(1 : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ Z.X).left
      (IsLocalRing.closedPoint k)⟩⟩
  obtain ⟨f, hf⟩ := SubgroupFunctor.exists_factor_of_algClosed_points (i := i) hζ
    (fun x hx => hmem x (le_pointClosureSubgroup _ (Subgroup.mem_sup_left hx)))
  obtain ⟨g, hg⟩ := SubgroupFunctor.exists_factor_of_algClosed_points (i := j) hζ
    (fun x hx => hmem x (le_pointClosureSubgroup _ (Subgroup.mem_sup_right hx)))
  obtain ⟨B, b, z, hb, hz⟩ :=
    BorelExistence.exists_isBorelSubgroup_containing ζ ⟨hζ, hZs, hZc, hZsolv⟩
  refine ⟨B, b, hb, ⟨f ≫ z, ?_⟩, ⟨g ≫ z, ?_⟩⟩
  · rw [Category.assoc, hz, hf]
  · rw [Category.assoc, hz, hg]

/-- An actual common Borel with compatible factor maps for both subgroup sources. -/
structure CommonBorelData where
  subgroup : GroupScheme (Spec (CommRingCat.of k))
  inclusion : subgroup ⟶ G
  isBorelSubgroup : IsBorelSubgroup inclusion
  leftFactor : U ⟶ subgroup
  rightFactor : T ⟶ subgroup
  left_comp : leftFactor ≫ inclusion = i
  right_comp : rightFactor ≫ inclusion = j

include hU hT hn in
/-- Choose the common Borel of a normalized pair of smooth connected solvable subgroups. -/
def commonBorelOfNormalizedSolvable : CommonBorelData i j :=
  Classical.choice (by
    obtain ⟨B, b, hb, ⟨f, hf⟩, ⟨g, hg⟩⟩ :=
      exists_isBorelSubgroup_containing_normalized_solvable i j hU hT hn
    exact ⟨⟨B, b, hb, f, g, hf, hg⟩⟩)

end SolvablePair

/-- A maximal torus and a smooth connected unipotent subgroup which it normalizes
belong to a common Borel pair with the original torus morphism unchanged. -/
theorem exists_isBorelPair_containing_normalized_unipotent
    {k : Type u} [Field k] [IsAlgClosed k]
    {G U : GroupScheme (Spec (CommRingCat.of k))}
    [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
    [Smooth U.X.hom] [ConnectedSpace U.X.left]
    (i : U ⟶ G) (hi : IsClosedSubgroup i) (hU : IsUnipotent U)
    {T : CommGroupScheme (Spec (CommRingCat.of k))}
    (j : T.toGrp ⟶ G) (hj : IsMaximalTorus j)
    (hn : (SubgroupFunctor.range i).IsNormalizedBy (SubgroupFunctor.range j)) :
    ∃ (B : GroupScheme (Spec (CommRingCat.of k))) (b : B ⟶ G),
      IsBorelPair b j ∧ ∃ f : U ⟶ B, f ≫ b = i := by
  have : IsAffineHom U.X.hom := hi.isAffineHom
  have : Smooth T.toGrp.X.hom := hj.1.smooth
  have : ConnectedSpace T.toGrp.X.left := hj.1.connectedSpace
  have hUs : IsSolvableGroupScheme U := by
    rw [isSolvableGroupScheme_iff_isSolvable_points]
    exact isSolvable_points_of_isUnipotent hU (Over.mk (𝟙 _))
  obtain ⟨B, b, hb, hf, hg⟩ := exists_isBorelSubgroup_containing_normalized_solvable
    i j hUs isSolvableGroupScheme_of_commutative hn
  exact ⟨B, b, ⟨hb, hj, hg⟩, hf⟩

end Langlands.GroupScheme
