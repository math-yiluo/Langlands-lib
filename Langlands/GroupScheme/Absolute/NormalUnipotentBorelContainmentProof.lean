import Langlands.GroupScheme.Absolute.NormalUnipotentBorelContainmentStatement
import Langlands.GroupScheme.Absolute.RationalPointClosureSolvable
import Langlands.GroupScheme.Absolute.RationalPointClosureProof
import Langlands.GroupScheme.Absolute.UnipotentPointsSolvable
import Langlands.GroupScheme.Absolute.RationalSubgroupContainment
import Langlands.GroupScheme.Dynamic.CentralizerReductiveTransport
import Langlands.AlgebraicGeometry.SmoothReducedProof

/-! # Normal unipotent subgroups lie in every Borel subgroup -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Opposite
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

/-- The join of a solvable normal subgroup and a solvable subgroup is solvable. -/
theorem isSolvable_sup_of_normal {G : Type*} [Group G] (N K : Subgroup G) [N.Normal]
    [Group.IsSolvable N] [Group.IsSolvable K] : Group.IsSolvable ↥(N ⊔ K) := by
  let g := ((QuotientGroup.mk' N).comp (N ⊔ K).subtype).rangeRestrict
  have hsurj : Function.Surjective (g.comp (Subgroup.inclusion le_sup_right)) := by
    rintro ⟨_, x, rfl⟩
    obtain ⟨y, hy, z, hz, hyz⟩ := Subgroup.mem_sup_of_normal_left.1 x.2
    refine ⟨⟨z, hz⟩, Subtype.ext ?_⟩
    change QuotientGroup.mk' N z = QuotientGroup.mk' N x
    have hy1 : QuotientGroup.mk' N y = 1 := (QuotientGroup.eq_one_iff y).2 hy
    rw [← hyz, map_mul, hy1, one_mul]
  have : Group.IsSolvable ((QuotientGroup.mk' N).comp (N ⊔ K).subtype).range :=
    Group.isSolvable_of_surjective hsurj
  refine Group.isSolvable_of_ker_le_range (Subgroup.inclusion le_sup_left) g ?_
  intro x hx
  have hx' : QuotientGroup.mk' N (x : G) = 1 := congrArg Subtype.val hx
  rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hx'
  exact ⟨⟨x, hx'⟩, rfl⟩

variable {k : Type u} [Field k] [IsAlgClosed k]

/-- If every rational point of `X` is sent into `S` by `f`, then the whole image of `f` lies in
the closure of the locations of the points of `S`: closed points are dense in a scheme locally of
finite type over a field, and they are the locations of rational points. -/
theorem range_left_subset_closure {X : Over (Spec (CommRingCat.of k))}
    [LocallyOfFiniteType X.hom] {H : GroupScheme (Spec (CommRingCat.of k))} (f : X ⟶ H.X)
    {S : Set (Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ H.X)}
    (h : ∀ y : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ X, y ≫ f ∈ S) :
    Set.range f.left ⊆ closure (rationalPointImage H S) := by
  have : JacobsonSpace X.left := LocallyOfFiniteType.jacobsonSpace X.hom
  have himage : f.left '' closedPoints X.left ⊆ rationalPointImage H S := by
    rintro _ ⟨z, hz, rfl⟩
    let y : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ X :=
      Over.homMk (pointOfClosedPoint X.hom z hz) (pointOfClosedPoint_comp X.hom z hz)
    refine ⟨y ≫ f, h y, ?_⟩
    exact congrArg f.left (pointOfClosedPoint_apply X.hom z hz (IsLocalRing.closedPoint k))
  rintro _ ⟨x, rfl⟩
  have hx : x ∈ closure (closedPoints X.left) := by
    rw [closure_closedPoints]
    trivial
  exact closure_mono himage (image_closure_subset_closure_image f.left.continuous ⟨x, hx, rfl⟩)

/-- A rational point located in the image of a closed subgroup `ζ` is a point of `ζ`. -/
theorem mem_range_of_location_mem {Z H : GroupScheme (Spec (CommRingCat.of k))}
    [LocallyOfFiniteType Z.X.hom] [LocallyOfFiniteType H.X.hom] {ζ : Z ⟶ H}
    (hζ : IsClosedSubgroup ζ) {x : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ H.X}
    (hx : x.left (IsLocalRing.closedPoint k) ∈ Set.range ζ.hom.hom.left) :
    x ∈ (SubgroupFunctor.range ζ).carrier (Over.mk (𝟙 (Spec (CommRingCat.of k)))) := by
  have : IsClosedImmersion ζ.hom.hom.left := hζ
  obtain ⟨z, hz⟩ := hx
  have hzc : IsClosed {z} := by
    have hpre : ζ.hom.hom.left ⁻¹' {x.left (IsLocalRing.closedPoint k)} = {z} := by
      ext w
      rw [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_singleton_iff, ← hz]
      exact ζ.hom.hom.left.isClosedEmbedding.injective.eq_iff
    rw [← hpre]
    exact (isClosed_singleton_rationalPoint x).preimage ζ.hom.hom.left.continuous
  let y : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ Z.X :=
    Over.homMk (pointOfClosedPoint Z.X.hom z hzc) (pointOfClosedPoint_comp Z.X.hom z hzc)
  refine SubgroupFunctor.mem_range.2 ⟨y, rationalPoint_ext ?_⟩
  exact (congrArg ζ.hom.hom.left
    (pointOfClosedPoint_apply Z.X.hom z hzc (IsLocalRing.closedPoint k))).trans hz

/-- The containment of normal unipotent subgroups in Borel subgroups follows from the existence
of closed subgroups underlying the Zariski closure of a group of rational points. -/
theorem normalUnipotentBorelContainment_of_rationalPointClosure
    (hcl : RationalPointClosureSubgroupStatement.{u}) :
    NormalUnipotentBorelContainmentStatement.{u} := by
  intro k _ _ H _ _ _ U i hi hUs hUc hU hnormal C c hc
  have : Smooth U.X.hom := hUs
  have : ConnectedSpace U.X.left := hUc
  have : Smooth C.X.hom := hc.smooth
  have : ConnectedSpace C.X.left := hc.connectedSpace
  have : IsAffineHom U.X.hom := hi.isAffineHom
  have : IsReduced U.X.left :=
    Langlands.AlgebraicGeometry.SmoothReducedProof.isReduced_of_smooth_over_field
      k U.X.left U.X.hom
  have : IsReduced C.X.left :=
    Langlands.AlgebraicGeometry.SmoothReducedProof.isReduced_of_smooth_over_field
      k C.X.left C.X.hom
  set N := (SubgroupFunctor.range i).carrier (Over.mk (𝟙 (Spec (CommRingCat.of k)))) with hN
  set K := (SubgroupFunctor.range c).carrier (Over.mk (𝟙 (Spec (CommRingCat.of k)))) with hK
  have hNnormal : N.Normal := ⟨fun n hn g => hnormal _ g n (Subgroup.mem_top g) hn⟩
  have hNsolv : Group.IsSolvable N := by
    have : Group.IsSolvable ((yonedaGrp.obj U).obj (op (Over.mk (𝟙 (Spec (CommRingCat.of k)))))) :=
      isSolvable_points_of_isUnipotent hU (Over.mk (𝟙 (Spec (CommRingCat.of k))))
    exact @Group.isSolvable_of_surjective _ _ _ _ _
      (MonoidHom.rangeRestrict_surjective ((yonedaGrp.map i).app (op _)).hom) this
  have hKsolv : Group.IsSolvable K := by
    have : Group.IsSolvable ((yonedaGrp.obj C).obj (op (Over.mk (𝟙 (Spec (CommRingCat.of k)))))) :=
      (isSolvableGroupScheme_iff_isSolvable_points C).1 hc.isSolvableGroupScheme
    exact @Group.isSolvable_of_surjective _ _ _ _ _
      (MonoidHom.rangeRestrict_surjective ((yonedaGrp.map c).app (op _)).hom) this
  have hΓsolv : Group.IsSolvable ↥(N ⊔ K) := isSolvable_sup_of_normal N K
  obtain ⟨Z, ζ, hζ, hZs, hZrange⟩ := hcl k H (N ⊔ K)
  have : Smooth Z.X.hom := hZs
  have : IsClosedImmersion ζ.hom.hom.left := hζ
  have hmem : ∀ x, x ∈ pointClosureSubgroup H (N ⊔ K) →
      x ∈ (SubgroupFunctor.range ζ).carrier (Over.mk (𝟙 (Spec (CommRingCat.of k)))) :=
    fun x hx => mem_range_of_location_mem hζ (by rw [hZrange]; exact hx)
  have hmem' : ∀ y : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ Z.X,
      y ≫ ζ.hom.hom ∈ pointClosureSubgroup H (N ⊔ K) := by
    intro y
    rw [mem_pointClosureSubgroup, ← hZrange]
    exact ⟨_, rfl⟩
  -- `Z` is solvable: its rational points embed into the closure of the solvable group `N ⊔ K`.
  have hZsolv : IsSolvableGroupScheme Z := by
    rw [isSolvableGroupScheme_iff_isSolvable_points]
    have := isSolvable_pointClosureSubgroup (H := H) (N ⊔ K)
    have : Mono ζ.hom.hom := Over.mono_of_mono_left _
    let f₀ : (Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ Z.X) →*
        (Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ H.X) := ((yonedaGrp.map ζ).app (op _)).hom
    exact Group.isSolvable_of_isSolvable_injective (f := f₀.codRestrict _ hmem')
      (fun y y' h => (cancel_mono ζ.hom.hom).1 (congrArg Subtype.val h))
  -- `Z` is connected: the closure of the locations of `N ⊔ K` is the closure of a union of
  -- translates of the image of `C`, each meeting the connected image of `U`.
  have hZc : ConnectedSpace Z.X.left := by
    choose φ hφ using exists_comp_eq_mul_left (H := H)
    let A := Set.range i.hom.hom.left
    let B : N → Set H.X.left := fun a => Set.range (c.hom.hom ≫ φ a).left
    have hA : _root_.IsPreconnected A := isPreconnected_range i.hom.hom.left.continuous
    have hB : ∀ a, _root_.IsPreconnected (B a) :=
      fun a => isPreconnected_range (c.hom.hom ≫ φ a).left.continuous
    have hAB : ∀ a : N, (a : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ H.X).left
        (IsLocalRing.closedPoint k) ∈ A ∩ B a := by
      intro a
      obtain ⟨y, hy⟩ := SubgroupFunctor.mem_range.1 a.2
      have h1 : (1 : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ C.X) ≫ c.hom.hom ≫ φ a = a := by
        rw [← Category.assoc, hφ, MonObj.one_comp, mul_one]
      refine ⟨⟨y.left (IsLocalRing.closedPoint k), ?_⟩,
        ⟨(1 : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ C.X).left (IsLocalRing.closedPoint k), ?_⟩⟩
      · change (y ≫ i.hom.hom).left (IsLocalRing.closedPoint k) = _
        rw [hy]
      · change ((1 : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ C.X) ≫ c.hom.hom ≫ φ a).left
          (IsLocalRing.closedPoint k) = _
        rw [h1]
    obtain ⟨u₀⟩ : Nonempty U.X.left := inferInstance
    have hY : _root_.IsPreconnected (⋃ a : N, B a ∪ A) :=
      isPreconnected_iUnion ⟨i.hom.hom.left u₀, Set.mem_iInter.2 fun _ => Or.inr ⟨u₀, rfl⟩⟩
        fun a => IsPreconnected.union _ (hAB a).2 (hAB a).1 (hB a) hA
    have hYsub : (⋃ a : N, B a ∪ A) ⊆ closure (rationalPointImage H ((N ⊔ K : Subgroup _) :
        Set (Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ H.X))) := by
      refine Set.iUnion_subset fun a => Set.union_subset ?_ ?_
      · refine range_left_subset_closure _ fun y => ?_
        rw [← Category.assoc, hφ]
        exact (N ⊔ K).mul_mem (Subgroup.mem_sup_left a.2)
          (Subgroup.mem_sup_right (SubgroupFunctor.mem_range.2 ⟨y, rfl⟩))
      · exact range_left_subset_closure _ fun y =>
          Subgroup.mem_sup_left (SubgroupFunctor.mem_range.2 ⟨y, rfl⟩)
    have hsubY : rationalPointImage H ((N ⊔ K : Subgroup _) :
        Set (Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ H.X)) ⊆ ⋃ a : N, B a ∪ A := by
      rintro _ ⟨x, hx, rfl⟩
      obtain ⟨n, hn, z, hz, rfl⟩ := Subgroup.mem_sup_of_normal_left.1 hx
      obtain ⟨y, rfl⟩ := SubgroupFunctor.mem_range.1 hz
      refine Set.mem_iUnion.2 ⟨⟨n, hn⟩, Or.inl ⟨y.left (IsLocalRing.closedPoint k), ?_⟩⟩
      change (y ≫ c.hom.hom ≫ φ n).left (IsLocalRing.closedPoint k) = _
      rw [← Category.assoc, hφ]
    have hcl' := hY.subset_closure hYsub (closure_mono hsubY)
    rw [← hZrange, ← Set.image_univ,
      ζ.hom.hom.left.isClosedEmbedding.isInducing.isPreconnected_image] at hcl'
    have : PreconnectedSpace Z.X.left := ⟨hcl'⟩
    exact ⟨⟨(1 : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ Z.X).left (IsLocalRing.closedPoint k)⟩⟩
  -- The Borel subgroup `c` factors through `ζ`, hence equals it by maximality.
  obtain ⟨f, hf⟩ := SubgroupFunctor.exists_factor_of_algClosed_points (i := c) hζ
    (fun x hx => hmem x (le_pointClosureSubgroup _ (Subgroup.mem_sup_right hx)))
  have : IsIso f := hc.maximal Z ζ f hζ hZs hZc hZsolv hf
  have hζc : ζ = inv f ≫ c := by rw [← hf, IsIso.inv_hom_id_assoc]
  apply SubgroupFunctor.range_le_of_algClosed_points hc.isClosedSubgroup
  intro x hx
  obtain ⟨y, rfl⟩ := SubgroupFunctor.mem_range.1
    (hmem x (le_pointClosureSubgroup _ (Subgroup.mem_sup_left hx)))
  refine SubgroupFunctor.mem_range.2 ⟨y ≫ (inv f).hom.hom, ?_⟩
  rw [Category.assoc, hζc]
  rfl

/-- Over an algebraically closed field, a smooth connected unipotent normal closed subgroup of a
smooth connected affine group scheme lies in every Borel subgroup. -/
theorem normalUnipotentBorelContainment : NormalUnipotentBorelContainmentStatement.{u} :=
  normalUnipotentBorelContainment_of_rationalPointClosure rationalPointClosureSubgroup

end Langlands.GroupScheme
