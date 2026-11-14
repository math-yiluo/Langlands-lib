import Langlands.GroupScheme.IntegralModel.ConnectedGenerationField
import Langlands.GroupScheme.Absolute.FiniteIndexQuotientProperProof
import Langlands.GroupScheme.RelativeIdentityComponent.SmoothExistenceProof
import Langlands.GroupScheme.SchemeActionOrbit

/-! # Finite-index closed subgroups contain the relative identity component -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.ConnectedGeneration

variable {k : Type u} [Field k]

private theorem exists_point_lift_of_mem_range
    {V W : Over (Spec (CommRingCat.of k))} (t : V ⟶ W)
    [IsClosedImmersion t.left]
    (a : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ W)
    (ha : a.left (IsLocalRing.closedPoint k) ∈ Set.range t.left) :
    ∃ b : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ V, b ≫ t = a := by
  have : Subsingleton (Over.mk (𝟙 (Spec (CommRingCat.of k)))).left :=
    inferInstanceAs (Subsingleton (Spec (CommRingCat.of k)))
  have : IsReduced (Over.mk (𝟙 (Spec (CommRingCat.of k)))).left :=
    inferInstanceAs (IsReduced (Spec (CommRingCat.of k)))
  have hr : Set.range a.left ⊆ Set.range t.left := by
    rintro _ ⟨p, rfl⟩
    have hp : p = IsLocalRing.closedPoint k := Subsingleton.elim _ _
    simpa only [hp] using ha
  obtain ⟨b, hb⟩ := FiniteIndexTransfer.exists_lift_of_range_subset t.left a.left hr
  refine ⟨Over.homMk b ?_, Over.OverMorphism.ext hb⟩
  rw [← t.w, ← Category.assoc, hb]
  exact a.w

variable {G H : GroupScheme (Spec (CommRingCat.of k))}

private theorem comp_translation (x a : rationalPoints G) :
    a ≫ SchemeAction.translation (ModObj.regular G.X) x = x * a := by
  rw [SchemeAction.comp_translation]
  have hu : toUnit (Over.mk (𝟙 (Spec (CommRingCat.of k)))) = 𝟙 _ :=
    toUnit_unique _ _
  rw [hu, Category.id_comp]
  rfl

private theorem isClosedImmersion_translated (j : H ⟶ G) (hj : IsClosedSubgroup j)
    (x : rationalPoints G) :
    IsClosedImmersion
      (j.hom.hom ≫ SchemeAction.translation (ModObj.regular G.X) x).left := by
  have : IsClosedImmersion j.hom.hom.left := hj
  have : IsIso (SchemeAction.translation (ModObj.regular G.X) x).left :=
    (Over.forget _).map_isIso (SchemeAction.translationIso (ModObj.regular G.X) x).hom
  change IsClosedImmersion
    (j.hom.hom.left ≫ (SchemeAction.translation (ModObj.regular G.X) x).left)
  infer_instance

private theorem mem_translated_range_iff (j : H ⟶ G) (hj : IsClosedSubgroup j)
    (x a : rationalPoints G) :
    a.left (IsLocalRing.closedPoint k) ∈
        Set.range (j.hom.hom ≫ SchemeAction.translation (ModObj.regular G.X) x).left ↔
      x⁻¹ * a ∈ (rationalPoints.map j).range := by
  have := isClosedImmersion_translated j hj x
  constructor
  · intro ha
    obtain ⟨b, hb⟩ := exists_point_lift_of_mem_range
      (j.hom.hom ≫ SchemeAction.translation (ModObj.regular G.X) x) a ha
    have hb' : x * rationalPoints.map j b = a := by
      change x * (b ≫ j.hom.hom) = a
      rw [← comp_translation, Category.assoc]
      exact hb
    refine ⟨b, ?_⟩
    rw [← hb', inv_mul_cancel_left]
  · rintro ⟨b, hb⟩
    have hb' : x * rationalPoints.map j b = a := by
      rw [hb, mul_inv_cancel_left]
    refine ⟨b.left (IsLocalRing.closedPoint k), ?_⟩
    change (b ≫ (j.hom.hom ≫ SchemeAction.translation (ModObj.regular G.X) x)).left _ = _
    rw [← Category.assoc, comp_translation]
    exact congrArg (fun p : rationalPoints G => p.left (IsLocalRing.closedPoint k)) hb'

/-- A closed subgroup of finite index on algebraically closed rational points
contains the points of every relative identity-component representative. -/
theorem componentRange_le_of_finiteIndex [IsAlgClosed k] [Smooth G.X.hom]
    (j : H ⟶ G) (hj : IsClosedSubgroup j)
    (hfinite : (rationalPoints.map j).range.FiniteIndex)
    (N : GroupScheme (Spec (CommRingCat.of k))) (i : N ⟶ G)
    (hi : IsRelativeIdentityComponent G i) :
    (rationalPoints.map i).range ≤ (rationalPoints.map j).range := by
  classical
  let K := (rationalPoints.map j).range
  have : K.FiniteIndex := hfinite
  let : Fintype (rationalPoints G ⧸ K) := Fintype.ofFinite _
  let C : (rationalPoints G ⧸ K) → Set G.X.left := fun q =>
    Set.range (j.hom.hom ≫ SchemeAction.translation (ModObj.regular G.X) q.out).left
  have hC : ∀ q, IsClosed (C q) := by
    intro q
    have := isClosedImmersion_translated j hj q.out
    exact Scheme.Hom.isClosedEmbedding
      (j.hom.hom ≫ SchemeAction.translation (ModObj.regular G.X) q.out).left
      |>.isClosed_range
  have hpoint : ∀ a : rationalPoints G,
      a.left (IsLocalRing.closedPoint k) ∈ ⋃ q, C q := by
    intro a
    refine Set.mem_iUnion.mpr ⟨(a : rationalPoints G ⧸ K), ?_⟩
    apply (mem_translated_range_iff j hj _ a).mpr
    exact QuotientGroup.eq.mp (Quotient.out_eq' (a : rationalPoints G ⧸ K))
  have hclosed : IsClosed (⋃ q, C q) := isClosed_iUnion_of_finite hC
  have hcov : ⋃ q, C q = Set.univ := by
    have : JacobsonSpace G.X.left := LocallyOfFiniteType.jacobsonSpace G.X.hom
    apply Set.eq_univ_of_univ_subset
    rw [← closure_closedPoints]
    apply closure_minimal _ hclosed
    intro x hx
    let a : rationalPoints G :=
      Over.homMk (pointOfClosedPoint G.X.hom x hx) (by simp)
    have h1 := hpoint a
    convert h1 using 2
    exact (pointOfClosedPoint_apply G.X.hom x hx _).symm
  have : IsOpenImmersion i.hom.hom.left := hi.isOpenImmersion
  have : Smooth N.X.hom := by
    rw [← Over.w i.hom.hom]
    infer_instance
  obtain ⟨N', i', hi', -, hconn⟩ :=
    RelativeIdentityComponent.smoothExistence _ G inferInstance
  have : GeometricallyConnected N'.X.hom := hconn
  have : GeometricallyConnected N.X.hom := hi.geometricallyConnected hi'
  have : ConnectedSpace N.X.left :=
    GeometricallyConnected.connectedSpace_of_subsingleton (f := N.X.hom)
  have : IrreducibleSpace N.X.left :=
    Langlands.AlgebraicGeometry.irreducibleSpace_of_smooth_connected N.X.hom
  have hirr : IsIrreducible (Set.range i.hom.hom.left) := by
    simpa only [Set.image_univ] using
      (IrreducibleSpace.isIrreducible_univ N.X.left).image
        i.hom.hom.left i.hom.hom.left.continuous.continuousOn
  let t : Finset (Set G.X.left) := Finset.univ.image C
  obtain ⟨Z, hZ, hsub⟩ := isIrreducible_iff_sUnion_isClosed.mp hirr t (by
    intro Z hZ
    obtain ⟨q, -, rfl⟩ := Finset.mem_image.mp hZ
    exact hC q) (by
    intro x hx
    have hx' : x ∈ ⋃ q, C q := by rw [hcov]; trivial
    obtain ⟨q, hq⟩ := Set.mem_iUnion.mp hx'
    exact Set.mem_sUnion.mpr ⟨C q, Finset.mem_image.mpr ⟨q, Finset.mem_univ _, rfl⟩, hq⟩)
  obtain ⟨q, -, rfl⟩ := Finset.mem_image.mp hZ
  have hunit : (1 : rationalPoints G).left (IsLocalRing.closedPoint k) ∈ C q := by
    apply hsub
    refine ⟨(1 : rationalPoints N).left (IsLocalRing.closedPoint k), ?_⟩
    change (rationalPoints.map i 1).left (IsLocalRing.closedPoint k) = _
    rw [map_one]
  have hqinv : q.out⁻¹ ∈ K := by
    have := (mem_translated_range_iff j hj q.out 1).mp hunit
    simpa only [mul_one] using this
  have hq : q.out ∈ K := K.inv_mem_iff.mp hqinv
  rintro a ⟨b, rfl⟩
  have ha : (rationalPoints.map i b).left (IsLocalRing.closedPoint k) ∈ C q :=
    hsub ⟨b.left (IsLocalRing.closedPoint k), rfl⟩
  have hqa := (mem_translated_range_iff j hj q.out _).mp ha
  simpa only [mul_inv_cancel_left] using K.mul_mem hq hqa

end Langlands.GroupScheme.ConnectedGeneration
