import Langlands.GroupScheme.SchemeActionRationalPoints
import Langlands.GroupScheme.SchemeActionReducedClosed
import Langlands.AlgebraicGeometry.ProperConnectedAffineConstancy
import Mathlib.AlgebraicGeometry.Morphisms.Proper

/-! # Proper images in fibres of invariant affine-valued maps on homogeneous spaces -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

/-- `H` sends every proper connected reduced scheme to one point of each of its
reduced separated quasi-compact locally finite type homogeneous spaces. -/
def HasOnePointProperImages {k : Type u} [Field k]
    (H : GroupScheme (Spec (CommRingCat.of k))) : Prop :=
  ∀ (O : Over (Spec (CommRingCat.of k))),
    IsReduced O.left → IsSeparated O.hom → LocallyOfFiniteType O.hom → QuasiCompact O.hom →
      ∀ (a : SchemeAction H O) (x : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ O),
        (∀ y : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ O,
          ∃ g : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ H.X, a.act g x = y) →
        ∀ (Z : Over (Spec (CommRingCat.of k))), IsProper Z.hom → IsReduced Z.left →
          ConnectedSpace Z.left → ∀ j : Z ⟶ O, (Set.range j.left).Subsingleton

/-- If an invariant map to an affine scheme has single orbits as its rational fibres,
the one-point property of the acting group passes to the whole scheme. -/
theorem HasOnePointProperImages.subsingleton_range_of_fibres
    {k : Type u} [Field k] [IsAlgClosed k]
    {N : GroupScheme (Spec (CommRingCat.of k))} [Smooth N.X.hom]
    (hN : HasOnePointProperImages N)
    {O W : Over (Spec (CommRingCat.of k))}
    [IsReduced O.left] [IsSeparated O.hom] [LocallyOfFiniteType O.hom] [QuasiCompact O.hom]
    [IsAffine W.left] (b : SchemeAction N O) (f : O ⟶ W)
    (hf : ∀ (n : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ N.X)
        (y : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ O), b.act n y ≫ f = y ≫ f)
    (horb : ∀ y z : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ O, y ≫ f = z ≫ f →
        ∃ n : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ N.X, b.act n y = z)
    {Z : Over (Spec (CommRingCat.of k))} [IsProper Z.hom] [IsReduced Z.left]
    [ConnectedSpace Z.left] (j : Z ⟶ O) : (Set.range j.left).Subsingleton := by
  obtain ⟨z0⟩ := nonempty_rationalPoints Z
  -- The value of the constant map `j ≫ f` and its closed image point.
  let w0 : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ W := z0 ≫ j ≫ f
  have : IsClosedImmersion w0.left :=
    isClosedImmersion_of_comp_eq_id W.hom w0.left (Over.w w0)
  have hconst : (j ≫ f).left = Z.hom ≫ w0.left :=
    Langlands.AlgebraicGeometry.affineMap_eq_constant_of_proper_connected_reduced
      Z.hom z0.left (Over.w z0) (j ≫ f).left
  -- The fibre through the image of `j`.
  let C : Set O.left := f.left ⁻¹' Set.range w0.left
  have hC : IsClosed C :=
    w0.left.isClosedEmbedding.isClosed_range.preimage f.left.continuous
  have htrans : ∀ n : 𝟙_ (Over (Spec (CommRingCat.of k))) ⟶ N.X,
      b.translation n ≫ f = f := by
    intro n
    apply hom_ext_rationalPoints
    intro y
    have hu : toUnit (Over.mk (𝟙 (Spec (CommRingCat.of k)))) = 𝟙 _ :=
      toUnit_unique _ _
    rw [b.comp_translation_assoc, hu, Category.id_comp]
    exact hf n y
  have hinv : b.IsInvariantClosed ⟨C, hC⟩ := by
    intro n y hy
    change f.left ((b.translation n).left y) ∈ Set.range w0.left
    rw [← Scheme.Hom.comp_apply, ← Over.comp_left, htrans n]
    exact hy
  obtain ⟨O', incl, b', hO'red, hincl, hrange, hcompat⟩ :=
    b.exists_reduced_invariantClosedSubscheme ⟨C, hC⟩ hinv
  have : IsSeparated O'.hom := by rw [← Over.w incl]; infer_instance
  have : LocallyOfFiniteType O'.hom := by rw [← Over.w incl]; infer_instance
  have : QuasiCompact O'.hom := by rw [← Over.w incl]; infer_instance
  have : Mono incl := Over.mono_of_mono_left incl
  -- Lift `j` into the reduced fibre.
  have hjC : Set.range j.left ⊆ Set.range incl.left := by
    rw [hrange]
    rintro _ ⟨z, rfl⟩
    change f.left (j.left z) ∈ Set.range w0.left
    rw [← Scheme.Hom.comp_apply, ← Over.comp_left, hconst, Scheme.Hom.comp_apply]
    exact ⟨_, rfl⟩
  obtain ⟨l, hl⟩ := FiniteIndexTransfer.exists_lift_of_range_subset incl.left j.left hjC
  let j' : Z ⟶ O' := Over.homMk l (by rw [← Over.w incl, ← Category.assoc, hl, Over.w j])
  -- The invariant map is constant on the reduced fibre.
  have hinclf : ∀ y : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ O', (y ≫ incl) ≫ f = w0 := by
    have hsub : Set.range (incl ≫ f).left ⊆ Set.range w0.left := by
      rintro _ ⟨y, rfl⟩
      have hy : incl.left y ∈ Set.range incl.left := ⟨y, rfl⟩
      rw [hrange] at hy
      exact hy
    obtain ⟨m, hm⟩ :=
      FiniteIndexTransfer.exists_lift_of_range_subset w0.left (incl ≫ f).left hsub
    have hmO : m = O'.hom := by
      have h1 : m ≫ w0.left ≫ W.hom = (incl ≫ f).left ≫ W.hom := by
        rw [← Category.assoc, hm]
      rw [Over.w w0, Over.w (incl ≫ f)] at h1
      simpa using h1
    intro y
    apply Over.OverMorphism.ext
    have e : (y ≫ incl ≫ f).left = y.left ≫ (incl ≫ f).left := Over.comp_left _ _ _ _ _
    rw [Category.assoc, e, ← hm, hmO, ← Category.assoc, Over.w y]
    simp
  -- The rational points of the reduced fibre form one orbit.
  let x' : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ O' := z0 ≫ j'
  have hO'trans : ∀ y : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ O',
      ∃ n : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ N.X, b'.act n x' = y := by
    intro y
    obtain ⟨n, hn⟩ := horb (x' ≫ incl) (y ≫ incl) (by rw [hinclf, hinclf])
    refine ⟨n, ?_⟩
    apply (cancel_mono incl).mp
    rw [hcompat, hn]
  have hsub := hN O' hO'red inferInstance inferInstance inferInstance b' x' hO'trans Z
    inferInstance inferInstance inferInstance j'
  rintro _ ⟨z1, rfl⟩ _ ⟨z2, rfl⟩
  have e : j'.left z1 = j'.left z2 := hsub ⟨z1, rfl⟩ ⟨z2, rfl⟩
  rw [← hl, Scheme.Hom.comp_apply, Scheme.Hom.comp_apply]
  exact congrArg incl.left e

/-- A group with trivial points on every test has the one-point property: its
homogeneous spaces are single points. -/
theorem hasOnePointProperImages_of_range_id_eq_bot
    {k : Type u} [Field k] [IsAlgClosed k]
    {H : GroupScheme (Spec (CommRingCat.of k))}
    (h : SubgroupFunctor.range (𝟙 H) = ⊥) : HasOnePointProperImages H := by
  intro O _ _ hlft _ a x hx Z _ _ _ j
  have hone : ∀ g : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ H.X, g = 1 := by
    intro g
    have hg : g ∈ (SubgroupFunctor.range (𝟙 H)).carrier _ :=
      SubgroupFunctor.mem_range.mpr ⟨g, by simp⟩
    rw [h, SubgroupFunctor.bot_carrier, Subgroup.mem_bot] at hg
    exact hg
  have hall : ∀ y : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ O, y = x := by
    intro y
    obtain ⟨g, rfl⟩ := hx y
    rw [hone g, a.act_one]
  have : JacobsonSpace O.left := LocallyOfFiniteType.jacobsonSpace O.hom
  have hx0 : IsClosed ({x.left (IsLocalRing.closedPoint k)} : Set O.left) :=
    (pointEquivClosedPoint O.hom ⟨x.left, Over.w x⟩).2
  have hcp : closedPoints O.left ⊆ {x.left (IsLocalRing.closedPoint k)} := by
    intro w hw
    have e := congrArg (fun p => p.left (IsLocalRing.closedPoint k))
      (hall (Over.homMk (pointOfClosedPoint O.hom w hw) (pointOfClosedPoint_comp O.hom w hw)))
    simp only [Over.homMk_left] at e
    exact (pointOfClosedPoint_apply O.hom w hw _).symm.trans e
  have huniv : (Set.univ : Set O.left) ⊆ {x.left (IsLocalRing.closedPoint k)} := by
    rw [← closure_closedPoints]
    exact closure_minimal hcp hx0
  exact Set.subsingleton_singleton.anti ((Set.subset_univ _).trans huniv)

end Langlands.GroupScheme
