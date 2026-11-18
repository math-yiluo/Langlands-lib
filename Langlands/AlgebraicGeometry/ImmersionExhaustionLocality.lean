import Mathlib.AlgebraicGeometry.Morphisms.Immersion
import Mathlib.AlgebraicGeometry.Morphisms.IsIso
import Mathlib.Data.Set.Finite.Lattice

/-! # Locality for directed exhaustions by subscheme immersions -/

noncomputable section

universe u v

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

namespace Langlands.AlgebraicGeometry.ImmersionExhaustion

/-- A subobject containing the full object is the full object. -/
theorem isIso_of_factorization {C : Type*} [Category C] {X Y Z : C}
    (i : Y ⟶ X) (j : Z ⟶ X) [IsIso i] [Mono j]
    (a : Y ⟶ Z) (ha : a ≫ j = i) : IsIso j := by
  have : IsSplitEpi j := IsSplitEpi.mk' ⟨inv i ≫ a, by rw [Category.assoc, ha]; simp⟩
  exact isIso_of_mono_of_isSplitEpi j

/-- Containment of subobjects preserves fullness after every pullback. -/
theorem isIso_pullback_snd_of_factorization
    {C : Type*} [Category C] [HasPullbacks C] {X Y Z T : C}
    (i : Y ⟶ X) (j : Z ⟶ X) [Mono j]
    (a : Y ⟶ Z) (ha : a ≫ j = i) (p : T ⟶ X)
    [IsIso (pullback.snd i p)] : IsIso (pullback.snd j p) := by
  let b : pullback i p ⟶ pullback j p :=
    pullback.lift (pullback.fst i p ≫ a) (pullback.snd i p)
      (by rw [Category.assoc, ha, pullback.condition])
  exact isIso_of_factorization (pullback.snd i p) (pullback.snd j p) b
    (pullback.lift_snd _ _ _)

/-- The actual structural base change of a subscheme immersion is a cartesian
square over the original ambient scheme. -/
theorem over_pullback_isPullback {S X Y T : Scheme.{u}}
    (f : X ⟶ S) (j : Y ⟶ X) (b : T ⟶ S) :
    IsPullback (pullback.fst (j ≫ f) b)
      (((Over.pullback b).map (Over.homMk j rfl :
        Over.mk (j ≫ f) ⟶ Over.mk f)).left)
      j (pullback.fst f b) := by
  apply IsPullback.of_bot (v₂₁ := pullback.snd f b) (v₂₂ := f) (h₃₁ := b)
  · simpa [Over.pullback_map_left] using IsPullback.of_hasPullback (j ≫ f) b
  · simp [Over.pullback_map_left]
  · exact IsPullback.of_hasPullback f b

/-- Either actual convention for the pulled-back inclusion tests the same
scheme-theoretic fullness. -/
theorem isIso_baseChange_iff {S X Y T : Scheme.{u}}
    (f : X ⟶ S) (j : Y ⟶ X) (b : T ⟶ S) :
    IsIso (((Over.pullback b).map (Over.homMk j rfl :
      Over.mk (j ≫ f) ⟶ Over.mk f)).left) ↔
      IsIso (pullback.snd j (pullback.fst f b)) := by
  let sq := over_pullback_isPullback f j b
  rw [← sq.isoPullback_hom_snd,
    ← MorphismProperty.isomorphisms.iff, ← MorphismProperty.isomorphisms.iff]
  exact (MorphismProperty.isomorphisms Scheme).cancel_left_of_respectsIso _ _

private theorem isIso_morphismRestrict_iff {X Y : Scheme.{u}}
    (j : Y ⟶ X) (U : X.Opens) :
    IsIso (j ∣_ U) ↔ IsIso (pullback.snd j U.ι) := by
  have sq := (isPullback_morphismRestrict j U).flip
  rw [← sq.isoPullback_hom_snd,
    ← MorphismProperty.isomorphisms.iff, ← MorphismProperty.isomorphisms.iff]
  exact (MorphismProperty.isomorphisms Scheme).cancel_left_of_respectsIso _ _

/-- On a quasi-compact ambient scheme, a directed increasing family of
subscheme immersions that is full locally at every point is full at one stage. -/
theorem exists_isIso_of_pointwise_open
    {X : Scheme.{u}} [CompactSpace X]
    {I : Type v} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
    (Y : I → Scheme.{u}) (j : ∀ i, Y i ⟶ X)
    (hj : ∀ i, IsImmersion (j i))
    (hinc : ∀ i k, i ≤ k → ∃ a : Y i ⟶ Y k, a ≫ j k = j i)
    (hloc : ∀ x : X, ∃ U : X.Opens, x ∈ U ∧
      ∃ i, IsIso (pullback.snd (j i) U.ι)) :
    ∃ i, IsIso (j i) := by
  classical
  let (i : I) : IsImmersion (j i) := hj i
  choose U hx i hi using hloc
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover
    (fun x => (U x : Set X)) (fun x => (U x).isOpen)
    (fun x _ => Set.mem_iUnion.mpr ⟨x, hx x⟩)
  obtain ⟨k, hk⟩ := (t.finite_toSet.image i).bddAbove
  refine ⟨k, ?_⟩
  apply IsZariskiLocalAtTarget.of_forall_exists_morphismRestrict
    (P := MorphismProperty.isomorphisms Scheme)
  intro x
  obtain ⟨z, hz, hxz⟩ := Set.mem_iUnion₂.mp (ht (Set.mem_univ x))
  obtain ⟨a, ha⟩ := hinc (i z) k (hk ⟨z, hz, rfl⟩)
  have := hi z
  have H := isIso_pullback_snd_of_factorization (j (i z)) (j k) a ha (U z).ι
  exact ⟨U z, hxz, (isIso_morphismRestrict_iff (j k) (U z)).mpr H⟩

/-- The finite-open-cover locality assertion for a directed subscheme family. -/
def LocalityStatement : Prop :=
  ∀ (X : Scheme.{u}) [CompactSpace X]
    (I : Type v) [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
    (Y : I → Scheme.{u}) (j : ∀ i, Y i ⟶ X),
    (∀ i, IsImmersion (j i)) →
    (∀ i k, i ≤ k → ∃ a : Y i ⟶ Y k, a ≫ j k = j i) →
    (∀ x : X, ∃ U : X.Opens, x ∈ U ∧
      ∃ i, IsIso (pullback.snd (j i) U.ι)) →
    ∃ i, IsIso (j i)

/-- Directed exhaustion is detected on an open neighborhood of each point. -/
theorem locality : LocalityStatement.{u, v} :=
  fun _ _ _ _ _ _ _ _ hj hinc hloc =>
    exists_isIso_of_pointwise_open _ _ hj hinc hloc

end Langlands.AlgebraicGeometry.ImmersionExhaustion
