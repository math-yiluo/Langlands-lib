import Langlands.GroupScheme.RelativeIdentityComponent.BaseChange
import Langlands.AlgebraicGeometry.ImmersionExhaustionLocality
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.RingTheory.Artinian.Ring

/-! # Actual subscheme families and their scalar changes -/

noncomputable section

universe u v

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

namespace Langlands.AlgebraicGeometry.ImmersionExhaustion

/-- A slice pullback of a morphism is also a cartesian square of schemes. -/
theorem over_map_isPullback {S T : Scheme.{u}} {X Y : Over S}
    (f : X ⟶ Y) (b : T ⟶ S) :
    IsPullback (pullback.fst X.hom b) (((Over.pullback b).map f).left)
      f.left (pullback.fst Y.hom b) :=
  (Langlands.GroupScheme.RelativeIdentityComponent.overPullback_isPullback b f).flip

/-- Fullness of a slice pullback is fullness of the pulled-back subscheme. -/
theorem isIso_over_map_iff {S T : Scheme.{u}} {X Y : Over S}
    (f : X ⟶ Y) (b : T ⟶ S) :
    IsIso ((Over.pullback b).map f) ↔
      IsIso (pullback.snd f.left (pullback.fst Y.hom b)) := by
  rw [← isIso_iff_of_reflects_iso _ (Over.forget T)]
  change IsIso (((Over.pullback b).map f).left) ↔ _
  have sq := over_map_isPullback f b
  rw [← sq.isoPullback_hom_snd,
    ← MorphismProperty.isomorphisms.iff, ← MorphismProperty.isomorphisms.iff]
  exact (MorphismProperty.isomorphisms Scheme).cancel_left_of_respectsIso _ _

/-- An increasing family of actual subschemes of an actual relative scheme. -/
structure Family (S : Scheme.{u}) (I : Type v) [Preorder I] where
  ambient : Over S
  member : I → Over S
  inclusion : ∀ i, member i ⟶ ambient
  immersion : ∀ i, IsImmersion (inclusion i).left
  increasing : ∀ i k, i ≤ k → ∃ a : member i ⟶ member k, a ≫ inclusion k = inclusion i

namespace Family

variable {S T U : Scheme.{u}} {I : Type v} [Preorder I]

/-- Bundle a scheme family with its structural triangles over the base. -/
def ofSchemes {X : Scheme.{u}} (f : X ⟶ S) (Y : I → Scheme.{u})
    (j : ∀ i, Y i ⟶ X) (hj : ∀ i, IsImmersion (j i))
    (hinc : ∀ i k, i ≤ k → ∃ a : Y i ⟶ Y k, a ≫ j k = j i) : Family S I where
  ambient := Over.mk f
  member i := Over.mk (j i ≫ f)
  inclusion i := Over.homMk (j i) rfl
  immersion := hj
  increasing i k hik := by
    obtain ⟨a, ha⟩ := hinc i k hik
    refine ⟨Over.homMk a (by
      change a ≫ (j k ≫ f) = j i ≫ f
      rw [← Category.assoc, ha]), ?_⟩
    exact Over.OverMorphism.ext ha

/-- One member is the entire ambient relative scheme. -/
def Full (D : Family S I) : Prop := ∃ i, IsIso (D.inclusion i)

/-- Base change of the entire family, using the actual slice pullback functor. -/
def baseChange (D : Family S I) (b : T ⟶ S) : Family T I where
  ambient := (Over.pullback b).obj D.ambient
  member i := (Over.pullback b).obj (D.member i)
  inclusion i := (Over.pullback b).map (D.inclusion i)
  immersion i := MorphismProperty.of_isPullback (over_map_isPullback (D.inclusion i) b)
    (D.immersion i)
  increasing i k hik := by
    obtain ⟨a, ha⟩ := D.increasing i k hik
    exact ⟨(Over.pullback b).map a, by rw [← Functor.map_comp, ha]⟩

/-- Fullness is preserved by any scalar extension. -/
theorem Full.baseChange {D : Family S I} (h : D.Full) (b : T ⟶ S) :
    (D.baseChange b).Full := by
  obtain ⟨i, hi⟩ := h
  let := hi
  exact ⟨i, (Over.pullback b).map_isIso (D.inclusion i)⟩

/-- Direct and iterated scalar change give the same fullness assertion. -/
theorem full_baseChange_comp_iff (D : Family S I) (b : T ⟶ S) (c : U ⟶ T) :
    ((D.baseChange b).baseChange c).Full ↔ (D.baseChange (c ≫ b)).Full := by
  exact exists_congr fun i => (NatIso.isIso_map_iff (Over.pullbackComp c b)
    (D.inclusion i)).symm

/-- Identity scalar change gives the original fullness assertion. -/
theorem full_baseChange_id_iff (D : Family S I) :
    (D.baseChange (𝟙 S)).Full ↔ D.Full :=
  exists_congr fun i => NatIso.isIso_map_iff Over.pullbackId (D.inclusion i)

/-- The family contains the whole ambient scheme after every local Artinian
affine base change, with the index allowed to depend on the test. -/
def ArtinianTests (D : Family S I) : Prop :=
  ∀ (R : Type u) [CommRing R] [IsLocalRing R] [IsArtinianRing R]
    (b : Spec (CommRingCat.of R) ⟶ S), (D.baseChange b).Full

/-- The local Artinian testing condition is stable under arbitrary base change. -/
theorem ArtinianTests.baseChange {D : Family S I} (h : D.ArtinianTests) (b : T ⟶ S) :
    (D.baseChange b).ArtinianTests := by
  intro R _ _ _ c
  exact (D.full_baseChange_comp_iff b c).mpr (h R (c ≫ b))

/-- Fullness in the slice category is the same as fullness of the underlying
subscheme immersion. -/
theorem full_iff (D : Family S I) :
    D.Full ↔ ∃ i, IsIso (D.inclusion i).left :=
  exists_congr fun i =>
    (isIso_iff_of_reflects_iso (D.inclusion i) (Over.forget S)).symm

/-- A directed family is full if it is full on an open neighborhood of every
point of a quasi-compact ambient scheme. -/
theorem full_of_pointwise_open (D : Family S I)
    [CompactSpace D.ambient.left] [Nonempty I] [IsDirected I (· ≤ ·)]
    (hloc : ∀ x : D.ambient.left, ∃ V : D.ambient.left.Opens, x ∈ V ∧
      ∃ i, IsIso (pullback.snd (D.inclusion i).left V.ι)) : D.Full := by
  apply D.full_iff.mpr
  apply exists_isIso_of_pointwise_open (fun i => (D.member i).left)
    (fun i => (D.inclusion i).left) D.immersion
  · intro i k hik
    obtain ⟨a, ha⟩ := D.increasing i k hik
    exact ⟨a.left, congrArg (fun f => f.left) ha⟩
  · exact hloc

end Family

end Langlands.AlgebraicGeometry.ImmersionExhaustion
