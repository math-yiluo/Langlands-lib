import Langlands.AlgebraicGeometry.ClosedSubschemeFiberIncidence

/-! # Finite closed covers of actual fibres near a generic point -/

noncomputable section

universe u v

open Set Topology TopologicalSpace CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.GenericImagePattern

variable {X Y : Scheme.{u}}

/-- The actual fibre is covered by the base changes of the given subschemes. -/
def closedSubschemeFiberCover {ι : Type v} (f : X ⟶ Y)
    {Z : ι → Scheme.{u}} (g : ∀ i, Z i ⟶ X) (y : Y) : Prop :=
  (⋃ i, fiberSubschemeSets f g y i) = Set.univ

/-- Failure of coverage is exactly membership in the image of the uncovered locus. -/
theorem closedSubschemeFiberCover_iff {ι : Type v} (f : X ⟶ Y)
    {Z : ι → Scheme.{u}} (g : ∀ i, Z i ⟶ X) (y : Y) :
    closedSubschemeFiberCover f g y ↔
      y ∉ f '' (⋃ i, Set.range (g i))ᶜ := by
  have hset : (f.fiberι y) ⁻¹' (⋃ i, Set.range (g i))ᶜ =
      (⋃ i, fiberSubschemeSets f g y i)ᶜ := by
    ext x
    simp [fiberSubschemeSets]
  rw [← preimage_fiberι_nonempty_iff f y, hset]
  simp only [Set.not_nonempty_iff_eq_empty, Set.compl_empty_iff,
    closedSubschemeFiberCover]

/-- The cover predicate refers to the ranges of actual scheme base changes. -/
theorem closedSubschemeFiberCover_iff_baseChangeRanges {ι : Type v} (f : X ⟶ Y)
    {Z : ι → Scheme.{u}} (g : ∀ i, Z i ⟶ X) (y : Y) :
    closedSubschemeFiberCover f g y ↔
      (⋃ i, Set.range (pullback.snd (g i) (f.fiberι y))) = Set.univ := by
  simp only [range_baseChange_eq_fiberSubschemeSets, closedSubschemeFiberCover]

/-- Finite closed-subscheme coverage has a constant truth value near a whole-space
 generic point of a Noetherian base. -/
theorem exists_open_closedSubschemeFiberCover
    {ι : Type v} [Finite ι] [IsNoetherian Y]
    (f : X ⟶ Y) [LocallyOfFiniteType f] [QuasiCompact f]
    {Z : ι → Scheme.{u}} (g : ∀ i, Z i ⟶ X)
    [∀ i, IsClosedImmersion (g i)]
    {η : Y} (hη : IsGenericPoint η (Set.univ : Set Y)) :
    ∃ U : Set Y, IsOpen U ∧ η ∈ U ∧
      ∀ y ∈ U, closedSubschemeFiberCover f g y ↔
        closedSubschemeFiberCover f g η := by
  let : IsNoetherian X :=
    { toIsLocallyNoetherian := LocallyOfFiniteType.isLocallyNoetherian f
      toCompactSpace := QuasiCompact.compactSpace_of_compactSpace f }
  have hc : IsClosed (⋃ i, Set.range (g i)) :=
    isClosed_iUnion_of_finite fun i => (g i).isClosedEmbedding.isClosed_range
  have hs : IsConstructible (f '' (⋃ i, Set.range (g i))ᶜ) :=
    f.isConstructible_image
      ((NoetherianSpace.isCompact _).isConstructible hc.isOpen_compl)
  obtain ⟨U, hU, hηU, hpattern⟩ := exists_open_constructible_membership hη hs
  exact ⟨U, hU, hηU, fun y hy =>
    (closedSubschemeFiberCover_iff f g y).trans
      ((not_congr (hpattern y hy)).trans (closedSubschemeFiberCover_iff f g η).symm)⟩

/-- In particular a finite closed cover of the generic fibre covers all nearby
 actual fibres. No flatness or separation hypothesis is needed. -/
theorem exists_open_closedSubschemeFiberCover_of_generic
    {ι : Type v} [Finite ι] [IsNoetherian Y]
    (f : X ⟶ Y) [LocallyOfFiniteType f] [QuasiCompact f]
    {Z : ι → Scheme.{u}} (g : ∀ i, Z i ⟶ X)
    [∀ i, IsClosedImmersion (g i)]
    {η : Y} (hη : IsGenericPoint η (Set.univ : Set Y))
    (hcover : closedSubschemeFiberCover f g η) :
    ∃ U : Set Y, IsOpen U ∧ η ∈ U ∧
      ∀ y ∈ U, closedSubschemeFiberCover f g y := by
  obtain ⟨U, hU, hηU, hpattern⟩ := exists_open_closedSubschemeFiberCover f g hη
  exact ⟨U, hU, hηU, fun y hy => (hpattern y hy).mpr hcover⟩

/-- One open neighbourhood preserves both coverage and all pairwise incidence
 predicates of the finite closed-subscheme family. -/
theorem exists_open_closedSubschemeFiberCover_and_incidence
    {ι : Type v} [Finite ι] [IsNoetherian Y]
    (f : X ⟶ Y) [LocallyOfFiniteType f] [QuasiCompact f]
    {Z : ι → Scheme.{u}} (g : ∀ i, Z i ⟶ X)
    [∀ i, IsClosedImmersion (g i)]
    {η : Y} (hη : IsGenericPoint η (Set.univ : Set Y)) :
    ∃ U : Set Y, IsOpen U ∧ η ∈ U ∧ ∀ y ∈ U,
      (closedSubschemeFiberCover f g y ↔ closedSubschemeFiberCover f g η) ∧
      ∀ i j, closedSubschemeFiberIncidence f g y i j ↔
        closedSubschemeFiberIncidence f g η i j := by
  obtain ⟨U, hU, hηU, hcover⟩ := exists_open_closedSubschemeFiberCover f g hη
  obtain ⟨V, hV, hηV, hinc⟩ := exists_open_closedSubschemeFiberIncidence f g hη
  exact ⟨U ∩ V, hU.inter hV, ⟨hηU, hηV⟩,
    fun y hy => ⟨hcover y hy.1, hinc y hy.2⟩⟩

end Langlands.AlgebraicGeometry.GenericImagePattern
