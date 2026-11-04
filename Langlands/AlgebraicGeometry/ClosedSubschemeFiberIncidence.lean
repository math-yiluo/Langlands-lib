import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.AlgebraicGeometry.Fiber
import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.Topology.Sober

/-! # Actual closed-subscheme incidence on fibres near a generic point -/

noncomputable section

universe u v

open Set Topology TopologicalSpace CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.GenericImagePattern

variable {A : Type u} [TopologicalSpace A] {η : A}

/-- Membership in one constructible set is constant on an open neighbourhood
of a point generic for the whole space. No Noetherian hypothesis is needed. -/
theorem exists_open_constructible_membership
    (hη : IsGenericPoint η (Set.univ : Set A)) {s : Set A}
    (hs : IsConstructible s) :
    ∃ U : Set A, IsOpen U ∧ η ∈ U ∧
      ∀ x ∈ U, (x ∈ s ↔ η ∈ s) := by
  induction hs using IsConstructible.empty_union_induction with
  | open_retrocompact U hU _ =>
    by_cases h : η ∈ U
    · exact ⟨U, hU, h, fun _ hx => ⟨fun _ => h, fun _ => hx⟩⟩
    · refine ⟨Set.univ, isOpen_univ, Set.mem_univ _, ?_⟩
      intro x _
      have hx : x ∉ U := by
        intro hx
        exact h ((hη.mem_open_set_iff hU).mpr ⟨x, Set.mem_univ _, hx⟩)
      simp only [hx, h]
  | union s hs t ht ihs iht =>
    obtain ⟨U, hU, hηU, hsU⟩ := ihs
    obtain ⟨V, hV, hηV, htV⟩ := iht
    exact ⟨U ∩ V, hU.inter hV, ⟨hηU, hηV⟩,
      fun x hx => or_congr (hsU x hx.1) (htV x hx.2)⟩
  | compl s hs ih =>
    obtain ⟨U, hU, hηU, hsU⟩ := ih
    exact ⟨U, hU, hηU, fun x hx => not_congr (hsU x hx)⟩

/-- A single open neighbourhood preserves the whole finite membership pattern. -/
theorem exists_open_finite_constructible_membership
    {ι : Type v} [Finite ι] (hη : IsGenericPoint η (Set.univ : Set A))
    (s : ι → Set A) (hs : ∀ i, IsConstructible (s i)) :
    ∃ U : Set A, IsOpen U ∧ η ∈ U ∧
      ∀ x ∈ U, ∀ i, (x ∈ s i ↔ η ∈ s i) := by
  classical
  choose U hU hηU hpattern using
    fun i => exists_open_constructible_membership hη (hs i)
  exact ⟨⋂ i, U i, isOpen_iInter_of_finite hU, Set.mem_iInter.mpr hηU,
    fun x hx i => hpattern i x (Set.mem_iInter.mp hx i)⟩

variable {X Y : Scheme.{u}}

/-- The underlying subset of the actual fibre cut out by a scheme mapping to X.
For a closed immersion, this is the image of its closed base change to the fibre. -/
def fiberSubschemeSets {ι : Type v} (f : X ⟶ Y)
    {Z : ι → Scheme.{u}} (g : ∀ i, Z i ⟶ X) (y : Y) (i : ι) :
    Set (f.fiber y) :=
  (f.fiberι y) ⁻¹' Set.range (g i)

/-- Incidence means intersection inside the actual scheme-theoretic fibre. -/
def closedSubschemeFiberIncidence {ι : Type v} (f : X ⟶ Y)
    {Z : ι → Scheme.{u}} (g : ∀ i, Z i ⟶ X) (y : Y) (i j : ι) : Prop :=
  (fiberSubschemeSets f g y i ∩ fiberSubschemeSets f g y j).Nonempty

theorem range_baseChange_eq_fiberSubschemeSets {ι : Type v} (f : X ⟶ Y)
    {Z : ι → Scheme.{u}} (g : ∀ i, Z i ⟶ X) (y : Y) (i : ι) :
    Set.range (pullback.snd (g i) (f.fiberι y)) = fiberSubschemeSets f g y i :=
  Scheme.Pullback.range_snd _ _

theorem preimage_fiberι_nonempty_iff (f : X ⟶ Y) (y : Y) (s : Set X) :
    ((f.fiberι y) ⁻¹' s).Nonempty ↔ y ∈ f '' s := by
  constructor
  · rintro ⟨z, hz⟩
    refine ⟨f.fiberι y z, hz, ?_⟩
    have hz' : f.fiberι y z ∈ f ⁻¹' {y} := by
      rw [← f.range_fiberι y]
      exact Set.mem_range_self z
    exact hz'
  · rintro ⟨x, hx, hxy⟩
    have hx' : x ∈ Set.range (f.fiberι y) := by
      rw [f.range_fiberι y]
      exact hxy
    obtain ⟨z, rfl⟩ := hx'
    exact ⟨z, hx⟩

/-- The actual fibre-intersection predicate is image membership on the base. -/
theorem closedSubschemeFiberIncidence_iff {ι : Type v} (f : X ⟶ Y)
    {Z : ι → Scheme.{u}} (g : ∀ i, Z i ⟶ X) (y : Y) (i j : ι) :
    closedSubschemeFiberIncidence f g y i j ↔
      y ∈ f '' (Set.range (g i) ∩ Set.range (g j)) := by
  unfold closedSubschemeFiberIncidence fiberSubschemeSets
  rw [← Set.preimage_inter]
  exact preimage_fiberι_nonempty_iff f y _

/-- Finite-type images over a Noetherian base have a constant finite membership
pattern on an open neighbourhood of its generic point. -/
theorem exists_open_finiteType_image_membership
    {ι : Type v} [Finite ι] [IsNoetherian Y]
    (Z : ι → Scheme.{u}) (g : ∀ i, Z i ⟶ Y)
    [∀ i, LocallyOfFiniteType (g i)] [∀ i, QuasiCompact (g i)]
    {η : Y} (hη : IsGenericPoint η (Set.univ : Set Y)) :
    ∃ U : Set Y, IsOpen U ∧ η ∈ U ∧
      ∀ y ∈ U, ∀ i, (y ∈ Set.range (g i) ↔ η ∈ Set.range (g i)) := by
  apply exists_open_finite_constructible_membership hη
  intro i
  simpa only [Set.image_univ] using
    (g i).isConstructible_image (s := Set.univ) IsConstructible.univ

/-- All intersections of a finite family of closed subschemes have the same
nonemptiness pattern as at the generic fibre after shrinking a Noetherian base.
This does not assert geometric irreducibility or identify fibre components. -/
theorem exists_open_closedSubschemeFiberIncidence
    {ι : Type v} [Finite ι] [IsNoetherian Y]
    (f : X ⟶ Y) [LocallyOfFiniteType f] [QuasiCompact f]
    {Z : ι → Scheme.{u}} (g : ∀ i, Z i ⟶ X)
    [∀ i, IsClosedImmersion (g i)]
    {η : Y} (hη : IsGenericPoint η (Set.univ : Set Y)) :
    ∃ U : Set Y, IsOpen U ∧ η ∈ U ∧
      ∀ y ∈ U, ∀ i j,
        closedSubschemeFiberIncidence f g y i j ↔
          closedSubschemeFiberIncidence f g η i j := by
  let : IsNoetherian X :=
    { toIsLocallyNoetherian := LocallyOfFiniteType.isLocallyNoetherian f
      toCompactSpace := QuasiCompact.compactSpace_of_compactSpace f }
  let s : ι × ι → Set Y :=
    fun ij => f '' (Set.range (g ij.1) ∩ Set.range (g ij.2))
  have hs : ∀ ij, IsConstructible (s ij) := by
    intro ij
    apply f.isConstructible_image
    have hc : IsClosed (Set.range (g ij.1) ∩ Set.range (g ij.2)) :=
      (g ij.1).isClosedEmbedding.isClosed_range.inter
        (g ij.2).isClosedEmbedding.isClosed_range
    exact ((NoetherianSpace.isCompact _).isConstructible hc.isOpen_compl).of_compl
  obtain ⟨U, hU, hηU, hpattern⟩ :=
    exists_open_finite_constructible_membership hη s hs
  refine ⟨U, hU, hηU, ?_⟩
  intro y hy i j
  rw [closedSubschemeFiberIncidence_iff, closedSubschemeFiberIncidence_iff]
  exact hpattern y hy (i, j)

end Langlands.AlgebraicGeometry.GenericImagePattern
