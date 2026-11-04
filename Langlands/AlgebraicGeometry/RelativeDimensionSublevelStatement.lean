import Langlands.AlgebraicGeometry.RelativeDimensionLoci
import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import Mathlib.Data.ENat.SuccOrder

/-! # Source-qualified relative-dimension sublevel properties -/

universe u v

open Set Order Topology TopologicalSpace CategoryTheory AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.SchemeFiberGeometry

/-- The openness assertion of Stacks Lemma 29.29.4, for every natural bound. -/
def RelativeDimensionSublevelOpenness : Prop :=
  ∀ {X Y : Scheme.{u}} (f : X ⟶ Y) [LocallyOfFiniteType f] (n : ℕ),
    IsOpen (relativeDimensionSublevel f n)

/-- The retrocompactness assertion of Stacks Lemma 29.29.6. -/
def RelativeDimensionSublevelRetrocompactness : Prop :=
  ∀ {X Y : Scheme.{u}} (f : X ⟶ Y) [LocallyOfFinitePresentation f] (n : ℕ),
    IsRetrocompact (relativeDimensionSublevel f n)

/-- The two general sublevel assertions, retaining their different hypotheses. -/
def RelativeDimensionSublevelProperties : Prop :=
  RelativeDimensionSublevelOpenness.{u} ∧ RelativeDimensionSublevelRetrocompactness.{u}

/-- The local dimension at an actual point cannot be negative. -/
theorem topologicalKrullDimAt_nonneg {T : Type v} [TopologicalSpace T] (x : T) :
    0 ≤ topologicalKrullDimAt x := by
  obtain ⟨U, hxU, hU⟩ := exists_open_topologicalKrullDim_eq_at x
  rw [← hU]
  exact Order.krullDim_nonneg_iff.mpr
    ⟨⟨closure {⟨x, hxU⟩}, isIrreducible_singleton.closure, isClosed_closure⟩⟩

theorem relativeTopologicalKrullDimAt_nonneg
    {X Y : Scheme.{u}} (f : X ⟶ Y) (x : X) :
    0 ≤ relativeTopologicalKrullDimAt f x :=
  topologicalKrullDimAt_nonneg (f.asFiber x)

/-- At bound zero, unequal dimension is exactly the complement of the sublevel. -/
theorem relativeDimension_ne_zero_eq_compl
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    {x | relativeTopologicalKrullDimAt f x ≠ 0} =
      (relativeDimensionSublevel f 0)ᶜ := by
  ext x
  change relativeTopologicalKrullDimAt f x ≠ 0 ↔
    ¬ relativeTopologicalKrullDimAt f x ≤ 0
  exact not_congr (le_antisymm_iff.trans
    (and_iff_left (relativeTopologicalKrullDimAt_nonneg f x)))

/-- At a positive natural bound, unequal dimension is a Boolean combination
of the two consecutive actual sublevels. -/
theorem relativeDimension_ne_succ_eq_union
    {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ) :
    {x | relativeTopologicalKrullDimAt f x ≠ (n + 1 : ℕ)} =
      relativeDimensionSublevel f n ∪ (relativeDimensionSublevel f (n + 1))ᶜ := by
  ext x
  change relativeTopologicalKrullDimAt f x ≠ (n + 1 : ℕ) ↔
    relativeTopologicalKrullDimAt f x ≤ (n : WithBot ℕ∞) ∨
      ¬ relativeTopologicalKrullDimAt f x ≤ (n + 1 : ℕ)
  rw [ne_iff_lt_or_gt, not_le, Nat.cast_add, Nat.cast_one,
    ENat.WithBot.lt_add_one_iff]

/-- Constructible sublevels imply constructibility of the actual exceptional
source set; no boundedness or equidimensionality premise is needed. -/
theorem isConstructible_relativeDimension_ne_of_sublevels
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    (h : ∀ n, IsConstructible (relativeDimensionSublevel f n)) (d : ℕ) :
    IsConstructible {x | relativeTopologicalKrullDimAt f x ≠ (d : WithBot ℕ∞)} := by
  cases d with
  | zero =>
    simpa only [Nat.cast_zero, relativeDimension_ne_zero_eq_compl] using (h 0).compl
  | succ n =>
    rw [relativeDimension_ne_succ_eq_union]
    exact (h n).union (h (n + 1)).compl

/-- Chevalley and the complement-image comparison turn actual constructible
source sublevels into the pure-dimension locus on a qcqs target. -/
theorem isConstructible_pureDimensionFiberLocus_of_sublevels
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    [LocallyOfFinitePresentation f] [QuasiCompact f]
    [CompactSpace Y] [QuasiSeparatedSpace Y]
    (h : ∀ n, IsConstructible (relativeDimensionSublevel f n)) (d : ℕ) :
    IsConstructible (pureDimensionFiberLocus d f) := by
  rw [pureDimensionFiberLocus_eq_compl_image]
  exact (f.isConstructible_image
    (isConstructible_relativeDimension_ne_of_sublevels f h d)).compl

/-- The generic sublevel properties suffice for pure-dimension locus
constructibility in the qcqs finite-presentation model setup. -/
theorem isConstructible_pureDimensionFiberLocus_of_sublevelProperties
    (h : RelativeDimensionSublevelProperties.{u})
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    [LocallyOfFinitePresentation f] [QuasiCompact f]
    [CompactSpace Y] [QuasiSeparatedSpace Y] (d : ℕ) :
    IsConstructible (pureDimensionFiberLocus d f) := by
  exact isConstructible_pureDimensionFiberLocus_of_sublevels f
    (fun n => IsRetrocompact.isConstructible (h.1 f n) (h.2 f n)) d

end Langlands.AlgebraicGeometry.SchemeFiberGeometry
