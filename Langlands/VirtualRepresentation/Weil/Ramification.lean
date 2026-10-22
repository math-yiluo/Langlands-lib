import Langlands.VirtualRepresentation.Weil.Local
import Langlands.LocalFactor.Ramification.Herbrand.Absolute
import Mathlib.RepresentationTheory.Invariants
import Mathlib.Data.Finset.Max

/-! # Intrinsic last-break labels and virtual Weil constituent extrema -/

noncomputable section

universe uF uV uW

namespace Langlands.VirtualRepresentation.LocalWeil.Ramification

open Langlands.Weil.Local Langlands.Ramification.Padic

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

/-- The actual upper ramification subgroup of the local Weil group. -/
def upperGroup (r : ℝ) : Subgroup (localWeilGroup F) :=
  (absoluteUpperRamificationGroup F r).comap (localProjection F).toMonoidHom

@[simp] theorem mem_upperGroup (r : ℝ) (w : localWeilGroup F) :
    w ∈ upperGroup F r ↔ localProjection F w ∈ absoluteUpperRamificationGroup F r := Iff.rfl

theorem upperGroup_antitone : Antitone (upperGroup F) := by
  intro r s hrs w hw
  exact absoluteUpperRamificationGroup_antitone F hrs hw

/-- The actual fixed subspace, with no finite-image presentation supplied. -/
def upperFixedSpace (A : FiniteRepresentation.{0, uF, uV} ℂ (localWeilGroup F))
    (r : ℝ) : Submodule ℂ A :=
  Representation.invariants (A.representation.comp (upperGroup F r).subtype)

@[simp] theorem mem_upperFixedSpace
    (A : FiniteRepresentation.{0, uF, uV} ℂ (localWeilGroup F)) (r : ℝ) (v : A) :
    v ∈ upperFixedSpace F A r ↔ ∀ w ∈ upperGroup F r, A.representation w v = v := by
  change (∀ w : upperGroup F r, A.representation w v = v) ↔ _
  exact Subtype.forall

/-- Triviality of the actual upper-group action. -/
def IsTrivialAt (A : FiniteRepresentation.{0, uF, uV} ℂ (localWeilGroup F))
    (r : ℝ) : Prop :=
  ∀ w ∈ upperGroup F r, A.representation w = 1

/-- Nonnegative parameters at which the actual upper group acts trivially. -/
def trivialityThresholds
    (A : FiniteRepresentation.{0, uF, uV} ℂ (localWeilGroup F)) : Set ℝ :=
  {r | 0 ≤ r ∧ IsTrivialAt F A r}

/-- The intrinsic last-break value. Real `sInf` is zero for an empty set;
nonemptiness on continuous objects is a separate arithmetic obligation. -/
def lastBreak (A : FiniteRepresentation.{0, uF, uV} ℂ (localWeilGroup F)) : ℝ :=
  sInf (trivialityThresholds F A)

theorem isTrivialAt_mono
    (A : FiniteRepresentation.{0, uF, uV} ℂ (localWeilGroup F))
    {r s : ℝ} (hrs : r ≤ s) (hr : IsTrivialAt F A r) : IsTrivialAt F A s :=
  fun w hw => hr w (upperGroup_antitone F hrs hw)

theorem trivialityThresholds_bddBelow
    (A : FiniteRepresentation.{0, uF, uV} ℂ (localWeilGroup F)) :
    BddBelow (trivialityThresholds F A) :=
  ⟨0, fun _ hr => hr.1⟩

/-- Nonnegativity includes the real-infimum empty-set convention. -/
theorem lastBreak_nonneg
    (A : FiniteRepresentation.{0, uF, uV} ℂ (localWeilGroup F)) :
    0 ≤ lastBreak F A :=
  Real.sInf_nonneg (fun _ hr => hr.1)

theorem lastBreak_eq_zero_of_thresholds_empty
    (A : FiniteRepresentation.{0, uF, uV} ℂ (localWeilGroup F))
    (h : trivialityThresholds F A = ∅) : lastBreak F A = 0 := by
  rw [lastBreak, h, Real.sInf_empty]

theorem lastBreak_le_of_mem
    (A : FiniteRepresentation.{0, uF, uV} ℂ (localWeilGroup F))
    {r : ℝ} (hr : r ∈ trivialityThresholds F A) : lastBreak F A ≤ r :=
  csInf_le (trivialityThresholds_bddBelow F A) hr

/-- Invertible intertwiners preserve triviality, even across carrier universes. -/
theorem isTrivialAt_equiv
    {A : FiniteRepresentation.{0, uF, uV} ℂ (localWeilGroup F)}
    {B : FiniteRepresentation.{0, uF, uW} ℂ (localWeilGroup F)}
    (e : FiniteRepresentation.Equiv A B) (r : ℝ) :
    IsTrivialAt F A r ↔ IsTrivialAt F B r := by
  have transfer {A : FiniteRepresentation.{0, uF, uV} ℂ (localWeilGroup F)}
      {B : FiniteRepresentation.{0, uF, uW} ℂ (localWeilGroup F)}
      (e : FiniteRepresentation.Equiv A B) (h : IsTrivialAt F A r) :
      IsTrivialAt F B r := by
    intro w hw
    apply LinearMap.ext
    intro v
    obtain ⟨a, rfl⟩ := e.toLinearEquiv.surjective v
    change B.representation w (e a) = e a
    calc
      B.representation w (e a) = e (A.representation w a) :=
        (Representation.IntertwiningMap.isIntertwining A.representation B.representation
          e.toIntertwiningMap w a).symm
      _ = e a := by rw [h w hw]; rfl
  constructor
  · exact transfer e
  · intro h w hw
    apply LinearMap.ext
    intro v
    apply e.toLinearEquiv.injective
    change e (A.representation w v) = e v
    calc
      e (A.representation w v) = B.representation w (e v) :=
        Representation.IntertwiningMap.isIntertwining A.representation B.representation
          e.toIntertwiningMap w v
      _ = e v := by rw [h w hw]; rfl

theorem trivialityThresholds_equiv
    {A : FiniteRepresentation.{0, uF, uV} ℂ (localWeilGroup F)}
    {B : FiniteRepresentation.{0, uF, uW} ℂ (localWeilGroup F)}
    (e : FiniteRepresentation.Equiv A B) :
    trivialityThresholds F A = trivialityThresholds F B := by
  ext r
  exact and_congr_right (fun _ => isTrivialAt_equiv F e r)

theorem lastBreak_equiv
    {A : FiniteRepresentation.{0, uF, uV} ℂ (localWeilGroup F)}
    {B : FiniteRepresentation.{0, uF, uW} ℂ (localWeilGroup F)}
    (e : FiniteRepresentation.Equiv A B) : lastBreak F A = lastBreak F B :=
  congrArg sInf (trivialityThresholds_equiv F e)

/-- The last break descends to genuine representation isomorphism classes. -/
def classLastBreak : FiniteRepresentation.IsomorphismClasses.{0, uF, uV}
    ℂ (localWeilGroup F) → ℝ :=
  Quotient.lift (lastBreak F) (fun _ _ ⟨e⟩ => lastBreak_equiv F e)

@[simp] theorem classLastBreak_classOf
    (A : FiniteRepresentation.{0, uF, uV} ℂ (localWeilGroup F)) :
    classLastBreak F (FiniteRepresentation.classOf A) = lastBreak F A := rfl

theorem classLastBreak_nonneg
    (c : FiniteRepresentation.IsomorphismClasses.{0, uF, uV} ℂ (localWeilGroup F)) :
    0 ≤ classLastBreak F c :=
  Quotient.inductionOn c (lastBreak_nonneg F)

/-- The intrinsic label of an actual continuous irreducible positive-rank class. -/
def breakLabel (b : Basis.{uF, uV} F) : ℝ :=
  classLastBreak F (Weil.underlyingClass (localWeilGroup F) b)

@[simp] theorem breakLabel_basisClass
    (A : FiniteRepresentation.{0, uF, uV} ℂ (localWeilGroup F))
    (hc : A.IsContinuous) (hi : A.IsIrreducible) (n : ℕ+) (hn : A.rank = (n : ℕ)) :
    breakLabel F (basisClass A hc hi n hn) = lastBreak F A := rfl

theorem breakLabel_nonneg (b : Basis.{uF, uV} F) : 0 ≤ breakLabel F b :=
  classLastBreak_nonneg F _

/-- Labels of the nonzero signed Weil coefficients after class cancellation.
This is a set image, not a pushforward that sums coefficients at equal labels. -/
def breakSupport (x : Lattice.{uF, uV} F) : Finset ℝ :=
  x.support.image (breakLabel F)

@[simp] theorem mem_breakSupport (x : Lattice.{uF, uV} F) (r : ℝ) :
    r ∈ breakSupport F x ↔ ∃ b, x b ≠ 0 ∧ breakLabel F b = r := by
  classical
  simp [breakSupport, Finsupp.mem_support_iff]

@[simp] theorem breakSupport_nonempty_iff (x : Lattice.{uF, uV} F) :
    (breakSupport F x).Nonempty ↔ x ≠ 0 := by
  classical
  simp [breakSupport, Finsupp.support_nonempty_iff]

@[simp] theorem breakSupport_zero : breakSupport F (0 : Lattice.{uF, uV} F) = ∅ := by
  classical
  simp [breakSupport]

theorem breakSupport_nonneg (x : Lattice.{uF, uV} F) {r : ℝ}
    (hr : r ∈ breakSupport F x) : 0 ≤ r := by
  obtain ⟨b, _, rfl⟩ := (mem_breakSupport F x r).mp hr
  exact breakLabel_nonneg F b

/-- Minimum only for explicitly nonempty constituent support. -/
def minimumBreak (x : Lattice.{uF, uV} F) (h : (breakSupport F x).Nonempty) : ℝ :=
  (breakSupport F x).min' h

/-- Maximum only for explicitly nonempty constituent support. -/
def maximumBreak (x : Lattice.{uF, uV} F) (h : (breakSupport F x).Nonempty) : ℝ :=
  (breakSupport F x).max' h

/-- Every surviving Weil constituent has label at least `a`. -/
def AllBreaksAtLeast (x : Lattice.{uF, uV} F) (a : ℝ) : Prop :=
  ∀ b, x b ≠ 0 → a ≤ breakLabel F b

/-- Every surviving Weil constituent has label strictly less than `b`.
This predicate is meaningful and vacuous on zero virtual input. -/
def AllBreaksBelow (x : Lattice.{uF, uV} F) (b : ℝ) : Prop :=
  ∀ c, x c ≠ 0 → breakLabel F c < b

/-- All surviving constituent labels are positive; vacuous on zero. -/
def PositiveBreakSupport (x : Lattice.{uF, uV} F) : Prop :=
  ∀ b, x b ≠ 0 → 0 < breakLabel F b

theorem allBreaksAtLeast_iff_support (x : Lattice.{uF, uV} F) (a : ℝ) :
    AllBreaksAtLeast F x a ↔ ∀ r ∈ breakSupport F x, a ≤ r := by
  simp only [AllBreaksAtLeast, mem_breakSupport]
  constructor
  · rintro h r ⟨b, hb, rfl⟩
    exact h b hb
  · intro h b hb
    exact h _ ⟨b, hb, rfl⟩

theorem allBreaksBelow_iff_support (x : Lattice.{uF, uV} F) (b : ℝ) :
    AllBreaksBelow F x b ↔ ∀ r ∈ breakSupport F x, r < b := by
  simp only [AllBreaksBelow, mem_breakSupport]
  constructor
  · rintro h r ⟨c, hc, rfl⟩
    exact h c hc
  · intro h c hc
    exact h _ ⟨c, hc, rfl⟩

theorem allBreaksAtLeast_iff_le_minimumBreak (x : Lattice.{uF, uV} F)
    (h : (breakSupport F x).Nonempty) (a : ℝ) :
    AllBreaksAtLeast F x a ↔ a ≤ minimumBreak F x h := by
  rw [allBreaksAtLeast_iff_support, minimumBreak, Finset.le_min'_iff]

theorem allBreaksBelow_iff_maximumBreak_lt (x : Lattice.{uF, uV} F)
    (h : (breakSupport F x).Nonempty) (b : ℝ) :
    AllBreaksBelow F x b ↔ maximumBreak F x h < b := by
  rw [allBreaksBelow_iff_support, maximumBreak, Finset.max'_lt_iff]

theorem positiveBreakSupport_iff_minimumBreak_pos (x : Lattice.{uF, uV} F)
    (h : (breakSupport F x).Nonempty) :
    PositiveBreakSupport F x ↔ 0 < minimumBreak F x h := by
  rw [minimumBreak, Finset.lt_min'_iff]
  unfold PositiveBreakSupport
  simp only [mem_breakSupport]
  constructor
  · rintro h r ⟨b, hb, rfl⟩
    exact h b hb
  · intro h b hb
    exact h _ ⟨b, hb, rfl⟩

@[simp] theorem allBreaksAtLeast_zero (a : ℝ) :
    AllBreaksAtLeast F (0 : Lattice.{uF, uV} F) a := by
  simp [AllBreaksAtLeast]

@[simp] theorem allBreaksBelow_zero (b : ℝ) :
    AllBreaksBelow F (0 : Lattice.{uF, uV} F) b := by
  simp [AllBreaksBelow]

@[simp] theorem positiveBreakSupport_zero :
    PositiveBreakSupport F (0 : Lattice.{uF, uV} F) := by
  simp [PositiveBreakSupport]

theorem allBreaksAtLeast_nonneg (x : Lattice.{uF, uV} F) : AllBreaksAtLeast F x 0 :=
  fun b _ => breakLabel_nonneg F b

theorem minimumBreak_nonneg (x : Lattice.{uF, uV} F)
    (h : (breakSupport F x).Nonempty) : 0 ≤ minimumBreak F x h :=
  (allBreaksAtLeast_iff_le_minimumBreak F x h 0).mp (allBreaksAtLeast_nonneg F x)

theorem minimumBreak_le_maximumBreak (x : Lattice.{uF, uV} F)
    (h : (breakSupport F x).Nonempty) : minimumBreak F x h ≤ maximumBreak F x h :=
  Finset.min'_le_max' _ h

theorem maximumBreak_nonneg (x : Lattice.{uF, uV} F)
    (h : (breakSupport F x).Nonempty) : 0 ≤ maximumBreak F x h :=
  (minimumBreak_nonneg F x h).trans (minimumBreak_le_maximumBreak F x h)

/-- A strict upper bound on a nonzero virtual element is necessarily positive. -/
theorem pos_of_allBreaksBelow (x : Lattice.{uF, uV} F) (hx : x ≠ 0)
    {b : ℝ} (hb : AllBreaksBelow F x b) : 0 < b := by
  have h := (breakSupport_nonempty_iff F x).mpr hx
  exact (maximumBreak_nonneg F x h).trans_lt
    ((allBreaksBelow_iff_maximumBreak_lt F x h b).mp hb)

end Langlands.VirtualRepresentation.LocalWeil.Ramification
