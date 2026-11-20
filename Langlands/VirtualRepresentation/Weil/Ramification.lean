import Langlands.VirtualRepresentation.Weil.Local
import Langlands.LocalFactor.Ramification.Herbrand.Absolute
import Mathlib.RepresentationTheory.Invariants
import Mathlib.Data.Finset.Max

/-!
# Intrinsic last-break labels and virtual Weil constituent extrema

The constructions apply to nonarchimedean local fields of any characteristic.
The p-adic interface specializes the same spectral construction.
-/

noncomputable section

universe u₀ uK uΩ uF uV uW

namespace Langlands.VirtualRepresentation.LocalWeil.SepClosed.Ramification.Spectral

variable (K₀ : Type u₀) [NontriviallyNormedField K₀] [IsUltrametricDist K₀]
    [CompleteSpace K₀] [ValuativeRel K₀] [LocallyCompactSpace K₀]
variable (K : Type uK) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    (Ω : Type uΩ) [Field Ω] [Algebra K Ω]
    [Algebra K₀ K] [FiniteDimensional K₀ K]
    [Algebra K₀ Ω] [IsScalarTower K₀ K Ω] [IsSepClosure K Ω]
    (hbase : ∀ a b : K₀, ‖a‖ ≤ ‖b‖ ↔ ValuativeRel.vle a b)

local notation "W" =>
  (@Weil.Local.SepClosed.localWeilGroup K _ _ _ _ Ω _ _ _ (IsSepClosure.sep_closed K))

local notation "weilProjection" =>
  (@Weil.Local.SepClosed.localProjection K _ _ _ _ Ω _ _ _ (IsSepClosure.sep_closed K))

/-- The actual upper ramification subgroup of the local Weil group. -/
def upperGroup (r : ℝ) : Subgroup W :=
  (Langlands.Ramification.Local.absoluteUpperRamificationGroup K₀ K Ω hbase r).comap
    (weilProjection).toMonoidHom

@[simp] theorem mem_upperGroup (r : ℝ) (w : W) :
    w ∈ upperGroup K₀ K Ω hbase r ↔
      weilProjection w ∈
        Langlands.Ramification.Local.absoluteUpperRamificationGroup K₀ K Ω hbase r :=
  Iff.rfl

theorem upperGroup_antitone : Antitone (upperGroup K₀ K Ω hbase) := by
  intro r s hrs w hw
  exact Langlands.Ramification.Local.absoluteUpperRamificationGroup_antitone K₀ K Ω hbase hrs hw

/-- The actual fixed subspace, with no finite-image presentation supplied. -/
def upperFixedSpace (A : FiniteRepresentation.{0, uΩ, uV} ℂ W)
    (r : ℝ) : Submodule ℂ A :=
  Representation.invariants (A.representation.comp (upperGroup K₀ K Ω hbase r).subtype)

@[simp] theorem mem_upperFixedSpace
    (A : FiniteRepresentation.{0, uΩ, uV} ℂ W) (r : ℝ) (v : A) :
    v ∈ upperFixedSpace K₀ K Ω hbase A r ↔
      ∀ w ∈ upperGroup K₀ K Ω hbase r, A.representation w v = v := by
  change (∀ w : upperGroup K₀ K Ω hbase r, A.representation w v = v) ↔ _
  exact Subtype.forall

/-- Triviality of the actual upper-group action. -/
def IsTrivialAt (A : FiniteRepresentation.{0, uΩ, uV} ℂ W)
    (r : ℝ) : Prop :=
  ∀ w ∈ upperGroup K₀ K Ω hbase r, A.representation w = 1

/-- Nonnegative parameters at which the actual upper group acts trivially. -/
def trivialityThresholds
    (A : FiniteRepresentation.{0, uΩ, uV} ℂ W) : Set ℝ :=
  {r | 0 ≤ r ∧ IsTrivialAt K₀ K Ω hbase A r}

/-- The real infimum of the nonnegative triviality thresholds, with value
zero on the empty set. -/
def lastBreak (A : FiniteRepresentation.{0, uΩ, uV} ℂ W) : ℝ :=
  sInf (trivialityThresholds K₀ K Ω hbase A)

theorem isTrivialAt_mono
    (A : FiniteRepresentation.{0, uΩ, uV} ℂ W)
    {r s : ℝ} (hrs : r ≤ s) (hr : IsTrivialAt K₀ K Ω hbase A r) : IsTrivialAt K₀ K Ω hbase A s :=
  fun w hw => hr w (upperGroup_antitone K₀ K Ω hbase hrs hw)

theorem trivialityThresholds_bddBelow
    (A : FiniteRepresentation.{0, uΩ, uV} ℂ W) :
    BddBelow (trivialityThresholds K₀ K Ω hbase A) :=
  ⟨0, fun _ hr => hr.1⟩

/-- Nonnegativity includes the real-infimum empty-set convention. -/
theorem lastBreak_nonneg
    (A : FiniteRepresentation.{0, uΩ, uV} ℂ W) :
    0 ≤ lastBreak K₀ K Ω hbase A :=
  Real.sInf_nonneg (fun _ hr => hr.1)

theorem lastBreak_eq_zero_of_thresholds_empty
    (A : FiniteRepresentation.{0, uΩ, uV} ℂ W)
    (h : trivialityThresholds K₀ K Ω hbase A = ∅) : lastBreak K₀ K Ω hbase A = 0 := by
  rw [lastBreak, h, Real.sInf_empty]

theorem lastBreak_le_of_mem
    (A : FiniteRepresentation.{0, uΩ, uV} ℂ W)
    {r : ℝ} (hr : r ∈ trivialityThresholds K₀ K Ω hbase A) : lastBreak K₀ K Ω hbase A ≤ r :=
  csInf_le (trivialityThresholds_bddBelow K₀ K Ω hbase A) hr

/-- Invertible intertwiners preserve triviality, even across carrier universes. -/
theorem isTrivialAt_equiv
    {A : FiniteRepresentation.{0, uΩ, uV} ℂ W}
    {B : FiniteRepresentation.{0, uΩ, uW} ℂ W}
    (e : FiniteRepresentation.Equiv A B) (r : ℝ) :
    IsTrivialAt K₀ K Ω hbase A r ↔ IsTrivialAt K₀ K Ω hbase B r := by
  have transfer {A : FiniteRepresentation.{0, uΩ, uV} ℂ W}
      {B : FiniteRepresentation.{0, uΩ, uW} ℂ W}
      (e : FiniteRepresentation.Equiv A B) (h : IsTrivialAt K₀ K Ω hbase A r) :
      IsTrivialAt K₀ K Ω hbase B r := by
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
    {A : FiniteRepresentation.{0, uΩ, uV} ℂ W}
    {B : FiniteRepresentation.{0, uΩ, uW} ℂ W}
    (e : FiniteRepresentation.Equiv A B) :
    trivialityThresholds K₀ K Ω hbase A = trivialityThresholds K₀ K Ω hbase B := by
  ext r
  exact and_congr_right (fun _ => isTrivialAt_equiv K₀ K Ω hbase e r)

theorem lastBreak_equiv
    {A : FiniteRepresentation.{0, uΩ, uV} ℂ W}
    {B : FiniteRepresentation.{0, uΩ, uW} ℂ W}
    (e : FiniteRepresentation.Equiv A B) : lastBreak K₀ K Ω hbase A = lastBreak K₀ K Ω hbase B :=
  congrArg sInf (trivialityThresholds_equiv K₀ K Ω hbase e)

/-- The last break descends to genuine representation isomorphism classes. -/
def classLastBreak : FiniteRepresentation.IsomorphismClasses.{0, uΩ, uV}
    ℂ W → ℝ :=
  Quotient.lift (lastBreak K₀ K Ω hbase) (fun _ _ ⟨e⟩ => lastBreak_equiv K₀ K Ω hbase e)

@[simp] theorem classLastBreak_classOf
    (A : FiniteRepresentation.{0, uΩ, uV} ℂ W) :
    classLastBreak K₀ K Ω hbase (FiniteRepresentation.classOf A) = lastBreak K₀ K Ω hbase A := rfl

theorem classLastBreak_nonneg
    (c : FiniteRepresentation.IsomorphismClasses.{0, uΩ, uV} ℂ W) :
    0 ≤ classLastBreak K₀ K Ω hbase c :=
  Quotient.inductionOn c (lastBreak_nonneg K₀ K Ω hbase)

/-- The intrinsic label of an actual continuous irreducible positive-rank class. -/
def breakLabel (b : Basis.{uK, uΩ, uV} K Ω) : ℝ :=
  classLastBreak K₀ K Ω hbase (Weil.underlyingClass W b)

@[simp] theorem breakLabel_basisClass
    (A : FiniteRepresentation.{0, uΩ, uV} ℂ W)
    (hc : A.IsContinuous) (hi : A.IsIrreducible) (n : ℕ+) (hn : A.rank = (n : ℕ)) :
    breakLabel K₀ K Ω hbase (Weil.basisClass A hc hi n hn) = lastBreak K₀ K Ω hbase A := rfl

theorem breakLabel_nonneg (b : Basis.{uK, uΩ, uV} K Ω) : 0 ≤ breakLabel K₀ K Ω hbase b :=
  classLastBreak_nonneg K₀ K Ω hbase _

/-- Labels of the nonzero signed Weil coefficients after class cancellation.
Repeated numerical labels occur once in the image. -/
def breakSupport (x : Lattice.{uK, uΩ, uV} K Ω) : Finset ℝ :=
  x.support.image (breakLabel K₀ K Ω hbase)

@[simp] theorem mem_breakSupport (x : Lattice.{uK, uΩ, uV} K Ω) (r : ℝ) :
    r ∈ breakSupport K₀ K Ω hbase x ↔ ∃ b, x b ≠ 0 ∧ breakLabel K₀ K Ω hbase b = r := by
  classical
  simp [breakSupport, Finsupp.mem_support_iff]

@[simp] theorem breakSupport_nonempty_iff (x : Lattice.{uK, uΩ, uV} K Ω) :
    (breakSupport K₀ K Ω hbase x).Nonempty ↔ x ≠ 0 := by
  classical
  simp [breakSupport, Finsupp.support_nonempty_iff]

@[simp] theorem breakSupport_zero :
    breakSupport K₀ K Ω hbase (0 : Lattice.{uK, uΩ, uV} K Ω) = ∅ := by
  classical
  simp [breakSupport]

theorem breakSupport_nonneg (x : Lattice.{uK, uΩ, uV} K Ω) {r : ℝ}
    (hr : r ∈ breakSupport K₀ K Ω hbase x) : 0 ≤ r := by
  obtain ⟨b, _, rfl⟩ := (mem_breakSupport K₀ K Ω hbase x r).mp hr
  exact breakLabel_nonneg K₀ K Ω hbase b

/-- Minimum only for explicitly nonempty constituent support. -/
def minimumBreak (x : Lattice.{uK, uΩ, uV} K Ω) (h : (breakSupport K₀ K Ω hbase x).Nonempty) : ℝ :=
  (breakSupport K₀ K Ω hbase x).min' h

/-- Maximum only for explicitly nonempty constituent support. -/
def maximumBreak (x : Lattice.{uK, uΩ, uV} K Ω) (h : (breakSupport K₀ K Ω hbase x).Nonempty) : ℝ :=
  (breakSupport K₀ K Ω hbase x).max' h

/-- Every surviving Weil constituent has label at least `a`. -/
def AllBreaksAtLeast (x : Lattice.{uK, uΩ, uV} K Ω) (a : ℝ) : Prop :=
  ∀ b, x b ≠ 0 → a ≤ breakLabel K₀ K Ω hbase b

/-- Every surviving Weil constituent has label strictly less than `b`.
This predicate is meaningful and vacuous on zero virtual input. -/
def AllBreaksBelow (x : Lattice.{uK, uΩ, uV} K Ω) (b : ℝ) : Prop :=
  ∀ c, x c ≠ 0 → breakLabel K₀ K Ω hbase c < b

/-- All surviving constituent labels are positive; vacuous on zero. -/
def PositiveBreakSupport (x : Lattice.{uK, uΩ, uV} K Ω) : Prop :=
  ∀ b, x b ≠ 0 → 0 < breakLabel K₀ K Ω hbase b

theorem allBreaksAtLeast_iff_support (x : Lattice.{uK, uΩ, uV} K Ω) (a : ℝ) :
    AllBreaksAtLeast K₀ K Ω hbase x a ↔ ∀ r ∈ breakSupport K₀ K Ω hbase x, a ≤ r := by
  simp only [AllBreaksAtLeast, mem_breakSupport]
  constructor
  · rintro h r ⟨b, hb, rfl⟩
    exact h b hb
  · intro h b hb
    exact h _ ⟨b, hb, rfl⟩

theorem allBreaksBelow_iff_support (x : Lattice.{uK, uΩ, uV} K Ω) (b : ℝ) :
    AllBreaksBelow K₀ K Ω hbase x b ↔ ∀ r ∈ breakSupport K₀ K Ω hbase x, r < b := by
  simp only [AllBreaksBelow, mem_breakSupport]
  constructor
  · rintro h r ⟨c, hc, rfl⟩
    exact h c hc
  · intro h c hc
    exact h _ ⟨c, hc, rfl⟩

theorem allBreaksAtLeast_iff_le_minimumBreak (x : Lattice.{uK, uΩ, uV} K Ω)
    (h : (breakSupport K₀ K Ω hbase x).Nonempty) (a : ℝ) :
    AllBreaksAtLeast K₀ K Ω hbase x a ↔ a ≤ minimumBreak K₀ K Ω hbase x h := by
  rw [allBreaksAtLeast_iff_support, minimumBreak, Finset.le_min'_iff]

theorem allBreaksBelow_iff_maximumBreak_lt (x : Lattice.{uK, uΩ, uV} K Ω)
    (h : (breakSupport K₀ K Ω hbase x).Nonempty) (b : ℝ) :
    AllBreaksBelow K₀ K Ω hbase x b ↔ maximumBreak K₀ K Ω hbase x h < b := by
  rw [allBreaksBelow_iff_support, maximumBreak, Finset.max'_lt_iff]

theorem positiveBreakSupport_iff_minimumBreak_pos (x : Lattice.{uK, uΩ, uV} K Ω)
    (h : (breakSupport K₀ K Ω hbase x).Nonempty) :
    PositiveBreakSupport K₀ K Ω hbase x ↔ 0 < minimumBreak K₀ K Ω hbase x h := by
  rw [minimumBreak, Finset.lt_min'_iff]
  unfold PositiveBreakSupport
  simp only [mem_breakSupport]
  constructor
  · rintro h r ⟨b, hb, rfl⟩
    exact h b hb
  · intro h b hb
    exact h _ ⟨b, hb, rfl⟩

@[simp] theorem allBreaksAtLeast_zero (a : ℝ) :
    AllBreaksAtLeast K₀ K Ω hbase (0 : Lattice.{uK, uΩ, uV} K Ω) a := by
  simp [AllBreaksAtLeast]

@[simp] theorem allBreaksBelow_zero (b : ℝ) :
    AllBreaksBelow K₀ K Ω hbase (0 : Lattice.{uK, uΩ, uV} K Ω) b := by
  simp [AllBreaksBelow]

@[simp] theorem positiveBreakSupport_zero :
    PositiveBreakSupport K₀ K Ω hbase (0 : Lattice.{uK, uΩ, uV} K Ω) := by
  simp [PositiveBreakSupport]

theorem allBreaksAtLeast_nonneg (x : Lattice.{uK, uΩ, uV} K Ω) :
    AllBreaksAtLeast K₀ K Ω hbase x 0 :=
  fun b _ => breakLabel_nonneg K₀ K Ω hbase b

theorem minimumBreak_nonneg (x : Lattice.{uK, uΩ, uV} K Ω)
    (h : (breakSupport K₀ K Ω hbase x).Nonempty) : 0 ≤ minimumBreak K₀ K Ω hbase x h :=
  (allBreaksAtLeast_iff_le_minimumBreak K₀ K Ω hbase x h 0).mp
    (allBreaksAtLeast_nonneg K₀ K Ω hbase x)

theorem minimumBreak_le_maximumBreak (x : Lattice.{uK, uΩ, uV} K Ω)
    (h : (breakSupport K₀ K Ω hbase x).Nonempty) :
    minimumBreak K₀ K Ω hbase x h ≤ maximumBreak K₀ K Ω hbase x h :=
  Finset.min'_le_max' _ h

theorem maximumBreak_nonneg (x : Lattice.{uK, uΩ, uV} K Ω)
    (h : (breakSupport K₀ K Ω hbase x).Nonempty) : 0 ≤ maximumBreak K₀ K Ω hbase x h :=
  (minimumBreak_nonneg K₀ K Ω hbase x h).trans (minimumBreak_le_maximumBreak K₀ K Ω hbase x h)

/-- A strict upper bound on a nonzero virtual element is necessarily positive. -/
theorem pos_of_allBreaksBelow (x : Lattice.{uK, uΩ, uV} K Ω) (hx : x ≠ 0)
    {b : ℝ} (hb : AllBreaksBelow K₀ K Ω hbase x b) : 0 < b := by
  have h := (breakSupport_nonempty_iff K₀ K Ω hbase x).mpr hx
  exact (maximumBreak_nonneg K₀ K Ω hbase x h).trans_lt
    ((allBreaksBelow_iff_maximumBreak_lt K₀ K Ω hbase x h b).mp hb)

end Langlands.VirtualRepresentation.LocalWeil.SepClosed.Ramification.Spectral

namespace Langlands.VirtualRepresentation.LocalWeil.SepClosed.Ramification

variable (K : Type uK) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    (Ω : Type uΩ) [Field Ω] [Algebra K Ω] [IsSepClosure K Ω]

local notation "W" =>
  (@Weil.Local.SepClosed.localWeilGroup K _ _ _ _ Ω _ _ _ (IsSepClosure.sep_closed K))

local notation "weilProjection" =>
  (@Weil.Local.SepClosed.localProjection K _ _ _ _ Ω _ _ _ (IsSepClosure.sep_closed K))

local instance : NontriviallyNormedField K := LocalGalois.localNormedField K
local instance : IsUltrametricDist K := LocalGalois.localNormedField_ultrametric K
local instance : CompleteSpace K := LocalGalois.localNormedField_complete K

private theorem baseNorm_compatible (a b : K) : ‖a‖ ≤ ‖b‖ ↔ ValuativeRel.vle a b :=
  (LocalGalois.localNormedField_le K a b).trans
    (ValuativeRel.valuation K).vle_iff_le.symm

/-- The local-norm specialization of `Spectral.upperGroup`. -/
abbrev upperGroup (r : ℝ) : Subgroup W :=
  Spectral.upperGroup K K Ω (baseNorm_compatible K) r

@[simp] theorem mem_upperGroup (r : ℝ) (w : W) :
    w ∈ upperGroup K Ω r ↔
      weilProjection w ∈ Langlands.Ramification.Local.localAbsoluteUpperRamificationGroup K Ω r :=
  Iff.rfl

theorem upperGroup_antitone : Antitone (upperGroup K Ω) :=
  Spectral.upperGroup_antitone K K Ω (baseNorm_compatible K)

/-- The local-norm specialization of `Spectral.upperFixedSpace`. -/
abbrev upperFixedSpace (A : FiniteRepresentation.{0, uΩ, uV} ℂ W)
    (r : ℝ) : Submodule ℂ A :=
  Spectral.upperFixedSpace K K Ω (baseNorm_compatible K) A r

@[simp] theorem mem_upperFixedSpace
    (A : FiniteRepresentation.{0, uΩ, uV} ℂ W) (r : ℝ) (v : A) :
    v ∈ upperFixedSpace K Ω A r ↔ ∀ w ∈ upperGroup K Ω r, A.representation w v = v :=
  Spectral.mem_upperFixedSpace K K Ω (baseNorm_compatible K) A r v

/-- The local-norm specialization of `Spectral.IsTrivialAt`. -/
abbrev IsTrivialAt (A : FiniteRepresentation.{0, uΩ, uV} ℂ W)
    (r : ℝ) : Prop :=
  Spectral.IsTrivialAt K K Ω (baseNorm_compatible K) A r

/-- The local-norm specialization of `Spectral.trivialityThresholds`. -/
abbrev trivialityThresholds
    (A : FiniteRepresentation.{0, uΩ, uV} ℂ W) : Set ℝ :=
  Spectral.trivialityThresholds K K Ω (baseNorm_compatible K) A

/-- The local-norm specialization of `Spectral.lastBreak`. -/
abbrev lastBreak (A : FiniteRepresentation.{0, uΩ, uV} ℂ W) : ℝ :=
  Spectral.lastBreak K K Ω (baseNorm_compatible K) A

theorem isTrivialAt_mono
    (A : FiniteRepresentation.{0, uΩ, uV} ℂ W)
    {r s : ℝ} (hrs : r ≤ s) (hr : IsTrivialAt K Ω A r) : IsTrivialAt K Ω A s :=
  Spectral.isTrivialAt_mono K K Ω (baseNorm_compatible K) A hrs hr

theorem trivialityThresholds_bddBelow
    (A : FiniteRepresentation.{0, uΩ, uV} ℂ W) :
    BddBelow (trivialityThresholds K Ω A) :=
  Spectral.trivialityThresholds_bddBelow K K Ω (baseNorm_compatible K) A

theorem lastBreak_nonneg
    (A : FiniteRepresentation.{0, uΩ, uV} ℂ W) :
    0 ≤ lastBreak K Ω A :=
  Spectral.lastBreak_nonneg K K Ω (baseNorm_compatible K) A

theorem lastBreak_eq_zero_of_thresholds_empty
    (A : FiniteRepresentation.{0, uΩ, uV} ℂ W)
    (h : trivialityThresholds K Ω A = ∅) : lastBreak K Ω A = 0 :=
  Spectral.lastBreak_eq_zero_of_thresholds_empty K K Ω (baseNorm_compatible K) A h

theorem lastBreak_le_of_mem
    (A : FiniteRepresentation.{0, uΩ, uV} ℂ W)
    {r : ℝ} (hr : r ∈ trivialityThresholds K Ω A) : lastBreak K Ω A ≤ r :=
  Spectral.lastBreak_le_of_mem K K Ω (baseNorm_compatible K) A hr

theorem isTrivialAt_equiv
    {A : FiniteRepresentation.{0, uΩ, uV} ℂ W}
    {B : FiniteRepresentation.{0, uΩ, uW} ℂ W}
    (e : FiniteRepresentation.Equiv A B) (r : ℝ) :
    IsTrivialAt K Ω A r ↔ IsTrivialAt K Ω B r :=
  Spectral.isTrivialAt_equiv K K Ω (baseNorm_compatible K) e r

theorem trivialityThresholds_equiv
    {A : FiniteRepresentation.{0, uΩ, uV} ℂ W}
    {B : FiniteRepresentation.{0, uΩ, uW} ℂ W}
    (e : FiniteRepresentation.Equiv A B) :
    trivialityThresholds K Ω A = trivialityThresholds K Ω B :=
  Spectral.trivialityThresholds_equiv K K Ω (baseNorm_compatible K) e

theorem lastBreak_equiv
    {A : FiniteRepresentation.{0, uΩ, uV} ℂ W}
    {B : FiniteRepresentation.{0, uΩ, uW} ℂ W}
    (e : FiniteRepresentation.Equiv A B) : lastBreak K Ω A = lastBreak K Ω B :=
  Spectral.lastBreak_equiv K K Ω (baseNorm_compatible K) e

/-- The local-norm specialization of `Spectral.classLastBreak`. -/
abbrev classLastBreak : FiniteRepresentation.IsomorphismClasses.{0, uΩ, uV}
    ℂ W → ℝ :=
  Spectral.classLastBreak K K Ω (baseNorm_compatible K)

@[simp] theorem classLastBreak_classOf
    (A : FiniteRepresentation.{0, uΩ, uV} ℂ W) :
    classLastBreak K Ω (FiniteRepresentation.classOf A) = lastBreak K Ω A :=
  Spectral.classLastBreak_classOf K K Ω (baseNorm_compatible K) A

theorem classLastBreak_nonneg
    (c : FiniteRepresentation.IsomorphismClasses.{0, uΩ, uV} ℂ W) :
    0 ≤ classLastBreak K Ω c :=
  Spectral.classLastBreak_nonneg K K Ω (baseNorm_compatible K) c

/-- The local-norm specialization of `Spectral.breakLabel`. -/
abbrev breakLabel (b : Basis.{uK, uΩ, uV} K Ω) : ℝ :=
  Spectral.breakLabel K K Ω (baseNorm_compatible K) b

@[simp] theorem breakLabel_basisClass
    (A : FiniteRepresentation.{0, uΩ, uV} ℂ W)
    (hc : A.IsContinuous) (hi : A.IsIrreducible) (n : ℕ+) (hn : A.rank = (n : ℕ)) :
    breakLabel K Ω (Weil.basisClass A hc hi n hn) = lastBreak K Ω A := rfl

theorem breakLabel_nonneg (b : Basis.{uK, uΩ, uV} K Ω) : 0 ≤ breakLabel K Ω b :=
  Spectral.breakLabel_nonneg K K Ω (baseNorm_compatible K) b

/-- The local-norm specialization of `Spectral.breakSupport`. -/
abbrev breakSupport (x : Lattice.{uK, uΩ, uV} K Ω) : Finset ℝ :=
  Spectral.breakSupport K K Ω (baseNorm_compatible K) x

@[simp] theorem mem_breakSupport (x : Lattice.{uK, uΩ, uV} K Ω) (r : ℝ) :
    r ∈ breakSupport K Ω x ↔ ∃ b, x b ≠ 0 ∧ breakLabel K Ω b = r :=
  Spectral.mem_breakSupport K K Ω (baseNorm_compatible K) x r

@[simp] theorem breakSupport_nonempty_iff (x : Lattice.{uK, uΩ, uV} K Ω) :
    (breakSupport K Ω x).Nonempty ↔ x ≠ 0 :=
  Spectral.breakSupport_nonempty_iff K K Ω (baseNorm_compatible K) x

@[simp] theorem breakSupport_zero : breakSupport K Ω (0 : Lattice.{uK, uΩ, uV} K Ω) = ∅ :=
  Spectral.breakSupport_zero K K Ω (baseNorm_compatible K)

theorem breakSupport_nonneg (x : Lattice.{uK, uΩ, uV} K Ω) {r : ℝ}
    (hr : r ∈ breakSupport K Ω x) : 0 ≤ r :=
  Spectral.breakSupport_nonneg K K Ω (baseNorm_compatible K) x hr

/-- The local-norm specialization of `Spectral.minimumBreak`. -/
abbrev minimumBreak (x : Lattice.{uK, uΩ, uV} K Ω) (h : (breakSupport K Ω x).Nonempty) : ℝ :=
  Spectral.minimumBreak K K Ω (baseNorm_compatible K) x h

/-- The local-norm specialization of `Spectral.maximumBreak`. -/
abbrev maximumBreak (x : Lattice.{uK, uΩ, uV} K Ω) (h : (breakSupport K Ω x).Nonempty) : ℝ :=
  Spectral.maximumBreak K K Ω (baseNorm_compatible K) x h

/-- The local-norm specialization of `Spectral.AllBreaksAtLeast`. -/
abbrev AllBreaksAtLeast (x : Lattice.{uK, uΩ, uV} K Ω) (a : ℝ) : Prop :=
  Spectral.AllBreaksAtLeast K K Ω (baseNorm_compatible K) x a

/-- The local-norm specialization of `Spectral.AllBreaksBelow`. -/
abbrev AllBreaksBelow (x : Lattice.{uK, uΩ, uV} K Ω) (b : ℝ) : Prop :=
  Spectral.AllBreaksBelow K K Ω (baseNorm_compatible K) x b

/-- The local-norm specialization of `Spectral.PositiveBreakSupport`. -/
abbrev PositiveBreakSupport (x : Lattice.{uK, uΩ, uV} K Ω) : Prop :=
  Spectral.PositiveBreakSupport K K Ω (baseNorm_compatible K) x

theorem allBreaksAtLeast_iff_support (x : Lattice.{uK, uΩ, uV} K Ω) (a : ℝ) :
    AllBreaksAtLeast K Ω x a ↔ ∀ r ∈ breakSupport K Ω x, a ≤ r :=
  Spectral.allBreaksAtLeast_iff_support K K Ω (baseNorm_compatible K) x a

theorem allBreaksBelow_iff_support (x : Lattice.{uK, uΩ, uV} K Ω) (b : ℝ) :
    AllBreaksBelow K Ω x b ↔ ∀ r ∈ breakSupport K Ω x, r < b :=
  Spectral.allBreaksBelow_iff_support K K Ω (baseNorm_compatible K) x b

theorem allBreaksAtLeast_iff_le_minimumBreak (x : Lattice.{uK, uΩ, uV} K Ω)
    (h : (breakSupport K Ω x).Nonempty) (a : ℝ) :
    AllBreaksAtLeast K Ω x a ↔ a ≤ minimumBreak K Ω x h :=
  Spectral.allBreaksAtLeast_iff_le_minimumBreak K K Ω (baseNorm_compatible K) x h a

theorem allBreaksBelow_iff_maximumBreak_lt (x : Lattice.{uK, uΩ, uV} K Ω)
    (h : (breakSupport K Ω x).Nonempty) (b : ℝ) :
    AllBreaksBelow K Ω x b ↔ maximumBreak K Ω x h < b :=
  Spectral.allBreaksBelow_iff_maximumBreak_lt K K Ω (baseNorm_compatible K) x h b

theorem positiveBreakSupport_iff_minimumBreak_pos (x : Lattice.{uK, uΩ, uV} K Ω)
    (h : (breakSupport K Ω x).Nonempty) :
    PositiveBreakSupport K Ω x ↔ 0 < minimumBreak K Ω x h :=
  Spectral.positiveBreakSupport_iff_minimumBreak_pos K K Ω (baseNorm_compatible K) x h

@[simp] theorem allBreaksAtLeast_zero (a : ℝ) :
    AllBreaksAtLeast K Ω (0 : Lattice.{uK, uΩ, uV} K Ω) a :=
  Spectral.allBreaksAtLeast_zero K K Ω (baseNorm_compatible K) a

@[simp] theorem allBreaksBelow_zero (b : ℝ) :
    AllBreaksBelow K Ω (0 : Lattice.{uK, uΩ, uV} K Ω) b :=
  Spectral.allBreaksBelow_zero K K Ω (baseNorm_compatible K) b

@[simp] theorem positiveBreakSupport_zero :
    PositiveBreakSupport K Ω (0 : Lattice.{uK, uΩ, uV} K Ω) :=
  Spectral.positiveBreakSupport_zero K K Ω (baseNorm_compatible K)

theorem allBreaksAtLeast_nonneg (x : Lattice.{uK, uΩ, uV} K Ω) : AllBreaksAtLeast K Ω x 0 :=
  Spectral.allBreaksAtLeast_nonneg K K Ω (baseNorm_compatible K) x

theorem minimumBreak_nonneg (x : Lattice.{uK, uΩ, uV} K Ω)
    (h : (breakSupport K Ω x).Nonempty) : 0 ≤ minimumBreak K Ω x h :=
  Spectral.minimumBreak_nonneg K K Ω (baseNorm_compatible K) x h

theorem minimumBreak_le_maximumBreak (x : Lattice.{uK, uΩ, uV} K Ω)
    (h : (breakSupport K Ω x).Nonempty) : minimumBreak K Ω x h ≤ maximumBreak K Ω x h :=
  Spectral.minimumBreak_le_maximumBreak K K Ω (baseNorm_compatible K) x h

theorem maximumBreak_nonneg (x : Lattice.{uK, uΩ, uV} K Ω)
    (h : (breakSupport K Ω x).Nonempty) : 0 ≤ maximumBreak K Ω x h :=
  Spectral.maximumBreak_nonneg K K Ω (baseNorm_compatible K) x h

theorem pos_of_allBreaksBelow (x : Lattice.{uK, uΩ, uV} K Ω) (hx : x ≠ 0)
    {b : ℝ} (hb : AllBreaksBelow K Ω x b) : 0 < b :=
  Spectral.pos_of_allBreaksBelow K K Ω (baseNorm_compatible K) x hx hb

end Langlands.VirtualRepresentation.LocalWeil.SepClosed.Ramification

namespace Langlands.VirtualRepresentation.LocalWeil.Ramification

open Langlands.Weil.Local Langlands.Ramification.Padic

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

local instance : TopologicalSpace F.Carrier := F.canonicalTopologicalData.topology
local instance : ValuativeRel F.Carrier := F.canonicalTopologicalData.valuativeRel
local instance : IsNonarchimedeanLocalField F.Carrier := F.canonicalTopologicalData.localField
local instance : CharZero F.Carrier := Algebra.charZero_of_charZero (Padic p) F.Carrier

private theorem padicBaseNorm_compatible (a b : Padic p) :
    ‖a‖ ≤ ‖b‖ ↔ ValuativeRel.vle a b := by
  change ‖a‖ ≤ ‖b‖ ↔ Padic.mulValuation a ≤ Padic.mulValuation b
  simp only [← not_lt, Padic.norm_lt_norm_iff_mulValuation_lt]

/-- The actual upper ramification subgroup of the local Weil group. -/
def upperGroup (r : ℝ) : Subgroup (localWeilGroup F) :=
  (absoluteUpperRamificationGroup F r).comap (localProjection F).toMonoidHom

@[simp] theorem mem_upperGroup (r : ℝ) (w : localWeilGroup F) :
    w ∈ upperGroup F r ↔ localProjection F w ∈ absoluteUpperRamificationGroup F r := Iff.rfl

theorem upperGroup_antitone : Antitone (upperGroup F) :=
  SepClosed.Ramification.Spectral.upperGroup_antitone (Padic p) F.Carrier
    (AlgebraicClosure F.Carrier) (padicBaseNorm_compatible (p := p))

/-- The actual fixed subspace, with no finite-image presentation supplied. -/
def upperFixedSpace (A : FiniteRepresentation.{0, uF, uV} ℂ (localWeilGroup F))
    (r : ℝ) : Submodule ℂ A :=
  SepClosed.Ramification.Spectral.upperFixedSpace (Padic p) F.Carrier
    (AlgebraicClosure F.Carrier) (padicBaseNorm_compatible (p := p)) A r

@[simp] theorem mem_upperFixedSpace
    (A : FiniteRepresentation.{0, uF, uV} ℂ (localWeilGroup F)) (r : ℝ) (v : A) :
    v ∈ upperFixedSpace F A r ↔ ∀ w ∈ upperGroup F r, A.representation w v = v :=
  SepClosed.Ramification.Spectral.mem_upperFixedSpace (Padic p) F.Carrier
    (AlgebraicClosure F.Carrier) (padicBaseNorm_compatible (p := p)) A r v

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
  SepClosed.Ramification.Spectral.isTrivialAt_mono (Padic p) F.Carrier
    (AlgebraicClosure F.Carrier) (padicBaseNorm_compatible (p := p)) A hrs hr

theorem trivialityThresholds_bddBelow
    (A : FiniteRepresentation.{0, uF, uV} ℂ (localWeilGroup F)) :
    BddBelow (trivialityThresholds F A) :=
  SepClosed.Ramification.Spectral.trivialityThresholds_bddBelow (Padic p) F.Carrier
    (AlgebraicClosure F.Carrier) (padicBaseNorm_compatible (p := p)) A

theorem lastBreak_nonneg
    (A : FiniteRepresentation.{0, uF, uV} ℂ (localWeilGroup F)) :
    0 ≤ lastBreak F A :=
  SepClosed.Ramification.Spectral.lastBreak_nonneg (Padic p) F.Carrier
    (AlgebraicClosure F.Carrier) (padicBaseNorm_compatible (p := p)) A

theorem lastBreak_eq_zero_of_thresholds_empty
    (A : FiniteRepresentation.{0, uF, uV} ℂ (localWeilGroup F))
    (h : trivialityThresholds F A = ∅) : lastBreak F A = 0 :=
  SepClosed.Ramification.Spectral.lastBreak_eq_zero_of_thresholds_empty (Padic p) F.Carrier
    (AlgebraicClosure F.Carrier) (padicBaseNorm_compatible (p := p)) A h

theorem lastBreak_le_of_mem
    (A : FiniteRepresentation.{0, uF, uV} ℂ (localWeilGroup F))
    {r : ℝ} (hr : r ∈ trivialityThresholds F A) : lastBreak F A ≤ r :=
  SepClosed.Ramification.Spectral.lastBreak_le_of_mem (Padic p) F.Carrier
    (AlgebraicClosure F.Carrier) (padicBaseNorm_compatible (p := p)) A hr

theorem isTrivialAt_equiv
    {A : FiniteRepresentation.{0, uF, uV} ℂ (localWeilGroup F)}
    {B : FiniteRepresentation.{0, uF, uW} ℂ (localWeilGroup F)}
    (e : FiniteRepresentation.Equiv A B) (r : ℝ) :
    IsTrivialAt F A r ↔ IsTrivialAt F B r :=
  SepClosed.Ramification.Spectral.isTrivialAt_equiv (Padic p) F.Carrier
    (AlgebraicClosure F.Carrier) (padicBaseNorm_compatible (p := p)) e r

theorem trivialityThresholds_equiv
    {A : FiniteRepresentation.{0, uF, uV} ℂ (localWeilGroup F)}
    {B : FiniteRepresentation.{0, uF, uW} ℂ (localWeilGroup F)}
    (e : FiniteRepresentation.Equiv A B) :
    trivialityThresholds F A = trivialityThresholds F B :=
  SepClosed.Ramification.Spectral.trivialityThresholds_equiv (Padic p) F.Carrier
    (AlgebraicClosure F.Carrier) (padicBaseNorm_compatible (p := p)) e

theorem lastBreak_equiv
    {A : FiniteRepresentation.{0, uF, uV} ℂ (localWeilGroup F)}
    {B : FiniteRepresentation.{0, uF, uW} ℂ (localWeilGroup F)}
    (e : FiniteRepresentation.Equiv A B) : lastBreak F A = lastBreak F B :=
  SepClosed.Ramification.Spectral.lastBreak_equiv (Padic p) F.Carrier
    (AlgebraicClosure F.Carrier) (padicBaseNorm_compatible (p := p)) e

/-- The last break descends to genuine representation isomorphism classes. -/
def classLastBreak : FiniteRepresentation.IsomorphismClasses.{0, uF, uV}
    ℂ (localWeilGroup F) → ℝ :=
  SepClosed.Ramification.Spectral.classLastBreak (Padic p) F.Carrier
    (AlgebraicClosure F.Carrier) (padicBaseNorm_compatible (p := p))

@[simp] theorem classLastBreak_classOf
    (A : FiniteRepresentation.{0, uF, uV} ℂ (localWeilGroup F)) :
    classLastBreak F (FiniteRepresentation.classOf A) = lastBreak F A :=
  SepClosed.Ramification.Spectral.classLastBreak_classOf (Padic p) F.Carrier
    (AlgebraicClosure F.Carrier) (padicBaseNorm_compatible (p := p)) A

theorem classLastBreak_nonneg
    (c : FiniteRepresentation.IsomorphismClasses.{0, uF, uV} ℂ (localWeilGroup F)) :
    0 ≤ classLastBreak F c :=
  SepClosed.Ramification.Spectral.classLastBreak_nonneg (Padic p) F.Carrier
    (AlgebraicClosure F.Carrier) (padicBaseNorm_compatible (p := p)) c

/-- The intrinsic label of an actual continuous irreducible positive-rank class. -/
def breakLabel (b : Basis.{uF, uV} F) : ℝ :=
  classLastBreak F (Weil.underlyingClass (localWeilGroup F) b)

@[simp] theorem breakLabel_basisClass
    (A : FiniteRepresentation.{0, uF, uV} ℂ (localWeilGroup F))
    (hc : A.IsContinuous) (hi : A.IsIrreducible) (n : ℕ+) (hn : A.rank = (n : ℕ)) :
    breakLabel F (basisClass A hc hi n hn) = lastBreak F A := rfl

theorem breakLabel_nonneg (b : Basis.{uF, uV} F) : 0 ≤ breakLabel F b :=
  SepClosed.Ramification.Spectral.breakLabel_nonneg (Padic p) F.Carrier
    (AlgebraicClosure F.Carrier) (padicBaseNorm_compatible (p := p)) b

/-- Labels of the nonzero signed Weil coefficients after class cancellation.
This is a set image, not a pushforward that sums coefficients at equal labels. -/
def breakSupport (x : Lattice.{uF, uV} F) : Finset ℝ :=
  x.support.image (breakLabel F)

@[simp] theorem mem_breakSupport (x : Lattice.{uF, uV} F) (r : ℝ) :
    r ∈ breakSupport F x ↔ ∃ b, x b ≠ 0 ∧ breakLabel F b = r :=
  SepClosed.Ramification.Spectral.mem_breakSupport (Padic p) F.Carrier
    (AlgebraicClosure F.Carrier) (padicBaseNorm_compatible (p := p)) x r

@[simp] theorem breakSupport_nonempty_iff (x : Lattice.{uF, uV} F) :
    (breakSupport F x).Nonempty ↔ x ≠ 0 :=
  SepClosed.Ramification.Spectral.breakSupport_nonempty_iff (Padic p) F.Carrier
    (AlgebraicClosure F.Carrier) (padicBaseNorm_compatible (p := p)) x

@[simp] theorem breakSupport_zero : breakSupport F (0 : Lattice.{uF, uV} F) = ∅ :=
  SepClosed.Ramification.Spectral.breakSupport_zero (Padic p) F.Carrier
    (AlgebraicClosure F.Carrier) (padicBaseNorm_compatible (p := p))

theorem breakSupport_nonneg (x : Lattice.{uF, uV} F) {r : ℝ}
    (hr : r ∈ breakSupport F x) : 0 ≤ r :=
  SepClosed.Ramification.Spectral.breakSupport_nonneg (Padic p) F.Carrier
    (AlgebraicClosure F.Carrier) (padicBaseNorm_compatible (p := p)) x hr

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
    AllBreaksAtLeast F x a ↔ ∀ r ∈ breakSupport F x, a ≤ r :=
  SepClosed.Ramification.Spectral.allBreaksAtLeast_iff_support (Padic p) F.Carrier
    (AlgebraicClosure F.Carrier) (padicBaseNorm_compatible (p := p)) x a

theorem allBreaksBelow_iff_support (x : Lattice.{uF, uV} F) (b : ℝ) :
    AllBreaksBelow F x b ↔ ∀ r ∈ breakSupport F x, r < b :=
  SepClosed.Ramification.Spectral.allBreaksBelow_iff_support (Padic p) F.Carrier
    (AlgebraicClosure F.Carrier) (padicBaseNorm_compatible (p := p)) x b

theorem allBreaksAtLeast_iff_le_minimumBreak (x : Lattice.{uF, uV} F)
    (h : (breakSupport F x).Nonempty) (a : ℝ) :
    AllBreaksAtLeast F x a ↔ a ≤ minimumBreak F x h :=
  SepClosed.Ramification.Spectral.allBreaksAtLeast_iff_le_minimumBreak (Padic p) F.Carrier
    (AlgebraicClosure F.Carrier) (padicBaseNorm_compatible (p := p)) x h a

theorem allBreaksBelow_iff_maximumBreak_lt (x : Lattice.{uF, uV} F)
    (h : (breakSupport F x).Nonempty) (b : ℝ) :
    AllBreaksBelow F x b ↔ maximumBreak F x h < b :=
  SepClosed.Ramification.Spectral.allBreaksBelow_iff_maximumBreak_lt (Padic p) F.Carrier
    (AlgebraicClosure F.Carrier) (padicBaseNorm_compatible (p := p)) x h b

theorem positiveBreakSupport_iff_minimumBreak_pos (x : Lattice.{uF, uV} F)
    (h : (breakSupport F x).Nonempty) :
    PositiveBreakSupport F x ↔ 0 < minimumBreak F x h :=
  SepClosed.Ramification.Spectral.positiveBreakSupport_iff_minimumBreak_pos (Padic p) F.Carrier
    (AlgebraicClosure F.Carrier) (padicBaseNorm_compatible (p := p)) x h

@[simp] theorem allBreaksAtLeast_zero (a : ℝ) :
    AllBreaksAtLeast F (0 : Lattice.{uF, uV} F) a :=
  SepClosed.Ramification.Spectral.allBreaksAtLeast_zero (Padic p) F.Carrier
    (AlgebraicClosure F.Carrier) (padicBaseNorm_compatible (p := p)) a

@[simp] theorem allBreaksBelow_zero (b : ℝ) :
    AllBreaksBelow F (0 : Lattice.{uF, uV} F) b :=
  SepClosed.Ramification.Spectral.allBreaksBelow_zero (Padic p) F.Carrier
    (AlgebraicClosure F.Carrier) (padicBaseNorm_compatible (p := p)) b

@[simp] theorem positiveBreakSupport_zero :
    PositiveBreakSupport F (0 : Lattice.{uF, uV} F) :=
  SepClosed.Ramification.Spectral.positiveBreakSupport_zero (Padic p) F.Carrier
    (AlgebraicClosure F.Carrier) (padicBaseNorm_compatible (p := p))

theorem allBreaksAtLeast_nonneg (x : Lattice.{uF, uV} F) : AllBreaksAtLeast F x 0 :=
  SepClosed.Ramification.Spectral.allBreaksAtLeast_nonneg (Padic p) F.Carrier
    (AlgebraicClosure F.Carrier) (padicBaseNorm_compatible (p := p)) x

theorem minimumBreak_nonneg (x : Lattice.{uF, uV} F)
    (h : (breakSupport F x).Nonempty) : 0 ≤ minimumBreak F x h :=
  SepClosed.Ramification.Spectral.minimumBreak_nonneg (Padic p) F.Carrier
    (AlgebraicClosure F.Carrier) (padicBaseNorm_compatible (p := p)) x h

theorem minimumBreak_le_maximumBreak (x : Lattice.{uF, uV} F)
    (h : (breakSupport F x).Nonempty) : minimumBreak F x h ≤ maximumBreak F x h :=
  SepClosed.Ramification.Spectral.minimumBreak_le_maximumBreak (Padic p) F.Carrier
    (AlgebraicClosure F.Carrier) (padicBaseNorm_compatible (p := p)) x h

theorem maximumBreak_nonneg (x : Lattice.{uF, uV} F)
    (h : (breakSupport F x).Nonempty) : 0 ≤ maximumBreak F x h :=
  SepClosed.Ramification.Spectral.maximumBreak_nonneg (Padic p) F.Carrier
    (AlgebraicClosure F.Carrier) (padicBaseNorm_compatible (p := p)) x h

theorem pos_of_allBreaksBelow (x : Lattice.{uF, uV} F) (hx : x ≠ 0)
    {b : ℝ} (hb : AllBreaksBelow F x b) : 0 < b :=
  SepClosed.Ramification.Spectral.pos_of_allBreaksBelow (Padic p) F.Carrier
    (AlgebraicClosure F.Carrier) (padicBaseNorm_compatible (p := p)) x hx hb

end Langlands.VirtualRepresentation.LocalWeil.Ramification
