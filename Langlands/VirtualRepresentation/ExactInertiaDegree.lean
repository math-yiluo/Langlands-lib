import Langlands.Global.Factors.RelativeWeilLocalEuler

/-!
# Inertia codimension on exact virtual representations

Finite inertia image makes invariant dimension exact-additive. Its difference
from dimension detects actual unramifiedness on genuine objects.
-/

noncomputable section

set_option autoImplicit false

universe uG uV u

namespace Langlands.FiniteRepresentation

variable {G : Type uG} [Group G] (I : Subgroup G) [I.Normal]

/-- All vectors are fixed precisely when inertia acts trivially. -/
theorem invariantSubspace_eq_top_iff_isUnramified
    (A : FiniteRepresentation.{0, uG, uV} ℂ G) :
    invariantSubspace A I = ⊤ ↔ A.IsUnramified I := by
  constructor
  · intro h i
    ext v
    have hv : v ∈ invariantSubspace A I := by rw [h]; trivial
    exact hv i
  · intro h
    apply top_unique
    intro v _ i
    change A.representation i v = v
    rw [h i]
    rfl

/-- In finite dimension, full invariant dimension detects trivial inertia. -/
theorem invariants_rank_eq_iff_isUnramified
    (A : FiniteRepresentation.{0, uG, uV} ℂ G) :
    (invariants I A).rank = A.rank ↔ A.IsUnramified I := by
  change Module.finrank ℂ (invariantSubspace A I) = Module.finrank ℂ A ↔ _
  rw [← Submodule.eq_top_iff_finrank_eq, invariantSubspace_eq_top_iff_isUnramified]

end Langlands.FiniteRepresentation

namespace Langlands.VirtualRepresentation.ExactGrothendieckGroup

open FiniteRepresentation

variable {G : Type uG} [Group G] (I : Subgroup G) [I.Normal]
  (P : FiniteRepresentation.{0, uG, uV} ℂ G → Prop)

/-- Integer dimension of inertia invariants, on genuine classes. -/
def invariantsClassDegree : IsomorphismClassesWith P → ℤ :=
  Quotient.lift (fun A => ((invariants I A.val).rank : ℤ)) fun _ _ ⟨e⟩ =>
    congrArg (fun n : ℕ => (n : ℤ)) (rank_eq_of_equiv (invariantsEquiv I e))

/-- Averaging over the finite inertia image proves exact additivity. -/
theorem invariantsClassDegree_isExactAdditive
    (hfinite : ∀ A, P A → A.HasFiniteInertiaImage I) :
    IsExactAdditive P (invariantsClassDegree I P) := by
  intro A B C f g h
  change ((invariants I B.val).rank : ℤ) =
    ((invariants I A.val).rank : ℤ) + ((invariants I C.val).rank : ℤ)
  rw [rank_eq_add_of_shortExact (isShortExact_invariants I h (hfinite B.val B.property)),
    Nat.cast_add]

/-- Invariant dimension on the exact virtual group of a finite-inertia family. -/
def invariantsDegree (hfinite : ∀ A, P A → A.HasFiniteInertiaImage I) :
    ExactGrothendieckGroup P →ₗ[ℤ] ℤ :=
  lift P (invariantsClassDegree I P) (invariantsClassDegree_isExactAdditive I P hfinite)

@[simp]
theorem invariantsDegree_ofRepresentation
    (hfinite : ∀ A, P A → A.HasFiniteInertiaImage I)
    (A : {A : FiniteRepresentation.{0, uG, uV} ℂ G // P A}) :
    invariantsDegree I P hfinite (ofRepresentation P A) = ((invariants I A.val).rank : ℤ) :=
  lift_ofRepresentation P _ _ A

/-- Total dimension minus invariant dimension, with integer values on virtual objects. -/
def inertiaCodimension (hfinite : ∀ A, P A → A.HasFiniteInertiaImage I) :
    ExactGrothendieckGroup P →ₗ[ℤ] ℤ :=
  degree P - invariantsDegree I P hfinite

@[simp]
theorem inertiaCodimension_ofRepresentation
    (hfinite : ∀ A, P A → A.HasFiniteInertiaImage I)
    (A : {A : FiniteRepresentation.{0, uG, uV} ℂ G // P A}) :
    inertiaCodimension I P hfinite (ofRepresentation P A) =
      (A.val.rank : ℤ) - ((invariants I A.val).rank : ℤ) := by
  simp [inertiaCodimension]

/-- Zero inertia codimension of a genuine object means its inertia action is trivial. -/
theorem inertiaCodimension_eq_zero_iff
    (hfinite : ∀ A, P A → A.HasFiniteInertiaImage I)
    (A : {A : FiniteRepresentation.{0, uG, uV} ℂ G // P A}) :
    inertiaCodimension I P hfinite (ofRepresentation P A) = 0 ↔ A.val.IsUnramified I := by
  rw [inertiaCodimension_ofRepresentation, sub_eq_zero, Nat.cast_inj, eq_comm,
    invariants_rank_eq_iff_isUnramified]

/-- Equality with a finite sum of unramified genuine classes forces actual
unramifiedness. The conclusion concerns the representation, not just its class. -/
theorem isUnramified_of_class_eq_sum
    (hfinite : ∀ A, P A → A.HasFiniteInertiaImage I)
    (A : {A : FiniteRepresentation.{0, uG, uV} ℂ G // P A})
    {J : Type*} [Fintype J]
    (B : J → {A : FiniteRepresentation.{0, uG, uV} ℂ G // P A})
    (h : ofRepresentation P A = ∑ j, ofRepresentation P (B j))
    (hB : ∀ j, (B j).val.IsUnramified I) :
    A.val.IsUnramified I := by
  apply (inertiaCodimension_eq_zero_iff I P hfinite A).mp
  rw [h, map_sum]
  exact Finset.sum_eq_zero fun j _ =>
    (inertiaCodimension_eq_zero_iff I P hfinite (B j)).mpr (hB j)

end Langlands.VirtualRepresentation.ExactGrothendieckGroup

namespace Langlands.Weil.Local

open FiniteRepresentation VirtualRepresentation VirtualRepresentation.ExactGrothendieckGroup

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{u} p)

/-- The published local continuity criterion supplies finite inertia image. -/
theorem hasFiniteInertiaImage_of_isContinuous
    (A : LocalWeilRepresentation.{u, uV} F) (hA : A.IsContinuous) :
    A.HasFiniteInertiaImage (localInertia F) := by
  have hc := localWeilContinuity F A
  exact (hc.2.2.2.2.mp (hc.2.2.1.mp hA)).1

/-- A local representation whose continuous exact class is a sum of unramified
classes is itself unramified. -/
theorem isUnramified_of_continuousClass_eq_sum
    (A : {A : LocalWeilRepresentation.{u, uV} F // A.IsContinuous})
    {J : Type*} [Fintype J]
    (B : J → {A : LocalWeilRepresentation.{u, uV} F // A.IsContinuous})
    (h : ofRepresentation _ A = ∑ j, ofRepresentation _ (B j))
    (hB : ∀ j, (B j).val.IsUnramified (localInertia F)) :
    A.val.IsUnramified (localInertia F) :=
  isUnramified_of_class_eq_sum (localInertia F) _
    (hasFiniteInertiaImage_of_isContinuous F) A B h hB

end Langlands.Weil.Local
