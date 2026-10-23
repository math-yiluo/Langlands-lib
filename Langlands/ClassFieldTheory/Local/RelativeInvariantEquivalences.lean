import Langlands.ClassFieldTheory.Local.Invariants
import Langlands.ClassFieldTheory.Local.UnramifiedInvariant

/-! # Equivalences and finiteness from a relative invariant image law -/

noncomputable section

namespace Langlands.ClassFieldTheory.Local.InvariantFamily

universe u v

variable {p : ℕ} [Fact p.Prime] (I : InvariantFamily.{u,v} p)
  (hI : I.RelativeImages) (F : PadicField.{u} p) (L : Type v)
  [Field L] [Algebra F.Carrier L] [FiniteDimensional F.Carrier L]
  [IsGalois F.Carrier L]

/-- The supplied relative invariant, with its exact image as codomain. -/
def relativeInvariantEquiv :
    relativeCohomology F.Carrier L 2 ≃+
      denominatorSubgroup (Module.finrank F.Carrier L) :=
  AddEquiv.ofBijective
    ((I.relative F L).codRestrict
      (denominatorSubgroup (Module.finrank F.Carrier L)) (fun x => by
        rw [← (hI F L).2]
        exact ⟨x, rfl⟩))
    ⟨fun _ _ h => (hI F L).1 (congrArg Subtype.val h),
      fun y => by
        have hy : y.val ∈ (I.relative F L).range := by
          rw [(hI F L).2]
          exact y.property
        obtain ⟨x, hx⟩ := hy
        exact ⟨x, Subtype.ext hx⟩⟩

/-- Forgetting subgroup membership recovers the original supplied invariant. -/
@[simp] theorem relativeInvariantEquiv_apply
    (x : relativeCohomology F.Carrier L 2) :
    (I.relativeInvariantEquiv hI F L x : RationalModIntegers) =
      I.relative F L x := rfl

/-- The inverse equivalence realizes each element of the denominator subgroup. -/
@[simp] theorem relativeInvariantEquiv_symm_apply
    (y : denominatorSubgroup (Module.finrank F.Carrier L)) :
    I.relative F L ((I.relativeInvariantEquiv hI F L).symm y) = y := by
  exact congrArg Subtype.val ((I.relativeInvariantEquiv hI F L).apply_symm_apply y)

/-- Relative cohomology in cyclic coordinates determined by the supplied invariant. -/
def relativeZModEquiv :
    relativeCohomology F.Carrier L 2 ≃+ ZMod (Module.finrank F.Carrier L) :=
  (I.relativeInvariantEquiv hI F L).trans
    (denominatorEquiv _ Module.finrank_pos).symm

/-- The cyclic coordinate retains the positive fraction convention. -/
theorem denominatorEquiv_relativeZModEquiv
    (x : relativeCohomology F.Carrier L 2) :
    (denominatorEquiv _ Module.finrank_pos (I.relativeZModEquiv hI F L x) :
      RationalModIntegers) = I.relative F L x := by
  change ((denominatorEquiv _ Module.finrank_pos)
    ((denominatorEquiv _ Module.finrank_pos).symm
      (I.relativeInvariantEquiv hI F L x)) : RationalModIntegers) = _
  rw [AddEquiv.apply_symm_apply, relativeInvariantEquiv_apply]

/-- The inverse cyclic coordinate has the corresponding positive rational invariant. -/
theorem relativeZModEquiv_symm_intCast (z : ℤ) :
    I.relative F L ((I.relativeZModEquiv hI F L).symm
      (z : ZMod (Module.finrank F.Carrier L))) =
      rationalClass ((z : ℚ) / Module.finrank F.Carrier L) := by
  change I.relative F L ((I.relativeInvariantEquiv hI F L).symm
    (denominatorEquiv _ Module.finrank_pos (z : ZMod _))) = _
  rw [relativeInvariantEquiv_symm_apply, denominatorEquiv_intCast]

include I hI in
/-- The exact image law determines the cardinality of actual relative H². -/
theorem relativeH2_card :
    Nat.card (relativeCohomology F.Carrier L 2) = Module.finrank F.Carrier L :=
  (Nat.card_congr (I.relativeZModEquiv hI F L).toEquiv).trans
    (Nat.card_zmod _)

include I hI in
/-- The actual relative H² is finite, separately from its cardinality formula. -/
theorem relativeH2_finite : Finite (relativeCohomology F.Carrier L 2) := by
  apply Nat.finite_of_card_ne_zero
  rw [I.relativeH2_card hI F L]
  exact ne_of_gt Module.finrank_pos

end Langlands.ClassFieldTheory.Local.InvariantFamily
