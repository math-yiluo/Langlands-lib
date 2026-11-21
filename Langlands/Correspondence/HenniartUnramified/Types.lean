import Langlands.Correspondence.HenniartUnramified.Uniqueness
import Mathlib.Dynamics.PeriodicPts.Defs

/-! # Inertia types and their Frobenius conjugates -/

noncomputable section

namespace Langlands.FiniteRepresentation.SplitDegree

open Representation

universe uG uH uW

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (D : SplitDegree G)

omit [IsTopologicalGroup G] in
theorem cj_surjective (k : ℕ) : Function.Surjective (D.cj k) :=
  (MulAut.conjNormal (D.lift ^ k)).surjective

/-- Continuous irreducible representations of inertia. -/
abbrev IsType (A : FiniteRepresentation.{0, uG, uW} ℂ D.inertia) : Prop :=
  A.IsContinuous ∧ A.IsIrreducible

/-- Inertia types: genuine isomorphism classes of continuous irreducible inertia
representations. -/
abbrev TypeClass := IsomorphismClassesWith.{0, uG, uW} (IsType.{uG, uW} D)

/-- The class of a type. -/
abbrev toClass (A : {A : FiniteRepresentation.{0, uG, uW} ℂ D.inertia // D.IsType A}) :
    TypeClass.{uG, uW} D :=
  Quotient.mk _ A

/-- The conjugate of an inertia type by the `k`th power of the lift, on the same carrier. -/
def conjObj (k : ℕ) (A : {A : FiniteRepresentation.{0, uG, uW} ℂ D.inertia // D.IsType A}) :
    {A : FiniteRepresentation.{0, uG, uW} ℂ D.inertia // D.IsType A} :=
  ⟨of (A.1.representation.comp (D.cj k)), by
      let _ : TopologicalSpace (Module.End ℂ A.1) := moduleTopology ℂ (Module.End ℂ A.1)
      have h : Continuous A.1.representation := A.2.1
      exact h.comp (D.continuous_cj k),
    isIrreducible_comp_surjective _ _ (D.cj_surjective k) A.2.2⟩

@[simp] theorem conjObj_representation (k : ℕ)
    (A : {A : FiniteRepresentation.{0, uG, uW} ℂ D.inertia // D.IsType A}) :
    (D.conjObj k A).1.representation = A.1.representation.comp (D.cj k) := rfl

/-- Conjugation of inertia types. -/
def conjType (k : ℕ) : TypeClass.{uG, uW} D → TypeClass.{uG, uW} D :=
  Quotient.map (D.conjObj k) fun _ _ ⟨e⟩ => ⟨equivComp e (D.cj k)⟩

theorem conjType_mk (k : ℕ) (A : {A : FiniteRepresentation.{0, uG, uW} ℂ D.inertia // D.IsType A}) :
    D.conjType k (D.toClass A) = D.toClass (D.conjObj k A) := rfl

omit [IsTopologicalGroup G] in
theorem toClass_eq_iff (A B : {A : FiniteRepresentation.{0, uG, uW} ℂ D.inertia // D.IsType A}) :
    D.toClass A = D.toClass B ↔
      Nonempty (Representation.Equiv A.1.representation B.1.representation) :=
  Quotient.eq

private def equivOfEqRep {V : Type uW} [AddCommGroup V] [Module ℂ V]
    {ρ σ : Representation ℂ D.inertia V} (h : ρ = σ) : Representation.Equiv ρ σ :=
  Representation.Equiv.mk (LinearEquiv.refl ℂ V) fun n => by rw [h]; rfl

theorem conjType_zero (c : TypeClass.{uG, uW} D) : D.conjType 0 c = c := by
  induction c using Quotient.inductionOn with
  | h A =>
    apply Quotient.sound
    refine ⟨D.equivOfEqRep ?_⟩
    ext n : 1
    change A.1.representation (D.cj 0 n) = A.1.representation n
    rw [cj_zero]

theorem conjType_conjType (k l : ℕ) (c : TypeClass.{uG, uW} D) :
    D.conjType k (D.conjType l c) = D.conjType (l + k) c := by
  induction c using Quotient.inductionOn with
  | h A =>
    apply Quotient.sound
    refine ⟨D.equivOfEqRep ?_⟩
    ext n : 1
    change A.1.representation (D.cj l (D.cj k n)) = A.1.representation (D.cj (l + k) n)
    rw [cj_add]

theorem iterate_conjType (d : ℕ) (c : TypeClass.{uG, uW} D) :
    (D.conjType 1)^[d] c = D.conjType d c := by
  induction d with
  | zero => exact (D.conjType_zero c).symm
  | succ d ih => rw [Function.iterate_succ_apply', ih, conjType_conjType]

variable {D}

/-- Distinct conjugates below the minimal period are unrelated. -/
theorem conj_dist_of_minimalPeriod
    (A : {A : FiniteRepresentation.{0, uG, uW} ℂ D.inertia // D.IsType A}) {m : ℕ}
    (hp : Function.minimalPeriod (D.conjType 1) (D.toClass A) = m + 1)
    (j k : Fin (m + 1)) (hjk : j ≠ k)
    (T : Representation.IntertwiningMap (A.1.representation.comp (D.cj j))
      (A.1.representation.comp (D.cj k))) : T = 0 := by
  by_contra hT
  have he := nonempty_equiv_of_ne_zero _ _ (D.conjObj j A).2.2 (D.conjObj k A).2.2 T hT
  have h : (D.conjType 1)^[j] (D.toClass A) = (D.conjType 1)^[k] (D.toClass A) := by
    rw [iterate_conjType, iterate_conjType, conjType_mk, conjType_mk]
    exact Quotient.sound he
  exact hjk (Fin.ext ((Function.iterate_eq_iterate_iff_of_lt_minimalPeriod
    (by rw [hp]; exact j.isLt) (by rw [hp]; exact k.isLt)).mp h))

/-- A type is isomorphic to its conjugate at its minimal period. -/
theorem conj_equiv_of_minimalPeriod
    (A : {A : FiniteRepresentation.{0, uG, uW} ℂ D.inertia // D.IsType A}) {m : ℕ}
    (hp : Function.minimalPeriod (D.conjType 1) (D.toClass A) = m + 1) :
    Nonempty (Representation.Equiv (A.1.representation.comp (D.cj (m + 1))) A.1.representation) := by
  have h := Function.iterate_minimalPeriod (f := D.conjType 1) (x := D.toClass A)
  rw [hp, iterate_conjType, conjType_mk] at h
  exact Quotient.exact h

end Langlands.FiniteRepresentation.SplitDegree
