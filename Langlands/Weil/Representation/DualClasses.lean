import Langlands.Weil.Representation.Dual
import Langlands.Weil.Representation.Predicates
import Langlands.Weil.Representation.OperationClosureProof

/-!
# Double duals and the dual involution on continuous irreducible classes

Evaluation identifies a finite-dimensional representation with its double
dual. For complex coefficients the dual is therefore an involution on genuine
isomorphism classes. Together with the published preservation of usual
continuity and irreducibility, it is a rank-preserving involution of the
continuous irreducible rank-`n` classes.
-/

noncomputable section

universe uK uG uV

namespace Langlands.FiniteRepresentation

section Algebraic

variable {K : Type uK} {G : Type uG} [Field K] [Group G]

/-- Evaluation is a genuine equivalence with the double dual. -/
def dualDualEquiv (A : FiniteRepresentation.{uK, uG, uV} K G) : Equiv A (dual (dual A)) :=
  Representation.Equiv.mk (Module.evalEquiv K A)
    (Langlands.bidualIntertwining A.representation).isIntertwining'

/-- The full algebraic dual of a finite-dimensional representation has the same rank. -/
@[simp]
theorem rank_dual (A : FiniteRepresentation.{uK, uG, uV} K G) : (dual A).rank = A.rank :=
  Subspace.dual_finrank_eq

/-- On representatives, the class map is the dual. -/
@[simp]
theorem dualClass_classOf (A : FiniteRepresentation.{uK, uG, uV} K G) :
    dualClass (classOf A) = classOf (dual A) := rfl

/-- Duality preserves rank on genuine classes. -/
@[simp]
theorem classRank_dualClass (c : IsomorphismClasses.{uK, uG, uV} K G) :
    classRank (dualClass c) = classRank c := by
  induction c using Quotient.inductionOn with
  | h A => exact rank_dual A

end Algebraic

section Complex

variable {G : Type uG} [Group G]

/-- For complex coefficients the dual is an involution on genuine classes. -/
@[simp]
theorem dualClass_dualClass (c : IsomorphismClasses.{0, uG, uV} ℂ G) :
    dualClass (dualClass c) = c := by
  induction c using Quotient.inductionOn with
  | h A => exact Quotient.sound ⟨(dualDualEquiv A).symm⟩

/-- The dual class map is involutive. -/
theorem dualClass_involutive :
    Function.Involutive (dualClass : IsomorphismClasses.{0, uG, uV} ℂ G →
      IsomorphismClasses.{0, uG, uV} ℂ G) :=
  dualClass_dualClass

/-- The dual as an involutive bijection of the genuine complex classes. -/
def dualClassEquiv : IsomorphismClasses.{0, uG, uV} ℂ G ≃ IsomorphismClasses.{0, uG, uV} ℂ G :=
  dualClass_involutive.toPerm _

@[simp]
theorem dualClassEquiv_apply (c : IsomorphismClasses.{0, uG, uV} ℂ G) :
    dualClassEquiv c = dualClass c := rfl

@[simp]
theorem dualClassEquiv_symm :
    (dualClassEquiv.{uG, uV} (G := G)).symm = dualClassEquiv := rfl

/-- Duality preserves and reflects irreducibility. -/
theorem isIrreducible_dual_iff (A : FiniteRepresentation.{0, uG, uV} ℂ G) :
    (dual A).IsIrreducible ↔ A.IsIrreducible :=
  Weil.OperationClosure.irreducible_dual_iff A.representation

variable [TopologicalSpace G] [IsTopologicalGroup G]

/-- Duality preserves and reflects usual-topology continuity. -/
theorem isContinuous_dual_iff (A : FiniteRepresentation.{0, uG, uV} ℂ G) :
    (dual A).IsContinuous ↔ A.IsContinuous :=
  Weil.OperationClosure.continuous_dual_iff A.representation

/-- The dual of an object carrying the actual continuity and irreducibility certificates. -/
def continuousIrreducibleDual
    (A : {A : FiniteRepresentation.{0, uG, uV} ℂ G // A.IsContinuous ∧ A.IsIrreducible}) :
    {A : FiniteRepresentation.{0, uG, uV} ℂ G // A.IsContinuous ∧ A.IsIrreducible} :=
  ⟨dual A.val, (isContinuous_dual_iff A.val).mpr A.property.1,
    (isIrreducible_dual_iff A.val).mpr A.property.2⟩

/-- Descend the certified dual through the existing property quotient. -/
def continuousIrreducibleDualClass :
    IsomorphismClassesWith (fun A : FiniteRepresentation.{0, uG, uV} ℂ G =>
      A.IsContinuous ∧ A.IsIrreducible) →
    IsomorphismClassesWith (fun A : FiniteRepresentation.{0, uG, uV} ℂ G =>
      A.IsContinuous ∧ A.IsIrreducible) :=
  Quotient.map continuousIrreducibleDual (fun _ _ ⟨e⟩ => ⟨(dualEquiv e).symm⟩)

/-- Forgetting the conditions intertwines the class map with `dualClass`. -/
@[simp]
theorem forget_continuousIrreducibleDualClass
    (c : IsomorphismClassesWith (fun A : FiniteRepresentation.{0, uG, uV} ℂ G =>
      A.IsContinuous ∧ A.IsIrreducible)) :
    forgetPropertyClass _ (continuousIrreducibleDualClass c) =
      dualClass (forgetPropertyClass _ c) := by
  induction c using Quotient.inductionOn with
  | h A => rfl

/-- The certified dual class map is an involution. -/
@[simp]
theorem continuousIrreducibleDualClass_continuousIrreducibleDualClass
    (c : IsomorphismClassesWith (fun A : FiniteRepresentation.{0, uG, uV} ℂ G =>
      A.IsContinuous ∧ A.IsIrreducible)) :
    continuousIrreducibleDualClass (continuousIrreducibleDualClass c) = c := by
  induction c using Quotient.inductionOn with
  | h A => exact Quotient.sound ⟨(dualDualEquiv A.val).symm⟩

/-- The dual as a rank-preserving involutive bijection of the continuous
irreducible rank-`n` classes. -/
def continuousIrreducibleDualEquiv (n : ℕ) :
    ContinuousIrreducibleClasses.{uG, uV} G n ≃ ContinuousIrreducibleClasses.{uG, uV} G n where
  toFun c := ⟨continuousIrreducibleDualClass c.val, by
    have hc := c.property
    change classRank (forgetPropertyClass _ c.val) = n at hc
    change classRank (forgetPropertyClass _ (continuousIrreducibleDualClass c.val)) = n
    rw [forget_continuousIrreducibleDualClass, classRank_dualClass, hc]⟩
  invFun c := ⟨continuousIrreducibleDualClass c.val, by
    have hc := c.property
    change classRank (forgetPropertyClass _ c.val) = n at hc
    change classRank (forgetPropertyClass _ (continuousIrreducibleDualClass c.val)) = n
    rw [forget_continuousIrreducibleDualClass, classRank_dualClass, hc]⟩
  left_inv c := Subtype.ext (continuousIrreducibleDualClass_continuousIrreducibleDualClass c.val)
  right_inv c := Subtype.ext (continuousIrreducibleDualClass_continuousIrreducibleDualClass c.val)

/-- The rank-indexed bijection descends the certified dual of each representative. -/
theorem continuousIrreducibleDualEquiv_mk (n : ℕ)
    (A : FiniteRepresentation.{0, uG, uV} ℂ G)
    (hA : A.IsContinuous ∧ A.IsIrreducible) (hn : A.rank = n) :
    continuousIrreducibleDualEquiv n ⟨Quotient.mk _ ⟨A, hA⟩, hn⟩ =
      ⟨Quotient.mk _ (continuousIrreducibleDual ⟨A, hA⟩), (rank_dual A).trans hn⟩ := rfl

/-- Forgetting the conditions intertwines the bijection with `dualClass`. -/
@[simp]
theorem forget_continuousIrreducibleDualEquiv (n : ℕ)
    (c : ContinuousIrreducibleClasses.{uG, uV} G n) :
    forgetPropertyClass _ (continuousIrreducibleDualEquiv n c).val =
      dualClass (forgetPropertyClass _ c.val) :=
  forget_continuousIrreducibleDualClass c.val

/-- The bijection is its own inverse. -/
@[simp]
theorem continuousIrreducibleDualEquiv_symm (n : ℕ) :
    (continuousIrreducibleDualEquiv.{uG, uV} (G := G) n).symm =
      continuousIrreducibleDualEquiv n := rfl

/-- Applying the dual twice returns the class. -/
@[simp]
theorem continuousIrreducibleDualEquiv_apply_apply (n : ℕ)
    (c : ContinuousIrreducibleClasses.{uG, uV} G n) :
    continuousIrreducibleDualEquiv n (continuousIrreducibleDualEquiv n c) = c :=
  (continuousIrreducibleDualEquiv n).symm_apply_apply c

/-- The bijection composed with itself is the identity. -/
@[simp]
theorem continuousIrreducibleDualEquiv_trans_self (n : ℕ) :
    (continuousIrreducibleDualEquiv.{uG, uV} (G := G) n).trans
      (continuousIrreducibleDualEquiv n) =
      _root_.Equiv.refl (ContinuousIrreducibleClasses.{uG, uV} G n) :=
  (continuousIrreducibleDualEquiv n).self_trans_symm

end Complex

end Langlands.FiniteRepresentation
