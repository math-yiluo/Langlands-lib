import Langlands.Group.GL.Blocks
import Mathlib.Analysis.Complex.Basic
import Mathlib.CategoryTheory.IsomorphismClasses
import Mathlib.RepresentationTheory.Irreducible
import Mathlib.RepresentationTheory.Rep.Basic

/-!
# Cuspidal complex representations of general linear groups over finite fields

Harish-Chandra's condition: no nonzero vector is fixed by the unipotent radical of a
proper standard block parabolic. The isomorphism classes of irreducible cuspidal
representations form a quotient of a full subcategory of Mathlib's `Rep`, at an
explicit carrier universe.
-/

noncomputable section

open CategoryTheory

namespace Langlands.FiniteGeneralLinear

/-- Harish-Chandra cuspidality: for every ordered block shape whose standard upper block
parabolic is proper, the only vector fixed by its block unipotent radical is zero. -/
def IsCuspidal {k : Type*} [Field k] {n : ℕ} {V : Type*} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ (GeneralLinear n k) V) : Prop :=
  ∀ B : GeneralLinear.BlockShape n, B.parabolic k ≠ ⊤ →
    ∀ v : V, (∀ u ∈ B.unipotentSubgroup k, ρ u v = v) → v = 0

/-- Cuspidality is invariant under equivalence of representations, including between
different carrier universes. -/
theorem IsCuspidal.of_equiv {k : Type*} [Field k] {n : ℕ}
    {V : Type*} [AddCommGroup V] [Module ℂ V] {W : Type*} [AddCommGroup W] [Module ℂ W]
    {ρ : Representation ℂ (GeneralLinear n k) V} {σ : Representation ℂ (GeneralLinear n k) W}
    (e : ρ.Equiv σ) (hρ : IsCuspidal ρ) : IsCuspidal σ := by
  intro B hB w hw
  have h0 : e.symm w = 0 := by
    refine hρ B hB (e.symm w) fun u hu => ?_
    have h := Representation.IntertwiningMap.isIntertwining _ _ e.symm.toIntertwiningMap u w
    simp only [Representation.Equiv.coe_toIntertwiningMap] at h
    rw [← h, hw u hu]
  simpa using congrArg e h0

theorem isCuspidal_iff_of_equiv {k : Type*} [Field k] {n : ℕ}
    {V : Type*} [AddCommGroup V] [Module ℂ V] {W : Type*} [AddCommGroup W] [Module ℂ W]
    {ρ : Representation ℂ (GeneralLinear n k) V} {σ : Representation ℂ (GeneralLinear n k) W}
    (e : ρ.Equiv σ) : IsCuspidal ρ ↔ IsCuspidal σ :=
  ⟨IsCuspidal.of_equiv e, IsCuspidal.of_equiv e.symm⟩

/-- The irreducible cuspidal objects of Mathlib's category of complex representations
of `GL_n(k)` on carriers in `Type w`. -/
def cuspidalProperty.{u, w} (n : ℕ) (k : Type u) [Field k] :
    ObjectProperty (Rep.{w} ℂ (GeneralLinear n k)) :=
  fun A => A.ρ.IsIrreducible ∧ IsCuspidal A.ρ

/-- The full subcategory of irreducible cuspidal complex representations of `GL_n(k)`
on carriers in `Type w`. -/
abbrev CuspidalRep.{u, w} (n : ℕ) (k : Type u) [Field k] :=
  (cuspidalProperty.{u, w} n k).FullSubcategory

/-- Isomorphism classes of irreducible cuspidal complex representations of `GL_n(k)`
on carriers in `Type w`, without resizing. -/
def CuspidalClass.{u, w} (n : ℕ) (k : Type u) [Field k] :=
  Quotient (isIsomorphicSetoid (CuspidalRep.{u, w} n k))

namespace CuspidalRep

universe u w

variable {n : ℕ} {k : Type u} [Field k]

/-- Bundle an irreducible cuspidal representation on a carrier in `Type w`. -/
def of {V : Type w} [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ (GeneralLinear n k) V)
    (hirr : ρ.IsIrreducible) (hcusp : IsCuspidal ρ) : CuspidalRep.{u, w} n k :=
  ⟨Rep.of ρ, show ρ.IsIrreducible ∧ IsCuspidal ρ from ⟨hirr, hcusp⟩⟩

theorem isIrreducible (A : CuspidalRep.{u, w} n k) : A.obj.ρ.IsIrreducible := A.property.1

theorem isCuspidal (A : CuspidalRep.{u, w} n k) : IsCuspidal A.obj.ρ := A.property.2

/-- The isomorphism class of an object. -/
def isoClass (A : CuspidalRep.{u, w} n k) : CuspidalClass.{u, w} n k :=
  Quotient.mk _ A

/-- Two objects have the same class exactly when their representations are equivalent. -/
theorem isoClass_eq_iff (A B : CuspidalRep.{u, w} n k) :
    A.isoClass = B.isoClass ↔ Nonempty (A.obj.ρ.Equiv B.obj.ρ) := by
  constructor
  · intro h
    obtain ⟨e⟩ := Quotient.exact h
    exact ⟨Representation.equivOfIso ((cuspidalProperty.{u, w} n k).ι.mapIso e)⟩
  · rintro ⟨e⟩
    exact Quotient.sound ⟨ObjectProperty.isoMk _ (Rep.mkIso e)⟩

theorem isoClass_surjective :
    Function.Surjective (isoClass : CuspidalRep.{u, w} n k → CuspidalClass.{u, w} n k) :=
  Quotient.mk_surjective

end CuspidalRep

end Langlands.FiniteGeneralLinear
