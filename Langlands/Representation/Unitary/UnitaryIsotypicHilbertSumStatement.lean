import Mathlib.Analysis.InnerProductSpace.l2Space

/-! # Isotypic components of a unitary Hilbert sum -/

noncomputable section

set_option autoImplicit false

namespace Langlands.Analysis

universe uG uE

variable {G : Type uG} [Group G]
  {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  (π : G →* (E →L[ℂ] E))

/-- A nonzero closed invariant subspace with no proper nonzero closed invariant subspace. -/
def IsIrreducibleInvariantSubspace (P : Submodule ℂ E) : Prop :=
  P ≠ ⊥ ∧ IsClosed (P : Set E) ∧
    (∀ g, ∀ x ∈ P, π g x ∈ P) ∧
    ∀ Q : Submodule ℂ E, Q ≤ P → IsClosed (Q : Set E) →
      (∀ g, ∀ x ∈ Q, π g x ∈ Q) → Q = ⊥ ∨ Q = P

/-- The restricted actions are intertwined by a surjective linear isometry. -/
def UnitarilyEquivalentSubspaces (P Q : Submodule ℂ E)
    (hP : ∀ g, ∀ x ∈ P, π g x ∈ P) : Prop :=
  ∃ U : P ≃ₗᵢ[ℂ] Q, ∀ g (x : P), (U ⟨π g x, hP g x x.2⟩ : E) = π g (U x)

variable {π}

theorem UnitarilyEquivalentSubspaces.symm {P Q : Submodule ℂ E}
    {hP : ∀ g, ∀ x ∈ P, π g x ∈ P} {hQ : ∀ g, ∀ x ∈ Q, π g x ∈ Q}
    (h : UnitarilyEquivalentSubspaces π P Q hP) :
    UnitarilyEquivalentSubspaces π Q P hQ := by
  obtain ⟨U, hU⟩ := h
  refine ⟨U.symm, fun g x => ?_⟩
  have heq : U (⟨π g (U.symm x), hP g _ (U.symm x).2⟩ : P) =
      (⟨π g x, hQ g x x.2⟩ : Q) := by
    apply Subtype.ext
    simpa only [LinearIsometryEquiv.apply_symm_apply] using hU g (U.symm x)
  rw [← heq, LinearIsometryEquiv.symm_apply_apply]

theorem UnitarilyEquivalentSubspaces.trans {P Q R : Submodule ℂ E}
    {hP : ∀ g, ∀ x ∈ P, π g x ∈ P} {hQ : ∀ g, ∀ x ∈ Q, π g x ∈ Q}
    (h₁ : UnitarilyEquivalentSubspaces π P Q hP)
    (h₂ : UnitarilyEquivalentSubspaces π Q R hQ) :
    UnitarilyEquivalentSubspaces π P R hP := by
  obtain ⟨U, hU⟩ := h₁
  obtain ⟨V, hV⟩ := h₂
  refine ⟨U.trans V, fun g x => ?_⟩
  have heq : U (⟨π g x, hP g x x.2⟩ : P) =
      (⟨π g (U x), hQ g _ (U x).2⟩ : Q) := Subtype.ext (hU g x)
  change (V (U ⟨π g x, hP g x x.2⟩) : E) = π g (V (U x))
  rw [heq]
  exact hV g (U x)

variable (π)

/-- The equivalence relation of unitary isomorphism on a family of invariant subspaces. -/
def subspaceUnitarySetoid {A : Set (Submodule ℂ E)}
    (hA : ∀ P ∈ A, ∀ g, ∀ x ∈ P, π g x ∈ P) : Setoid A where
  r P Q := UnitarilyEquivalentSubspaces π P.val Q.val (hA P.val P.property)
  iseqv := {
    refl := fun _ => ⟨LinearIsometryEquiv.refl ℂ _, fun _ _ => rfl⟩
    symm := fun h => h.symm
    trans := fun h₁ h₂ => h₁.trans h₂ }

/-- The finite sums within the unitary equivalence classes give an internal Hilbert sum
of invariant subspaces. Each class projection is the sum of the original projections.
The component of a class is the span of all irreducible subspaces of that class. -/
def UnitaryIsotypicHilbertSum [CompleteSpace E] {A : Set (Submodule ℂ E)}
    (hA : ∀ P ∈ A, IsIrreducibleInvariantSubspace π P) : Prop :=
  let s := subspaceUnitarySetoid π (fun P hP => (hA P hP).2.2.1)
  let label : A → Quotient s := Quotient.mk s
  let C (b : Quotient s) := ⨆ P : {P : A // label P = b}, P.val.val
  letI (P : A) : CompleteSpace P.val := (hA P.val P.property).2.1.completeSpace_coe
  ∃ hFinite : ∀ b : Quotient s, Finite {P : A // label P = b},
    letI (b : Quotient s) : Finite {P : A // label P = b} := hFinite b
    letI (b : Quotient s) : Fintype {P : A // label P = b} := Fintype.ofFinite _
    ∃ hClosed : ∀ b : Quotient s, IsClosed (C b : Set E),
      letI (b : Quotient s) : CompleteSpace (C b) := (hClosed b).completeSpace_coe
      IsHilbertSum ℂ (fun b => ↥(C b)) (fun b => (C b).subtypeₗᵢ) ∧
      (∀ g b, ∀ x ∈ C b, π g x ∈ C b) ∧
      (∀ b (x : E), (C b).starProjection x =
        ∑ P : {P : A // label P = b}, P.val.val.starProjection x) ∧
      ∀ P : A, C (label P) =
        sSup {Q : Submodule ℂ E | ∃ hQ : IsIrreducibleInvariantSubspace π Q,
          UnitarilyEquivalentSubspaces π Q P.val hQ.2.2.1}

/-- An internal Hilbert sum of irreducible unitary summands with finite multiplicities
regroups by unitary equivalence into its intrinsic isotypic components. -/
def UnitaryIsotypicHilbertSumStatement : Prop :=
  ∀ (G : Type uG) [Group G]
    (E : Type uE) [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    (π : G →* (E →L[ℂ] E)),
    (∀ g x y, inner ℂ (π g x) (π g y) = inner ℂ x y) →
    ∀ (A : Set (Submodule ℂ E)) (hA : ∀ P ∈ A, IsIrreducibleInvariantSubspace π P),
      IsHilbertSum ℂ (fun P : A => ↥P.val) (fun P => P.val.subtypeₗᵢ) →
      (∀ P ∈ A, ∀ hP : (∀ g, ∀ x ∈ P, π g x ∈ P),
        {Q : Submodule ℂ E | Q ∈ A ∧ UnitarilyEquivalentSubspaces π P Q hP}.Finite) →
      UnitaryIsotypicHilbertSum π hA

end Langlands.Analysis
