import Langlands.GroupScheme.MatrixRepresentation.MinimalStableSubrepresentation
import Mathlib.Order.CompleteSublattice
import Mathlib.Order.CompactlyGenerated.Basic

/-! # Stable-subspace lattices and semisimple representations -/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry
open scoped Matrix CategoryTheory.MonObj

namespace Langlands.GroupScheme.MatrixRepresentation

variable {k : Type u} [Field k]
  {G : GroupScheme (Spec (CommRingCat.of k))}
  {n : Type} [Fintype n] [DecidableEq n]

/-- The ground-field endomorphism obtained from one linear coefficient of an
actual affine-test matrix. Test algebras need not be reduced. -/
def affineCoefficientEndomorphism (ρ : MatrixRepresentation G n)
    (A : CommAlgCat.{u} (CommRingCat.of k))
    (x : (algSpec (CommRingCat.of k)).obj (op A) ⟶ G.X)
    (ℓ : A →ₗ[k] k) : Module.End k (n → k) :=
  Matrix.mulVecLin (fun i j => ℓ ((ρ.affineMatrix A x : Matrix n n A) i j))

/-- Coefficient extraction is the action of the coefficient endomorphism. -/
theorem affineCoefficientEndomorphism_apply (ρ : MatrixRepresentation G n)
    (A : CommAlgCat.{u} (CommRingCat.of k))
    (x : (algSpec (CommRingCat.of k)).obj (op A) ⟶ G.X)
    (ℓ : A →ₗ[k] k) (v : n → k) :
    ρ.affineCoefficientEndomorphism A x ℓ v =
      fun i => ℓ (((ρ.affineMatrix A x : Matrix n n A) *ᵥ
        (fun j => algebraMap k A (v j))) i) := by
  have hs (a : A) (c : k) : ℓ (a * algebraMap k A c) = c * ℓ a := by
    rw [mul_comm, ← Algebra.smul_def, map_smul, smul_eq_mul]
  ext i
  change (∑ j, ℓ ((ρ.affineMatrix A x : Matrix n n A) i j) * v j) =
    ℓ (∑ j, (ρ.affineMatrix A x : Matrix n n A) i j * algebraMap k A (v j))
  simp only [map_sum, hs, mul_comm]

/-- An arbitrary intersection of stable subspaces is stable. -/
theorem IsStableSubspace.sInf {ρ : MatrixRepresentation G n}
    {S : Set (Submodule k (n → k))} (hS : ∀ V ∈ S, ρ.IsStableSubspace V) :
    ρ.IsStableSubspace (sInf S) := by
  intro A x v hv ℓ
  rw [Submodule.mem_sInf] at hv ⊢
  intro V hV
  exact hS V hV A x v (hv V hV) ℓ

/-- An arbitrary sum of stable subspaces is stable. -/
theorem IsStableSubspace.iSup {ρ : MatrixRepresentation G n}
    {J : Sort*} {V : J → Submodule k (n → k)}
    (hV : ∀ i, ρ.IsStableSubspace (V i)) :
    ρ.IsStableSubspace (⨆ i, V i) := by
  intro A x v hv ℓ
  rw [← affineCoefficientEndomorphism_apply]
  let f := ρ.affineCoefficientEndomorphism A x ℓ
  change f v ∈ ⨆ i, V i
  refine Submodule.iSup_induction V (motive := fun w => f w ∈ ⨆ i, V i) hv ?_ ?_ ?_
  · intro i w hw
    exact Submodule.mem_iSup_of_mem i <| by
      rw [affineCoefficientEndomorphism_apply]
      exact hV i A x w hw ℓ
  · simpa only [map_zero] using (⨆ i, V i).zero_mem
  · intro v w hv hw
    simpa only [map_add] using (⨆ i, V i).add_mem hv hw

/-- A set-indexed sum of stable subspaces is stable. -/
theorem IsStableSubspace.sSup {ρ : MatrixRepresentation G n}
    {S : Set (Submodule k (n → k))} (hS : ∀ V ∈ S, ρ.IsStableSubspace V) :
    ρ.IsStableSubspace (sSup S) := by
  rw [sSup_eq_iSup']
  exact IsStableSubspace.iSup (fun V => hS V V.property)

/-- A binary intersection of stable subspaces is stable. -/
theorem IsStableSubspace.inf {ρ : MatrixRepresentation G n}
    {V W : Submodule k (n → k)} (hV : ρ.IsStableSubspace V)
    (hW : ρ.IsStableSubspace W) : ρ.IsStableSubspace (V ⊓ W) := by
  intro A x v hv ℓ
  exact ⟨hV A x v hv.1 ℓ, hW A x v hv.2 ℓ⟩

/-- A binary sum of stable subspaces is stable. -/
theorem IsStableSubspace.sup {ρ : MatrixRepresentation G n}
    {V W : Submodule k (n → k)} (hV : ρ.IsStableSubspace V)
    (hW : ρ.IsStableSubspace W) : ρ.IsStableSubspace (V ⊔ W) := by
  have h : ∀ U ∈ ({V, W} : Set (Submodule k (n → k))),
      ρ.IsStableSubspace U := by
    intro U hU
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hU
    rcases hU with rfl | rfl
    · exact hV
    · exact hW
  simpa only [sSup_pair] using IsStableSubspace.sSup h

/-- All-test stable subspaces form a complete sublattice of the ordinary
subspace lattice. Its atoms are the simple subrepresentations. -/
def stableSubspaceLattice (ρ : MatrixRepresentation G n) :
    CompleteSublattice (Submodule k (n → k)) :=
  CompleteSublattice.mk' {V | ρ.IsStableSubspace V}
    (fun {_} hS => IsStableSubspace.sSup hS)
    (fun {_} hS => IsStableSubspace.sInf hS)

instance (ρ : MatrixRepresentation G n) :
    IsModularLattice ρ.stableSubspaceLattice where
  sup_inf_le_assoc_of_le {_} y {_} h :=
    (sup_inf_le_assoc_of_le (y : Submodule k (n → k)) h)

instance (ρ : MatrixRepresentation G n) :
    IsCompactlyGenerated ρ.stableSubspaceLattice :=
  CompleteLattice.isCompactlyGenerated_of_wellFoundedGT

/-- Semisimplicity is exactly the sum-of-simple-subspaces condition used in
Nagata's theorem. This definition includes the zero representation. -/
def IsSemisimple (ρ : MatrixRepresentation G n) : Prop :=
  sSup {W : Submodule k (n → k) | ρ.IsStableSubspace W ∧ W ≠ ⊥ ∧
    ∀ U : Submodule k (n → k), ρ.IsStableSubspace U → U ≤ W →
      U = ⊥ ∨ U = W} = ⊤

/-- Atoms of the stable-subspace lattice are precisely the nonzero stable
subspaces with no proper nonzero stable subspace. -/
theorem stableSubspaceLattice_isAtom_iff (ρ : MatrixRepresentation G n)
    (W : ρ.stableSubspaceLattice) :
    IsAtom W ↔ (W : Submodule k (n → k)) ≠ ⊥ ∧
      ∀ U : Submodule k (n → k), ρ.IsStableSubspace U →
        U ≤ (W : Submodule k (n → k)) → U = ⊥ ∨ U = W := by
  constructor
  · intro hW
    refine ⟨fun h => hW.ne_bot (Subtype.ext h), ?_⟩
    intro U hU hUW
    have h := hW.le_iff.mp (show (⟨U, hU⟩ : ρ.stableSubspaceLattice) ≤ W from hUW)
    exact h.imp (congrArg Subtype.val) (congrArg Subtype.val)
  · rintro ⟨hW0, hW⟩
    refine ⟨fun h => hW0 (congrArg Subtype.val h), ?_⟩
    intro U hU
    rcases hW U U.property hU.le with h | h
    · exact Subtype.ext h
    · exact False.elim (hU.ne (Subtype.ext h))

/-- Coercion identifies the sum of lattice atoms with the sum of simple
subrepresentations in the ambient coordinate space. -/
theorem stableSubspaceLattice_sSup_atoms_coe (ρ : MatrixRepresentation G n) :
    ((sSup {W : ρ.stableSubspaceLattice | IsAtom W} : ρ.stableSubspaceLattice) :
      Submodule k (n → k)) =
      sSup {W : Submodule k (n → k) | ρ.IsStableSubspace W ∧ W ≠ ⊥ ∧
        ∀ U : Submodule k (n → k), ρ.IsStableSubspace U → U ≤ W →
          U = ⊥ ∨ U = W} := by
  rw [CompleteSublattice.coe_sSup]
  congr 1
  ext W
  constructor
  · rintro ⟨U, hU, rfl⟩
    exact ⟨U.property, (stableSubspaceLattice_isAtom_iff ρ U).mp hU⟩
  · rintro ⟨hW, hW0, hmin⟩
    exact ⟨⟨W, hW⟩, (stableSubspaceLattice_isAtom_iff ρ _).mpr ⟨hW0, hmin⟩, rfl⟩

/-- Semisimplicity is equivalent to existence of a stable complementary
subspace for every stable subspace. -/
theorem isSemisimple_iff_exists_stable_complement (ρ : MatrixRepresentation G n) :
    ρ.IsSemisimple ↔ ∀ V : Submodule k (n → k), ρ.IsStableSubspace V →
      ∃ W : Submodule k (n → k), ρ.IsStableSubspace W ∧ IsCompl V W := by
  have hsup : sSup {W : ρ.stableSubspaceLattice | IsAtom W} = ⊤ ↔
      ρ.IsSemisimple := by
    rw [← Subtype.coe_injective.eq_iff, stableSubspaceLattice_sSup_atoms_coe]
    rfl
  change ρ.IsSemisimple ↔ ∀ V ∈ ρ.stableSubspaceLattice,
    ∃ W ∈ ρ.stableSubspaceLattice, IsCompl V W
  rw [← (CompleteSublattice.isComplemented_iff (L := ρ.stableSubspaceLattice))]
  constructor
  · intro h
    exact complementedLattice_of_sSup_atoms_eq_top (hsup.mpr h)
  · intro h
    let := h
    exact hsup.mp sSup_atoms_eq_top

end Langlands.GroupScheme.MatrixRepresentation
