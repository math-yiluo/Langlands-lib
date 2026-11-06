import Langlands.GroupScheme.Reductive.InvariantLinearForm
import Langlands.GroupScheme.Reductive.CharZeroSemisimplicity.TangentStability
import Langlands.GroupScheme.MatrixRepresentation.AdditiveFiniteCutoff

/-! # Actual and rational-point irreducibility on the original coordinate space -/

noncomputable section

universe u v

open CategoryTheory AlgebraicGeometry
open scoped Matrix CategoryTheory.MonObj

namespace Langlands.GroupScheme.MatrixRepresentation

variable {k : Type u} [Field k]
  {G : GroupScheme (Spec (CommRingCat.of k))}
  {n : Type} [Fintype n] [DecidableEq n]

/-- An actual irreducible representation has at least one coordinate. -/
theorem IsIrreducible.nonempty_coordinates {ρ : MatrixRepresentation G n}
    (hρ : ρ.IsIrreducible) : Nonempty n := by
  let := hρ.1
  obtain ⟨v, w, hvw⟩ := exists_pair_ne (n → k)
  obtain ⟨i, -⟩ := Function.ne_iff.mp hvw
  exact ⟨i⟩

section Affine

variable [IsAffineHom G.X.hom]

/-- An all-test stable subspace carries the restricted rational-point action. -/
def IsStableSubspace.rationalSubrepresentation {ρ : MatrixRepresentation G n}
    {W : Submodule k (n → k)} (hW : ρ.IsStableSubspace W) :
    Subrepresentation ρ.rationalRepresentation where
  toSubmodule := W
  apply_mem_toSubmodule g _ hv := hW.rationalMatrix_mulVec_mem g hv

@[simp]
theorem IsStableSubspace.rationalSubrepresentation_toSubmodule
    {ρ : MatrixRepresentation G n} {W : Submodule k (n → k)}
    (hW : ρ.IsStableSubspace W) : hW.rationalSubrepresentation.toSubmodule = W := rfl

/-- Rational-point irreducibility implies irreducibility on all affine tests.
No algebraic-closedness, reducedness or characteristic hypothesis is needed. -/
theorem isIrreducible_of_rationalRepresentation (ρ : MatrixRepresentation G n)
    (hρ : ρ.rationalRepresentation.IsIrreducible) : ρ.IsIrreducible := by
  let := hρ
  have hnt : Nontrivial (Submodule k (n → k)) :=
    ⟨⊥, ⊤, fun h => (bot_ne_top : (⊥ : Subrepresentation ρ.rationalRepresentation) ≠ ⊤)
      (Subrepresentation.toSubmodule_injective h)⟩
  refine ⟨(Submodule.nontrivial_iff k).mp hnt, ?_⟩
  intro W hW
  rcases eq_bot_or_eq_top hW.rationalSubrepresentation with h | h
  · exact Or.inl (congrArg Subrepresentation.toSubmodule h)
  · exact Or.inr (congrArg Subrepresentation.toSubmodule h)

section Detection

variable [IsAlgClosed k] [IsReduced G.X.left] [LocallyOfFiniteType G.X.hom]

/-- All-test stable subspaces and rational-point subrepresentations have the
same underlying subspace and the same inclusion order. -/
def rationalSubrepresentationOrderIso (ρ : MatrixRepresentation G n) :
    {W : Submodule k (n → k) // ρ.IsStableSubspace W} ≃o
      Subrepresentation ρ.rationalRepresentation where
  toFun W := W.property.rationalSubrepresentation
  invFun W := ⟨W.toSubmodule, isStableSubspace_of_rationalMatrix ρ W.toSubmodule
    (fun g _ hv => W.apply_mem_toSubmodule g hv)⟩
  left_inv _ := Subtype.ext rfl
  right_inv _ := Subrepresentation.toSubmodule_injective rfl
  map_rel_iff' := Iff.rfl

@[simp]
theorem rationalSubrepresentationOrderIso_toSubmodule (ρ : MatrixRepresentation G n)
    (W : {W : Submodule k (n → k) // ρ.IsStableSubspace W}) :
    (ρ.rationalSubrepresentationOrderIso W).toSubmodule = W.val := rfl

@[simp]
theorem rationalSubrepresentationOrderIso_symm_val (ρ : MatrixRepresentation G n)
    (W : Subrepresentation ρ.rationalRepresentation) :
    (ρ.rationalSubrepresentationOrderIso.symm W).val = W.toSubmodule := rfl

/-- Under rational-point detection, actual irreducibility implies irreducibility
of the original rational-point representation. -/
theorem IsIrreducible.rationalRepresentation {ρ : MatrixRepresentation G n}
    (hρ : ρ.IsIrreducible) : ρ.rationalRepresentation.IsIrreducible := by
  let := hρ.1
  refine { exists_pair_ne := ?_, eq_bot_or_eq_top := ?_ }
  · refine ⟨⊥, ⊤, ?_⟩
    intro h
    exact bot_ne_top (congrArg Subrepresentation.toSubmodule h)
  · intro W
    have hW : ρ.IsStableSubspace W.toSubmodule :=
      (ρ.rationalSubrepresentationOrderIso.symm W).property
    rcases hρ.2 W.toSubmodule hW with h | h
    · exact Or.inl (Subrepresentation.toSubmodule_injective h)
    · exact Or.inr (Subrepresentation.toSubmodule_injective h)

/-- For reduced affine groups locally of finite type over an algebraically
closed field, actual and rational-point irreducibility are equivalent. -/
theorem isIrreducible_iff_rationalRepresentation (ρ : MatrixRepresentation G n) :
    ρ.IsIrreducible ↔ ρ.rationalRepresentation.IsIrreducible :=
  ⟨IsIrreducible.rationalRepresentation, isIrreducible_of_rationalRepresentation ρ⟩

end Detection
end Affine

section EventualTensor

variable {I : Type v} [IsAlgClosed k] [IsReduced G.X.left]
  [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
  (ρ : MatrixRepresentation G n)
  (f : I → (VectorGroup.groupScheme (CommRingCat.of k) 1 ⟶ G))
  (p : ℕ) [Fact p.Prime] [CharP k p]

/-- A supplied rationally irreducible first representation has one exponent
bound for every supplied rationally irreducible second representation. -/
theorem exists_forall_rationalRepresentation_isIrreducible_tensor_frobeniusPower
    (hρ : ρ.rationalRepresentation.IsIrreducible)
    (hgen : IsGeneratedByFamily
      (fun _ : I => VectorGroup.groupScheme (CommRingCat.of k) 1) f (𝟙 G)) :
    ∃ E, ∀ e, E ≤ e →
      ∀ {m : Type} [Fintype m] [DecidableEq m]
        (σ : MatrixRepresentation G m), σ.rationalRepresentation.IsIrreducible →
          (ρ.tensor (σ.frobeniusPower p e)).rationalRepresentation.IsIrreducible := by
  have hρ' := isIrreducible_of_rationalRepresentation ρ hρ
  let := hρ'.nonempty_coordinates
  obtain ⟨E, hE⟩ :=
    AdditiveFiniteCutoff.exists_forall_isIrreducible_tensor_frobeniusPower_of_isGeneratedByFamily
      ρ f p hρ' hgen
  refine ⟨E, ?_⟩
  intro e he m _ _ σ hσ
  have hσ' := isIrreducible_of_rationalRepresentation σ hσ
  let := hσ'.nonempty_coordinates
  exact (hE e he σ hσ').rationalRepresentation

/-- The rational eventual tensor theorem supplies arbitrarily large exponents
on the entire original tensor coordinate space. -/
theorem exists_ge_rationalRepresentation_isIrreducible_tensor_frobeniusPower
    (hρ : ρ.rationalRepresentation.IsIrreducible)
    (hgen : IsGeneratedByFamily
      (fun _ : I => VectorGroup.groupScheme (CommRingCat.of k) 1) f (𝟙 G))
    {m : Type} [Fintype m] [DecidableEq m]
    (σ : MatrixRepresentation G m) (hσ : σ.rationalRepresentation.IsIrreducible)
    (N : ℕ) :
    ∃ e, N ≤ e ∧
      (ρ.tensor (σ.frobeniusPower p e)).rationalRepresentation.IsIrreducible := by
  obtain ⟨E, hE⟩ :=
    exists_forall_rationalRepresentation_isIrreducible_tensor_frobeniusPower ρ f p hρ hgen
  exact ⟨max N E, le_max_left N E, hE _ (le_max_right N E) σ hσ⟩

end EventualTensor

end Langlands.GroupScheme.MatrixRepresentation
