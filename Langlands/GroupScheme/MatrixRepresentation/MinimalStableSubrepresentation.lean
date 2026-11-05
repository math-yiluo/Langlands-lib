import Langlands.GroupScheme.MatrixRepresentation.StableSubrepresentation
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-! # Minimal stable subspaces and actual simple subrepresentations -/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry
open scoped Matrix CategoryTheory.MonObj

namespace Langlands.GroupScheme.MatrixRepresentation

variable {k : Type u} [Field k]
  {G : GroupScheme (Spec (CommRingCat.of k))}
  {n m : Type} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]

/-- The zero subspace is stable on every affine test. -/
theorem isStableSubspace_bot (ρ : MatrixRepresentation G n) :
    ρ.IsStableSubspace ⊥ := by
  intro A x v hv ℓ
  have hv0 : v = 0 := hv
  subst v
  change (fun i => ℓ (((ρ.affineMatrix A x : Matrix n n A) *ᵥ
    (fun _ => algebraMap k A 0)) i)) = 0
  funext i
  simp [Matrix.mulVec, dotProduct]

/-- The whole coordinate space is stable on every affine test. -/
theorem isStableSubspace_top (ρ : MatrixRepresentation G n) :
    ρ.IsStableSubspace ⊤ := by
  intro A x v hv ℓ
  trivial

/-- Equivariant images preserve the all-affine-tests stability condition. -/
theorem IsStableSubspace.map {ρ : MatrixRepresentation G n}
    {σ : MatrixRepresentation G m} {C : Matrix m n k}
    {V : Submodule k (n → k)} (hV : ρ.IsStableSubspace V)
    (hC : Intertwines ρ σ C) :
    σ.IsStableSubspace (V.map C.mulVecLin) := by
  rintro A x v ⟨w, hw, rfl⟩ ℓ
  refine ⟨_, hV A x w hw ℓ, ?_⟩
  exact hC.linearFunctional_mulVec A x w ℓ

omit [DecidableEq n] [DecidableEq m] in
/-- Split coordinates whose columns lie in a subspace and whose projection
fixes it have exactly that subspace as their image. -/
theorem range_coordinateInclusion_eq
    (V : Submodule k (n → k)) (B : Matrix n m k) (C : Matrix m n k)
    (hcols : ∀ j, (fun i => B i j) ∈ V)
    (hproj : ∀ v, v ∈ V → (B * C) *ᵥ v = v) :
    LinearMap.range B.mulVecLin = V := by
  apply le_antisymm
  · rw [Matrix.range_mulVecLin]
    apply Submodule.span_le.mpr
    rintro v ⟨j, rfl⟩
    exact hcols j
  · intro v hv
    refine ⟨C *ᵥ v, ?_⟩
    change B *ᵥ (C *ᵥ v) = v
    rw [Matrix.mulVec_mulVec, hproj v hv]

/-- A nonzero finite coordinate representation has a minimal nonzero stable
subspace. Minimality refers to actual all-test stability. -/
theorem exists_minimal_nonzero_stableSubspace [Nontrivial (n → k)]
    (ρ : MatrixRepresentation G n) :
    ∃ V : Submodule k (n → k), ρ.IsStableSubspace V ∧ V ≠ ⊥ ∧
      ∀ W : Submodule k (n → k), ρ.IsStableSubspace W → W ≤ V →
        W = ⊥ ∨ W = V := by
  classical
  let P : ℕ → Prop := fun d =>
    ∃ V : Submodule k (n → k),
      ρ.IsStableSubspace V ∧ V ≠ ⊥ ∧ Module.finrank k V = d
  have hP : ∃ d, P d :=
    ⟨_, ⊤, ρ.isStableSubspace_top, top_ne_bot, rfl⟩
  obtain ⟨V, hV, hV0, hdim⟩ := Nat.find_spec hP
  refine ⟨V, hV, hV0, ?_⟩
  intro W hW hWV
  by_cases hW0 : W = ⊥
  · exact Or.inl hW0
  · right
    apply Submodule.eq_of_le_of_finrank_le hWV
    rw [hdim]
    exact Nat.find_min' hP ⟨W, hW, hW0, rfl⟩

/-- A chosen minimal nonzero subspace stable on every affine test. -/
def minimalNonzeroStableSubspace [Nontrivial (n → k)]
    (ρ : MatrixRepresentation G n) : Submodule k (n → k) :=
  Classical.choose (exists_minimal_nonzero_stableSubspace ρ)

/-- The chosen subspace is nonzero, stable, and minimal among such subspaces. -/
theorem minimalNonzeroStableSubspace_spec [Nontrivial (n → k)]
    (ρ : MatrixRepresentation G n) :
    ρ.IsStableSubspace ρ.minimalNonzeroStableSubspace ∧
      ρ.minimalNonzeroStableSubspace ≠ ⊥ ∧
      ∀ W : Submodule k (n → k), ρ.IsStableSubspace W →
        W ≤ ρ.minimalNonzeroStableSubspace →
        W = ⊥ ∨ W = ρ.minimalNonzeroStableSubspace :=
  Classical.choose_spec (exists_minimal_nonzero_stableSubspace ρ)

/-- Every nonzero representation of an affine group has an actual nonzero
simple subrepresentation, with split injective coordinates. The last two
conjuncts are precisely the nontriviality and stable-subspace conditions used
by the actual irreducibility interface. -/
theorem exists_simple_subrepresentation [IsAffineHom G.X.hom]
    [Nontrivial (n → k)] (ρ : MatrixRepresentation G n) :
    ∃ (d : ℕ) (σ : MatrixRepresentation G (Fin d))
      (B : Matrix n (Fin d) k) (C : Matrix (Fin d) n k),
      C * B = 1 ∧ Intertwines σ ρ B ∧ Nontrivial (Fin d → k) ∧
        ∀ W : Submodule k (Fin d → k), σ.IsStableSubspace W →
          W = ⊥ ∨ W = ⊤ := by
  classical
  obtain ⟨V, hV, hV0, hmin⟩ := exists_minimal_nonzero_stableSubspace ρ
  obtain ⟨d, B, C, hCB, hcols, hproj⟩ := exists_subspace_split_coordinates V
  have hstable := hV.isStableCoordinates B C hcols hproj
  let σ := restrictCoordinates ρ B C hCB hstable
  have hB : Intertwines σ ρ B := intertwines_restrictCoordinates ρ B C hCB hstable
  have hi : Function.Injective B.mulVecLin :=
    coordinateInclusion_injective (R := CommRingCat.of k) B C hCB
  have hrange : LinearMap.range B.mulVecLin = V :=
    range_coordinateInclusion_eq V B C hcols hproj
  have hn : Nontrivial (Fin d → k) := by
    by_contra h
    have : Subsingleton (Fin d → k) := not_nontrivial_iff_subsingleton.mp h
    apply hV0
    rw [← hrange]
    apply LinearMap.range_eq_bot.mpr
    apply LinearMap.ext
    intro v
    have hv : v = 0 := Subsingleton.elim _ _
    rw [hv, map_zero, LinearMap.zero_apply]
  refine ⟨d, σ, B, C, hCB, hB, hn, ?_⟩
  intro W hW
  have hW' := hW.map hB
  have hle : W.map B.mulVecLin ≤ V := by
    rw [← hrange]
    exact LinearMap.map_le_range
  have hmapinj := Submodule.map_injective_of_injective hi
  rcases hmin _ hW' hle with h | h
  · left
    apply hmapinj
    simpa only [Submodule.map_bot] using h
  · right
    apply hmapinj
    simpa only [Submodule.map_top, hrange] using h

end Langlands.GroupScheme.MatrixRepresentation
