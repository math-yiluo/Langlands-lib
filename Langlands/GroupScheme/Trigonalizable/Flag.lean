import Langlands.GroupScheme.Trigonalizable.StableLines
import Langlands.GroupScheme.MatrixRepresentation.QuotientCoordinates
import Langlands.GroupScheme.MatrixRepresentation.MinimalStableSubrepresentation

/-! # Trigonalizable groups and stable flags (Milne 16.2, (a) ⇔ (b))

An affine group over a field is trigonalizable exactly when every finite-dimensional matrix
representation stabilizes a maximal flag of subspaces. The forward direction is an induction on
the dimension: a stable line is split off and the induction hypothesis is applied to the quotient
representation. The backward direction reads off the one-dimensional term of the flag.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped Matrix

namespace Langlands.GroupScheme

open MatrixRepresentation

namespace Trigonalizable

/-- Rank-nullity for preimages: along a surjective linear map, the preimage of a subspace has the
dimension of the subspace plus the dimension of the kernel. -/
theorem finrank_comap_of_surjective {K E F : Type*} [Field K] [AddCommGroup E] [Module K E]
    [FiniteDimensional K E] [AddCommGroup F] [Module K F] {f : E →ₗ[K] F}
    (hf : Function.Surjective f) (U : Submodule K F) :
    Module.finrank K (U.comap f) = Module.finrank K U + Module.finrank K (LinearMap.ker f) := by
  have h := LinearMap.finrank_range_add_finrank_ker (f.domRestrict (U.comap f))
  rw [LinearMap.range_domRestrict, Submodule.map_comap_eq_of_surjective hf,
    LinearMap.ker_domRestrict,
    (Submodule.comapSubtypeEquivOfLe (LinearMap.ker_le_comap f)).finrank_eq] at h
  exact h.symm

variable {k : Type u} [Field k] {G : GroupScheme (Spec (CommRingCat.of k))}

/-- The quotient of a representation by the line spanned by a nonzero vector has one dimension
less than the representation. -/
theorem dimension_add_one_of_line {n : Type} [Fintype n] [DecidableEq n]
    {ρ : MatrixRepresentation G n} {v : n → k} (hv : v ≠ 0)
    (q : QuotientRepresentation ρ (k ∙ v)) : q.dimension + 1 = Fintype.card n := by
  have h := LinearMap.finrank_range_add_finrank_ker q.projection.mulVecLin
  rw [LinearMap.range_eq_top.mpr q.projection_surjective, finrank_top, q.ker_projection,
    finrank_span_singleton hv, Module.finrank_fintype_fun_eq_card,
    Module.finrank_fintype_fun_eq_card, Fintype.card_fin] at h
  exact h

/-- Milne 16.2, (a) ⇒ (b), in a form suited to induction on the dimension `d`: every
representation of a trigonalizable affine group on a `d`-dimensional coordinate space stabilizes
a maximal flag. -/
theorem exists_stableFlag_of_card_eq [IsAffineHom G.X.hom] (hG : IsTrigonalizable G) :
    ∀ (d : ℕ) (n : Type) [Fintype n] [DecidableEq n] (ρ : MatrixRepresentation G n),
      Fintype.card n = d →
        ∃ W : Fin (d + 1) → Submodule k (n → k),
          Monotone W ∧ (∀ i, Module.finrank k (W i) = i.val) ∧
            ∀ i, ρ.IsStableSubspace (W i) := by
  intro d
  induction d with
  | zero =>
    intro n _ _ ρ _
    refine ⟨fun _ => ⊥, fun _ _ _ => le_rfl, fun i => ?_, fun _ => isStableSubspace_bot ρ⟩
    rw [finrank_bot, Fin.val_eq_zero i]
  | succ d ih =>
    intro n _ _ ρ hcard
    have : Nonempty n := Fintype.card_pos_iff.mp (by omega)
    obtain ⟨v, hv0, hv⟩ := hG n ρ
    obtain ⟨q⟩ := nonempty_quotientRepresentation ρ (k ∙ v) hv.isStableSubspace
    have hdim : q.dimension = d := by
      have := dimension_add_one_of_line hv0 q
      omega
    obtain ⟨W', hmono, hrank, hstable⟩ :=
      ih (Fin q.dimension) q.representation (by rw [Fintype.card_fin, hdim])
    let W : Fin (d + 1 + 1) → Submodule k (n → k) :=
      Fin.cons ⊥ fun i => (W' i).comap q.projection.mulVecLin
    have hW0 : W 0 = ⊥ := Fin.cons_zero _ _
    have hWs (i : Fin (d + 1)) : W i.succ = (W' i).comap q.projection.mulVecLin :=
      Fin.cons_succ _ _ _
    refine ⟨W, ?_, ?_, ?_⟩
    · intro i j hij
      induction i using Fin.cases with
      | zero => rw [hW0]; exact bot_le
      | succ i =>
        induction j using Fin.cases with
        | zero => exact absurd hij (Fin.succ_pos i).not_ge
        | succ j =>
          rw [hWs, hWs]
          exact Submodule.comap_mono (hmono (Fin.succ_le_succ_iff.mp hij))
    · intro i
      induction i using Fin.cases with
      | zero => rw [hW0, finrank_bot, Fin.val_zero]
      | succ i =>
        rw [hWs, finrank_comap_of_surjective q.projection_surjective, hrank, q.ker_projection,
          finrank_span_singleton hv0, Fin.val_succ]
    · intro i
      induction i using Fin.cases with
      | zero => rw [hW0]; exact isStableSubspace_bot ρ
      | succ i => rw [hWs]; exact (hstable i).comap q.intertwines

/-- Milne 16.2, (b) ⇒ (a): if every representation stabilizes a maximal flag, then the
one-dimensional term of the flag of a nonzero representation is a stable line. -/
theorem isTrigonalizable_of_exists_stableFlag [IsAffineHom G.X.hom]
    (h : ∀ (n : Type) [Fintype n] [DecidableEq n] (ρ : MatrixRepresentation G n),
      ∃ W : Fin (Fintype.card n + 1) → Submodule k (n → k),
        Monotone W ∧ (∀ i, Module.finrank k (W i) = i.val) ∧
          ∀ i, ρ.IsStableSubspace (W i)) :
    IsTrigonalizable G := by
  intro n _ _ _ ρ
  obtain ⟨W, -, hrank, hstable⟩ := h n ρ
  have hpos : 0 < Fintype.card n := Fintype.card_pos
  let i₁ : Fin (Fintype.card n + 1) := ⟨1, by omega⟩
  obtain ⟨w, hw0, hw⟩ := finrank_eq_one_iff'.mp (hrank i₁)
  have hspan : W i₁ = k ∙ (w : n → k) := by
    apply le_antisymm
    · intro x hx
      obtain ⟨c, hc⟩ := hw ⟨x, hx⟩
      exact Submodule.mem_span_singleton.mpr ⟨c, congrArg Subtype.val hc⟩
    · rw [Submodule.span_singleton_le_iff_mem]
      exact w.2
  refine ⟨w, fun h0 => hw0 (Subtype.ext h0), ?_⟩
  apply isStableLine_of_isStableSubspace
  rw [← hspan]
  exact hstable i₁

/-- Milne 16.2, (a) ⇔ (b): an affine group over a field is trigonalizable exactly when every
finite-dimensional matrix representation stabilizes a maximal flag. -/
theorem isTrigonalizable_iff_exists_stableFlag [IsAffineHom G.X.hom] :
    IsTrigonalizable G ↔
      ∀ (n : Type) [Fintype n] [DecidableEq n] (ρ : MatrixRepresentation G n),
        ∃ W : Fin (Fintype.card n + 1) → Submodule k (n → k),
          Monotone W ∧ (∀ i, Module.finrank k (W i) = i.val) ∧
            ∀ i, ρ.IsStableSubspace (W i) :=
  ⟨fun hG n _ _ ρ => exists_stableFlag_of_card_eq hG _ n ρ rfl,
    isTrigonalizable_of_exists_stableFlag⟩

end Trigonalizable

end Langlands.GroupScheme
