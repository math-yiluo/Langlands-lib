import Langlands.Cohomology.GaloisCovering
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs

/-! # Pullback of a Galois covering on a site -/

noncomputable section

universe u v w

namespace Langlands.Cohomology.GaloisCovering

open CategoryTheory CategoryTheory.Limits

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  {Γ : Type w} [Group Γ] {V' V B P : C}
  (G : GaloisCovering J Γ V' V)
  {a : P ⟶ V'} {p' : P ⟶ B} {b : B ⟶ V} (h : IsPullback a p' G.p b)

/-- An existing pullback of a Galois covering is a Galois covering with the same group.
The pullback projections determine the lifted deck transformations. -/
def pullback : GaloisCovering J Γ P B := by
  let deck' (γ : Γ) : P ⟶ P :=
    h.lift (a ≫ G.deck γ) p' (by rw [Category.assoc, G.deck_comp, h.w])
  have hd₁ (γ : Γ) : deck' γ ≫ a = a ≫ G.deck γ := h.lift_fst _ _ _
  have hd₂ (γ : Γ) : deck' γ ≫ p' = p' := h.lift_snd _ _ _
  refine ⟨p', ?_, deck', ?_, ?_, hd₂, ?_, ?_⟩
  · rw [Sieve.ofArrows_eq_pullback_of_isPullback (fun _ : Unit => G.p) (fun _ => h.flip)]
    exact J.pullback_stable b G.covering
  · apply h.hom_ext
    · simp only [hd₁, G.deck_one, Category.comp_id, Category.id_comp]
    · simp only [hd₂, Category.id_comp]
  · intro γ δ
    apply h.hom_ext
    · rw [hd₁, Category.assoc, hd₁, ← Category.assoc, hd₁, Category.assoc, G.deck_mul]
    · simp only [Category.assoc, hd₂]
  · intro U f g hfg
    have hproj : (f ≫ a) ≫ G.p = (g ≫ a) ≫ G.p := by
      rw [Category.assoc, Category.assoc, h.w, ← Category.assoc, ← Category.assoc, hfg]
    apply J.superset_covering _ (G.locally_transitive (f ≫ a) (g ≫ a) hproj)
    rintro W k ⟨γ, hk⟩
    refine ⟨γ, h.hom_ext ?_ ?_⟩
    · simpa only [Category.assoc, hd₁] using hk
    · simpa only [Category.assoc, hd₂] using congrArg (fun l : U ⟶ B => k ≫ l) hfg.symm
  · intro U f γ hf
    apply G.locally_free (f ≫ a) γ
    simpa only [Category.assoc, hd₁] using congrArg (fun k : U ⟶ P => k ≫ a) hf

@[simp]
theorem pullback_p : (G.pullback h).p = p' := rfl

@[reassoc (attr := simp)]
theorem pullback_deck_fst (γ : Γ) : (G.pullback h).deck γ ≫ a = a ≫ G.deck γ := by
  simp only [pullback, IsPullback.lift_fst]

end Langlands.Cohomology.GaloisCovering
