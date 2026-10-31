import Langlands.Representation.Induction.Definitions
import Langlands.Representation.Filtration.GeneralizedEigencharacterProof

/-! evaluation transport for uniform generalized characters in smooth induction. -/

noncomputable section

namespace Langlands.Induction

universe uR uG uA uV

variable {R : Type uR} [CommRing R]
  {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {A : Type uA} [Monoid A]
  {V : Type uV} [AddCommGroup V] [Module R V]

/-- Evaluation intertwines restriction along a homomorphism whose image is
central in the ambient group. -/
def centralEvaluation (P : Subgroup G) (σ : Representation R P V)
    (ι : A →* P) (hι : ∀ a : A, ∀ g : G, (ι a : G) * g = g * ι a)
    (x : G) :
    Representation.IntertwiningMap
      ((smoothInduced P σ).comp (P.subtype.comp ι)) (σ.comp ι) where
  toFun f := eval P σ f x
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  isIntertwining' a := by
    ext f
    change f.1.1 (x * (ι a : G)) = σ (ι a) (f.1.1 x)
    rw [← hι a x]
    exact f.1.2 (ι a) x

@[simp]
theorem centralEvaluation_apply (P : Subgroup G) (σ : Representation R P V)
    (ι : A →* P) (hι : ∀ a : A, ∀ g : G, (ι a : G) * g = g * ι a)
    (x : G) (f : SmoothFunctions P σ) :
    centralEvaluation P σ ι hι x f = eval P σ f x := rfl

/-- The same finite exponent works at every evaluation. -/
theorem eval_mem_characterSpace (P : Subgroup G) (σ : Representation R P V)
    (ι : A →* P) (hι : ∀ a : A, ∀ g : G, (ι a : G) * g = g * ι a)
    (χ : A →* Rˣ) (k : ℕ) {f : SmoothFunctions P σ}
    (hf : f ∈ characterSpace ((smoothInduced P σ).comp (P.subtype.comp ι)) χ k)
    (x : G) :
    eval P σ f x ∈ characterSpace (σ.comp ι) χ k :=
  map_mem_characterSpace_of_intertwiningMap
    (centralEvaluation P σ ι hι x) χ k hf

omit [IsTopologicalGroup G] in
/-- A nonzero smooth induced function has a nonzero value. -/
theorem exists_smoothInduced_eval_ne_zero (P : Subgroup G) (σ : Representation R P V)
    {f : SmoothFunctions P σ} (hf : f ≠ 0) :
    ∃ x : G, eval P σ f x ≠ 0 := by
  classical
  by_contra h
  simp only [not_exists, not_not] at h
  apply hf
  apply Subtype.ext
  apply Subtype.ext
  funext x
  exact h x

/-- An actual generalized character in a central restriction of smooth
induction occurs in the same restriction of its actual inducing action. -/
theorem smoothInduced_isGeneralizedEigencharacter_reflects
    (P : Subgroup G) (σ : Representation R P V)
    (ι : A →* P) (hι : ∀ a : A, ∀ g : G, (ι a : G) * g = g * ι a)
    (χ : A →* Rˣ)
    (hχ : IsGeneralizedEigencharacter
      ((smoothInduced P σ).comp (P.subtype.comp ι)) χ) :
    IsGeneralizedEigencharacter (σ.comp ι) χ := by
  obtain ⟨k, f, hf0, hf⟩ := (isGeneralizedEigencharacter_iff _ _).mp hχ
  obtain ⟨x, hx⟩ := exists_smoothInduced_eval_ne_zero P σ hf0
  exact isGeneralizedEigencharacter_of_map_ne_zero
    (centralEvaluation P σ ι hι x) χ k
      ((mem_characterSpace _ _ _ _).mpr hf) hx

end Langlands.Induction
