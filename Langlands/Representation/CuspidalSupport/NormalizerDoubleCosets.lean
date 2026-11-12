import Mathlib.GroupTheory.DoubleCoset
import Langlands.Representation.Exponents.LeviNormalizerQuotientProof

/-! # Double cosets represented by elements normalizing a rational Levi -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Aubert.General.RepresentedParabolic

open GroupScheme

variable {k : Type u} [Field k]
  {G P M : GroupScheme (Spec (CommRingCat.of k))}

/-- Parabolic double cosets containing a point whose conjugation preserves the Levi. -/
def normalizerDoubleCosets (p : P ⟶ G) (l : M ⟶ P) :
    Set (DoubleCoset.Quotient (pointImage p : Set (rationalPoints G))
      (pointImage p : Set (rationalPoints G))) :=
  {x | ∃ (w : rationalPoints G) (φ : M ≅ M),
    DoubleCoset.mk (pointImage p) (pointImage p) w = x ∧
      φ.hom ≫ l ≫ p = l ≫ p ≫ (G.innerIso w).hom}

/-- Finitely many normalizer representatives modulo the Levi give finitely many
parabolic double cosets. This step uses no topology or representation. -/
theorem normalizerDoubleCosets_finite_of_representatives
    (p : P ⟶ G) (l : M ⟶ P)
    (n : ℕ) (g : Fin n → rationalPoints G)
    (hrep : ∀ (w : rationalPoints G) (φ : M ≅ M),
      φ.hom ≫ l ≫ p = l ≫ p ≫ (G.innerIso w).hom →
        ∃ (j : Fin n) (m : rationalPoints M),
          w = g j * rationalPoints.map (l ≫ p) m) :
    (normalizerDoubleCosets p l).Finite := by
  apply (Set.finite_range (fun j => DoubleCoset.mk (pointImage p) (pointImage p) (g j))).subset
  rintro x ⟨w, φ, rfl, hφ⟩
  obtain ⟨j, m, rfl⟩ := hrep w φ hφ
  refine ⟨j, ?_⟩
  have hm : rationalPoints.map (l ≫ p) m ∈ pointImage p := by
    refine ⟨rationalPoints.map l m, ?_⟩
    rfl
  exact (DoubleCoset.mk_mul_mem ⟨_, hm⟩ (g j)).symm

/-- The actual rational normalizer double cosets of a Levi in a connected reductive
group over a nonarchimedean local field form a finite set. -/
theorem normalizerDoubleCosets_finite [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (hG : IsConnectedReductive G)
    (p : P ⟶ G) (l : M ⟶ P) (hp : IsParabolicSubgroup p)
    (hl : IsRationalLeviSubgroup l) :
    (normalizerDoubleCosets p l).Finite := by
  obtain ⟨n, g, _, hrep⟩ := leviNormalizerFiniteQuotient k G hG P M p l hp hl
  exact normalizerDoubleCosets_finite_of_representatives p l n g hrep

/-- Any selection of normalizing representatives, such as the stabilizer of an
unramified inertial class, still gives finitely many parabolic double cosets. -/
theorem normalizerDoubleCosets_subset_finite [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (hG : IsConnectedReductive G)
    (p : P ⟶ G) (l : M ⟶ P) (hp : IsParabolicSubgroup p)
    (hl : IsRationalLeviSubgroup l)
    (W : Set (DoubleCoset.Quotient (pointImage p : Set (rationalPoints G))
      (pointImage p : Set (rationalPoints G))))
    (hW : W ⊆ normalizerDoubleCosets p l) : W.Finite :=
  (normalizerDoubleCosets_finite hG p l hp hl).subset hW

end Langlands.Aubert.General.RepresentedParabolic
