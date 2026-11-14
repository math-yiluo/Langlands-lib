import Langlands.GroupScheme.Rational.MinimalParabolicLineCharacter
import Langlands.Global.AdelicPositiveRootCharacterRelation

/-! # Uniform bounds for minimal-parabolic line characters on simple-root boxes -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj NNReal

namespace Langlands.Global.PositiveRealTorus

open Langlands.GroupScheme AdelicGroupPoints

variable (F : Type u) [Field F] [NumberField F]
  (G : GroupScheme (Spec (CommRingCat.of F)))
  (T : CommGroupScheme (Spec (CommRingCat.of F)))

/-- The normalized norm of a sum of torus characters is the product of the norms. -/
theorem normCharacter_add (χ ψ : characterLattice T) (s : AdelicGroupPoints F T.toGrp) :
    normCharacter F T (χ + ψ) s = normCharacter F T χ s * normCharacter F T ψ s :=
  characterNorm_add F T.toGrp χ ψ s

/-- The normalized norm of the trivial torus character is one. -/
theorem normCharacter_zero (s : AdelicGroupPoints F T.toGrp) :
    normCharacter F T 0 s = 1 :=
  characterNorm_zero F T.toGrp s

/-- Uniform bounds on a set of characters give uniform bounds on every
nonnegative integral combination of them. -/
theorem hasUniformCharacterBound_of_mem_closure
    {Δ : Set (characterLattice T)} (S : Set (AdelicGroupPoints F T.toGrp))
    (hΔ : ∀ α ∈ Δ, HasUniformCharacterBound F T α S)
    {χ : characterLattice T} (hχ : χ ∈ AddSubmonoid.closure Δ) :
    HasUniformCharacterBound F T χ S := by
  induction hχ using AddSubmonoid.closure_induction with
  | mem α hα => exact hΔ α hα
  | zero => exact ⟨1, fun s _ => (normCharacter_zero F T s).le⟩
  | add x y _ _ hx hy =>
    obtain ⟨C, hC⟩ := hx
    obtain ⟨D, hD⟩ := hy
    exact ⟨C * D, fun s hs => by
      rw [normCharacter_add]
      exact mul_le_mul' (hC s hs) (hD s hs)⟩

omit [NumberField F] in
private theorem le_max_of_pow_le {x C : ℝ≥0ˣ} {d : ℕ} (hd : 0 < d) (hx : x ^ d ≤ C) :
    x ≤ max C 1 := by
  by_cases h : x ≤ 1
  · exact h.trans (le_max_right _ _)
  · exact ((le_self_pow (le_of_not_ge h) hd.ne').trans hx).trans (le_max_left _ _)

/-- On ambient norm-one torus points, a character a positive multiple of which
is a restricted ambient character plus a uniformly bounded character is itself
uniformly bounded. -/
theorem hasUniformCharacterBound_of_pos_nsmul_sub_restrict
    (i : T.toGrp ⟶ G) {ψ : characterLattice T} {d : ℕ} (hd : 0 < d)
    (θ : rationalCharacters G) (S : Set (AdelicGroupPoints F T.toGrp))
    (hS : ∀ s ∈ S, map F T.toGrp G i s ∈ normOneSubgroup F G)
    (hbound : HasUniformCharacterBound F T (d • ψ - torusCharacterRestrict i θ) S) :
    HasUniformCharacterBound F T ψ S := by
  obtain ⟨C, hC⟩ := hbound
  refine ⟨max C 1, fun s hs => le_max_of_pow_le hd ?_⟩
  have hrel : d • ψ = torusCharacterRestrict i θ + 1 • (d • ψ - torusCharacterRestrict i θ) := by
    rw [one_nsmul, add_sub_cancel]
  rw [normCharacter_pow_eq_of_integral_relation F G T i θ hrel s (hS s hs), pow_one]
  exact hC s hs

/-- A coordinate line preserved by the minimal standard parabolic has a
uniformly bounded normalized torus line character on the ambient norm-one
torus points all of whose simple-root norms are at most `c`. -/
theorem hasUniformCharacterBound_torusCoordinateLineCharacter_of_minimalStandardParabolic
    [IsAffineHom G.X.hom] (hG : IsConnectedReductive G)
    (i : T.toGrp ⟶ G) (hi : IsMaximalSplitTorus i)
    (ν : cocharacterLattice T) (hν : IsGenericCocharacter i ν)
    {n : Type} [Fintype n] [DecidableEq n] (ρ : MatrixRepresentation G n) (j : n)
    (hline : (ρ.restrict (Standard.parabolicHom i ν ∅)).PreservesCoordinateLine j)
    (hTline : (ρ.restrict i).PreservesCoordinateLine j) (c : ℝ≥0ˣ) :
    HasUniformCharacterBound F T (ρ.torusCoordinateLineCharacter i j hTline)
      {s | map F T.toGrp G i s ∈ normOneSubgroup F G ∧
        ∀ α ∈ simpleRelativeRoots i ν, normCharacter F T α s ≤ c} := by
  obtain ⟨d, hd, θ, hmem⟩ :=
    ρ.exists_pos_nsmul_sub_restrict_mem_closure_simpleRelativeRoots i hG hi ν hν j hline hTline
  refine hasUniformCharacterBound_of_pos_nsmul_sub_restrict F G T i hd θ _
    (fun s hs => hs.1) ?_
  exact hasUniformCharacterBound_of_mem_closure F T _
    (fun α hα => ⟨c, fun s hs => hs.2 α hα⟩) hmem

/-- The same bound, with torus preservation of the line derived from the
minimal-parabolic hypothesis. -/
theorem exists_hasUniformCharacterBound_torusCoordinateLineCharacter_of_minimalStandardParabolic
    [IsAffineHom G.X.hom] (hG : IsConnectedReductive G)
    (i : T.toGrp ⟶ G) (hi : IsMaximalSplitTorus i)
    (ν : cocharacterLattice T) (hν : IsGenericCocharacter i ν)
    {n : Type} [Fintype n] [DecidableEq n] (ρ : MatrixRepresentation G n) (j : n)
    (hline : (ρ.restrict (Standard.parabolicHom i ν ∅)).PreservesCoordinateLine j) :
    ∃ hTline : (ρ.restrict i).PreservesCoordinateLine j, ∀ c : ℝ≥0ˣ,
      HasUniformCharacterBound F T (ρ.torusCoordinateLineCharacter i j hTline)
        {s | map F T.toGrp G i s ∈ normOneSubgroup F G ∧
          ∀ α ∈ simpleRelativeRoots i ν, normCharacter F T α s ≤ c} :=
  let hTline :=
    ρ.preservesCoordinateLine_torus_of_minimalStandardParabolic i hG hi ν hν j hline
  ⟨hTline, hasUniformCharacterBound_torusCoordinateLineCharacter_of_minimalStandardParabolic
    F G T hG i hi ν hν ρ j hline hTline⟩

end Langlands.Global.PositiveRealTorus
