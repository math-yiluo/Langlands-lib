import Langlands.AbelianScheme.PolarizedFiniteLevel.FrameLocusField
import Langlands.AbelianScheme.PolarizedFiniteLevel.FrameLocusBaseChangeStatement
import Langlands.AbelianScheme.PolarizedFiniteLevel.FrameLocusCoverStatement
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-! # Covering by projective frame loci from Lefschetz's theorem -/

noncomputable section

open CategoryTheory AlgebraicGeometry

universe u

namespace Langlands.AbelianScheme.PolarizedFiniteLevel

/-- If `n` exceeds `(m + 1) * (6^g*d*g!)`, then `n^(2g)` exceeds `m + 1` times the
hyperplane bound `6^g*d*g!*n^(2g-2)`, for positive `g`. -/
lemma frameSize_lt {g d n m : ℕ} (hg : 0 < g)
    (hn : (m + 1) * (6 ^ g * d * Nat.factorial g) < n) :
    (m + 1) * (6 ^ g * d * Nat.factorial g * n ^ (2 * g - 2)) < n ^ (2 * g) := by
  have hn0 : 0 < n := lt_of_le_of_lt (Nat.zero_le _) hn
  have h2 : n ^ (2 * g) = n ^ 2 * n ^ (2 * g - 2) := by
    rw [← pow_add]
    congr 1
    omega
  have hsq : n ≤ n ^ 2 := le_self_pow hn0 two_ne_zero
  calc (m + 1) * (6 ^ g * d * Nat.factorial g * n ^ (2 * g - 2))
      = (m + 1) * (6 ^ g * d * Nat.factorial g) * n ^ (2 * g - 2) := by ring
    _ < n ^ 2 * n ^ (2 * g - 2) :=
        Nat.mul_lt_mul_of_pos_right (lt_of_lt_of_le hn hsq) (pow_pos hn0 _)
    _ = n ^ (2 * g) := h2.symm

set_option linter.defProp false in
/-- Proved definition: Lefschetz's embedding theorem over fields and base change of
the frame locus imply the published `FrameLocusCoverStatement`, with the bound
`N = (6^g*d) * (6^g*d*g!) + 1`. -/
def frameLocusCover_of_cubicFieldEmbedding (hL : CubicFieldEmbeddingStatement.{u})
    (hB : FrameLocusBaseChangeStatement.{u}) : FrameLocusCoverStatement.{u} := by
  intro P g d hg hd
  refine ⟨(cubicProjectiveDimension g d + 1) * (6 ^ g * d * Nat.factorial g) + 1, ?_⟩
  intro n hN S _ hunit a x
  have hlt : (cubicProjectiveDimension g d + 1) * (6 ^ g * d * Nat.factorial g) < n := hN
  have hn : 0 < n := lt_of_le_of_lt (Nat.zero_le _) hlt
  let κ := S.residueField x
  let K := AlgebraicClosure κ
  let f : Spec (CommRingCat.of K) ⟶ S :=
    Spec.map (CommRingCat.ofHom (algebraMap κ K)) ≫ S.fromSpecResidueField x
  have hnK : (n : K) ≠ 0 := by
    have h1 : IsUnit (n : Γ(Spec (CommRingCat.of K), ⊤)) := by
      have := hunit.map f.appTop.hom
      simpa only [map_natCast] using this
    have h2 : IsUnit (n : K) := by
      have := h1.map (Scheme.ΓSpecIso (CommRingCat.of K)).hom.hom
      simpa only [map_natCast] using this
    exact h2.ne_zero
  obtain ⟨ρ, hρ⟩ := (a.pullback f).exists_frameLocus_eq_top hL hg hd hn hnK
    (frameSize_lt hg hlt)
  refine ⟨ρ, ?_⟩
  have hmem : IsLocalRing.closedPoint K ∈ (a.pullback f).frameLocus ρ := by
    rw [hρ]
    trivial
  rw [hB P S (Spec (CommRingCat.of K)) g d n hd a f ρ] at hmem
  have hx : f (IsLocalRing.closedPoint K) = x := by
    exact Scheme.fromSpecResidueField_apply x _
  rw [← hx]
  exact hmem

end Langlands.AbelianScheme.PolarizedFiniteLevel
