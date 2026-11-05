import Langlands.Representation.Plancherel.RationalUniformizerCoordinateHeightStatement
import Langlands.Representation.Plancherel.RationalMatrixNormComparison

/-! # Regular functions control uniformizer coordinate height -/

noncomputable section

universe u uI

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj BigOperators NNReal

namespace Langlands.Plancherel

open GroupScheme MatrixRepresentation CocharacterUniformizer

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G : GroupScheme (Spec (CommRingCat.of F))}
  {n : Type} [Fintype n] [DecidableEq n] [Nonempty n]

@[simp] theorem rationalMatrixNorm_restrict (ρ : MatrixRepresentation G n)
    {H : GroupScheme (Spec (CommRingCat.of F))} (i : H ⟶ G)
    (g : rationalPoints H) :
    rationalMatrixNorm F (ρ.restrict i) g =
      rationalMatrixNorm F ρ (rationalPoints.map i g) := by
  let := (LocalField.residueNormalizedAbsoluteValue F).toNormedField
  change HarishChandraSchwartz.glNorm ((ρ.restrict i).rationalMatrix g) =
    HarishChandraSchwartz.glNorm (ρ.rationalMatrix (rationalPoints.map i g))
  rw [rationalMatrix_restrict]
  rfl

/-- Actual algebraic characters have power growth in any supplied closed
matrix embedding, with no topology change on rational point sets. -/
theorem rationalCharacter_rationalMatrixNorm_bound (ρ : MatrixRepresentation G n)
    (hρ : IsClosedSubgroup ρ) (χ : rationalCharacters G) :
    ∃ (d : ℕ) (c : ℝ), 0 < c ∧ ∀ g : rationalPoints G,
      LocalField.residueNormalizedAbsoluteValue F (rationalCharacterEval χ g : F) ≤
        c * rationalMatrixNorm F ρ g ^ d := by
  let := (LocalField.residueNormalizedAbsoluteValue F).toNormedField
  let a : Γ(G.X.left, ⊤) := (characterEval χ G.X (𝟙 G.X)).val
  obtain ⟨d, c, hc, hb⟩ := regularFunction_rationalMatrixNorm_bound ρ hρ a
  refine ⟨d, c, hc, fun g => ?_⟩
  have he := congrArg Units.val (characterEval_naturality χ g (𝟙 G.X))
  simp only [Category.comp_id, Units.coe_map] at he
  change ‖(rationalCharacterEval χ g : F)‖ ≤ _
  rw [rationalCharacterEval_val, he]
  exact hb g

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
/-- A positive integral pairing dominates the unweighted sum of natural
coordinates, also for an empty family. -/
theorem sum_le_latticePairing_of_pos
    {S : CommGroupScheme (Spec (CommRingCat.of F))}
    {I : Type uI} [Fintype I] (x : I → cocharacterLattice S)
    (α : characterLattice S) (hα : ∀ j, 0 < latticePairing S α (x j))
    (m : I → ℕ) :
    (∑ j, m j : ℕ) ≤ latticePairing S α (∑ j, m j • x j) := by
  rw [map_sum]
  push_cast
  apply Finset.sum_le_sum
  intro j _
  rw [map_nsmul, nsmul_eq_mul]
  have hp : (1 : ℤ) ≤ latticePairing S α (x j) := hα j
  nlinarith [Int.natCast_nonneg (m j)]

/-- A character positive on the supplied generators gives a polynomial
matrix-norm upper bound for their total natural coordinate height. -/
theorem rationalUniformizerCoordinateHeight :
    RationalUniformizerCoordinateHeightStatement.{u, uI} := by
  intro F _ _ _ _ G S i hi n _ _ _ ρ hρ I _ x α hα
  classical
  obtain ⟨d, c, hc, hb⟩ := rationalCharacter_rationalMatrixNorm_bound
    (ρ.restrict i) (hi.comp hρ)
    ((rationalCharacters.equivCharacterLattice S).symm (-α))
  refine ⟨d, c, hc, fun m => ?_⟩
  have hq : (1 : ℝ) < LocalField.residueCardinality F := by
    exact_mod_cast LocalField.residueCardinality_gt_one F
  calc
    (LocalField.residueCardinality F : ℝ) ^ (∑ j, m j) ≤
        (LocalField.residueCardinality F : ℝ) ^
          latticePairing S α (∑ j, m j • x j) := by
      rw [← zpow_natCast]
      exact zpow_le_zpow_right₀ hq.le (sum_le_latticePairing_of_pos x α hα m)
    _ = characterNorm F S (-α)
        (latticeSection F S (.ofAdd (∑ j, m j • x j))) := by
      rw [characterNorm_latticeSection, map_neg, LinearMap.neg_apply, neg_neg]
    _ ≤ c * rationalMatrixNorm F ρ
        (rationalPoints.map i
          (latticeSection F S (.ofAdd (∑ j, m j • x j)))) ^ d := by
      have h := hb (latticeSection F S (.ofAdd (∑ j, m j • x j)))
      simpa only [characterNorm, rationalNormCharacters_val,
        rationalMatrixNorm_restrict] using h

end Langlands.Plancherel
