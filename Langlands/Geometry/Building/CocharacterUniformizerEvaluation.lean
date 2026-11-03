import Langlands.Geometry.Building.CocharacterUniformizer

/-! # Intrinsic uniformizer evaluation for the Jacquet adapter -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj NNReal

namespace Langlands.GroupScheme.CocharacterUniformizer

variable (F : Type u) [Field F]
  (A : CommGroupScheme (Spec (CommRingCat.of F)))

/-- An actual character evaluated on an actual cocharacter is the integer-pairing
power, without any choice of split coordinates. -/
theorem rationalCharacterEval_cocharacterPoints (α : characterLattice A)
    (c : cocharacterLattice A) (b : Fˣ) :
    rationalCharacterEval ((rationalCharacters.equivCharacterLattice A).symm α)
      (cocharacterPoints F A c b) = b ^ latticePairing A α c := by
  rw [rationalCharacterEval_apply]
  change Gm.affinePointsEquiv (𝟙 (Spec (CommRingCat.of F)))
    (((Gm.affinePointsEquiv (𝟙 (Spec (CommRingCat.of F)))).symm b ≫
      (CommGroupScheme.groupHom c).hom.hom) ≫
      (CommGroupScheme.groupHom α).hom.hom) = _
  rw [Category.assoc]
  change Gm.affinePointsEquiv (𝟙 (Spec (CommRingCat.of F)))
    ((Gm.affinePointsEquiv (𝟙 (Spec (CommRingCat.of F)))).symm b ≫
      (CommGroupScheme.groupHom (c ≫ α)).hom.hom) = _
  conv_lhs => rw [← (gmEndEquiv F).symm_apply_apply (c ≫ α)]
  rw [gmEndEquiv_symm_comp, map_zpow, MulEquiv.apply_symm_apply, latticePairing_apply]

variable [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]

/-- Pairing with any actual character gives its positive normalized order on
the common-uniformizer section. -/
theorem rationalCharacterValuation_latticeSection
    (α : characterLattice A) (c : cocharacterLattice A) :
    (Plancherel.rationalCharacterValuation A.toGrp
      (latticeSection F A (Multiplicative.ofAdd c))).toAdd
        ((rationalCharacters.equivCharacterLattice A).symm α) =
      latticePairing A α c := by
  rw [Plancherel.rationalCharacterValuation_apply]
  change (Plancherel.fieldOrderUnits F
    (rationalCharacterEval ((rationalCharacters.equivCharacterLattice A).symm α)
      (cocharacterPoints F A c (SplitTorusValuation.uniformizerUnit F)))).toAdd = _
  rw [rationalCharacterEval_cocharacterPoints, map_zpow, toAdd_zpow,
    SplitTorusValuation.fieldOrderUnits_uniformizerUnit, smul_eq_mul, mul_one]

/-- The residue-normalized norm uses the negative of the positive pairing. -/
theorem characterNorm_latticeSection
    (α : characterLattice A) (c : cocharacterLattice A) :
    characterNorm F A α (latticeSection F A (Multiplicative.ofAdd c)) =
      (LocalField.residueCardinality F : ℝ) ^ (-latticePairing A α c) := by
  unfold characterNorm
  rw [Plancherel.rationalNormCharacters_apply, Plancherel.fieldNormUnits_zpow]
  rw [← Plancherel.rationalCharacterValuation_apply,
    rationalCharacterValuation_latticeSection]

/-- Positive integral pairings yield the strict chamber inequalities. -/
theorem characterNorm_latticeSection_lt_one
    (α : characterLattice A) (c : cocharacterLattice A)
    (hpos : 0 < latticePairing A α c) :
    characterNorm F A α (latticeSection F A (Multiplicative.ofAdd c)) < 1 := by
  rw [characterNorm_latticeSection]
  have hq : (1 : ℝ) < LocalField.residueCardinality F := by
    exact_mod_cast LocalField.residueCardinality_gt_one F
  exact (zpow_lt_one_iff_right₀ hq).mpr (neg_neg_of_pos hpos)

end Langlands.GroupScheme.CocharacterUniformizer
