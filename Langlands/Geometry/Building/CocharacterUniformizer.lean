import Langlands.Geometry.Building.SplitTorusValuation

/-!
# Uniformizer sections and Renard's contracting cones

The section evaluates each actual cocharacter at the same chosen field uniformizer.
Its image is Renard's `C_A`, rather than all rational points of the split torus.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj NNReal

namespace Langlands.GroupScheme.CocharacterUniformizer

variable (F : Type u) [Field F]
  (A : CommGroupScheme (Spec (CommRingCat.of F)))

/-- Intrinsic evaluation of an actual cocharacter at a field unit. -/
def cocharacterPoints (c : cocharacterLattice A) : Fˣ →* rationalPoints A.toGrp :=
  (rationalPoints.map (CommGroupScheme.groupHom c)).comp
    (Gm.affinePointsEquiv (𝟙 (Spec (CommRingCat.of F)))).symm.toMonoidHom

variable [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]

/-- The group homomorphism `c ↦ c(π)` for the already chosen order-one uniformizer. -/
def latticeSection : Multiplicative (cocharacterLattice A) →* rationalPoints A.toGrp where
  toFun c := cocharacterPoints F A c.toAdd (SplitTorusValuation.uniformizerUnit F)
  map_one' := by
    exact comp_groupHom_zero _
  map_mul' c d := by
    exact comp_groupHom_add _ c.toAdd d.toAdd

/-- Renard's lattice-lifting subgroup `C_A` inside the actual group `A(F)`. -/
def CA : Subgroup (rationalPoints A.toGrp) :=
  (latticeSection F A).range

/-- The normalized norm of an actual algebraic character of `A`. -/
def characterNorm (α : characterLattice A) (a : rationalPoints A.toGrp) : ℝ :=
  (((Plancherel.rationalNormCharacters A.toGrp
    ((rationalCharacters.equivCharacterLattice A).symm α)).toMul a : ℝ≥0) : ℝ)

/-- `C_A^+`, using the restrictions of the simple roots of the chosen parabolic. -/
def CAplus (R : Set (characterLattice A)) : Set (rationalPoints A.toGrp) :=
  {a | a ∈ CA F A ∧ ∀ α ∈ R, characterNorm F A α a ≤ 1}

/-- `C_A^{++}`: every relevant character has norm strictly below one. -/
def CAstrict (R : Set (characterLattice A)) : Set (rationalPoints A.toGrp) :=
  {a | a ∈ CA F A ∧ ∀ α ∈ R, characterNorm F A α a < 1}

/-- Renard V.3.22's strict epsilon condition; it has no additional norm-at-most-one
condition when `ε > 1`. -/
def CAepsilon (R : Set (characterLattice A)) (ε : ℝ) :
    Set (rationalPoints A.toGrp) :=
  {a | a ∈ CA F A ∧ ∀ α ∈ R, characterNorm F A α a < ε}

/-- The retained general split-torus lattice-section obligations: injectivity,
the actual rational-character valuation formula, and unique representatives modulo
the actual common norm kernel. -/
def IsUniformizerLatticeSection : Prop :=
  Function.Injective (latticeSection F A) ∧
    (∀ (c : cocharacterLattice A) (α : characterLattice A),
      (Plancherel.rationalCharacterValuation A.toGrp
        (latticeSection F A (Multiplicative.ofAdd c))).toAdd
          ((rationalCharacters.equivCharacterLattice A).symm α) =
        latticePairing A α c) ∧
    ∀ a : rationalPoints A.toGrp,
      ∃! c : Multiplicative (cocharacterLattice A),
        a * (latticeSection F A c)⁻¹ ∈ Plancherel.rationalCommonNormKernel A.toGrp

/-- The valuation and norm-kernel section statement for every actual split torus,
in both characteristics and without a chosen coordinate presentation. -/
def SplitTorusUniformizerSectionStatement : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (A : CommGroupScheme (Spec (CommRingCat.of F))),
    IsSplitTorus A.toGrp → IsUniformizerLatticeSection F A

end Langlands.GroupScheme.CocharacterUniformizer
