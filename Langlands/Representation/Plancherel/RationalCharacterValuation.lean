import Langlands.GroupScheme.Rational.Characters
import Langlands.Representation.Plancherel.LocalFieldUnits
import Langlands.Representation.Plancherel.UnramifiedValuation
import Langlands.Representation.Plancherel.UnramifiedLogarithm

/-!
# Actual rational-character norms and valuations

The character evaluations, field norm and integer order in this module are the
published group-scheme and local-field objects. Their composition requires no
chosen rational-point topology or reductive structure.
-/

noncomputable section

open CategoryTheory AlgebraicGeometry
open scoped NNReal CategoryTheory.MonObj

namespace Langlands.Plancherel

universe u

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]

variable (G : GroupScheme (Spec (CommRingCat.of F)))

/-- The actual normalized norms of all rational algebraic characters. -/
def rationalNormCharacters :
    GroupScheme.rationalCharacters G →+
      Additive (GroupScheme.rationalPoints G →* ℝ≥0ˣ) :=
  evaluationNormCharacters (GroupScheme.rationalCharacterEvalHom (G := G)) (fieldNormUnits F)

@[simp]
theorem rationalNormCharacters_apply (χ : GroupScheme.rationalCharacters G)
    (g : GroupScheme.rationalPoints G) :
    (rationalNormCharacters G χ).toMul g =
      fieldNormUnits F (GroupScheme.rationalCharacterEval χ g) := rfl

/-- The positive character is the source's actual normalized absolute value. -/
theorem rationalNormCharacters_val (χ : GroupScheme.rationalCharacters G)
    (g : GroupScheme.rationalPoints G) :
    (((rationalNormCharacters G χ).toMul g : ℝ≥0) : ℝ) =
      LocalField.residueNormalizedAbsoluteValue F
        (GroupScheme.rationalCharacterEval χ g : F) := rfl

/-- The source-positive integer valuation of actual rational-character values. -/
def rationalCharacterValuation :
    GroupScheme.rationalPoints G →*
      Multiplicative (GroupScheme.rationalCharacters G →+ ℤ) :=
  characterValuation (GroupScheme.rationalCharacterEvalHom (G := G)) (fieldOrderUnits F)

@[simp]
theorem rationalCharacterValuation_apply (g : GroupScheme.rationalPoints G)
    (χ : GroupScheme.rationalCharacters G) :
    (rationalCharacterValuation G g).toAdd χ =
      (fieldOrderUnits F (GroupScheme.rationalCharacterEval χ g)).toAdd := rfl

/-- The integer coordinate equals the existing order, with its finite-value cast. -/
theorem rationalCharacterValuation_ord (g : GroupScheme.rationalPoints G)
    (χ : GroupScheme.rationalCharacters G) :
    FML.ord F (GroupScheme.rationalCharacterEval χ g : F) =
      ((rationalCharacterValuation G g).toAdd χ : WithTop ℤ) :=
  fieldOrderUnits_ord F _

/-- The intersection of the actual normalized rational-character kernels. -/
def rationalCommonNormKernel : Subgroup (GroupScheme.rationalPoints G) :=
  commonNormKernel (fun χ => (rationalNormCharacters G χ).toMul)

instance rationalCommonNormKernel_normal : (rationalCommonNormKernel G).Normal :=
  commonNormKernel_normal _

theorem mem_rationalCommonNormKernel (g : GroupScheme.rationalPoints G) :
    g ∈ rationalCommonNormKernel G ↔
      ∀ χ : GroupScheme.rationalCharacters G,
        fieldNormUnits F (GroupScheme.rationalCharacterEval χ g) = 1 :=
  mem_commonNormKernel _ _

/-- The equality uses the proved field-unit kernel law, with no compatibility premise. -/
theorem rationalCharacterValuation_ker :
    (rationalCharacterValuation G).ker = rationalCommonNormKernel G :=
  characterValuation_ker _ _ _ (fun a => (fieldNormUnits_eq_one_iff F a).symm)

theorem mem_rationalCommonNormKernel_iff_valuation (g : GroupScheme.rationalPoints G) :
    g ∈ rationalCommonNormKernel G ↔
      ∀ χ : GroupScheme.rationalCharacters G,
        (rationalCharacterValuation G g).toAdd χ = 0 := by
  rw [← rationalCharacterValuation_ker G]
  exact mem_characterValuation_ker _ _ _

/-- The normalized real logarithm on the actual rational-character group. -/
def rationalNormLogarithm :
    GroupScheme.rationalPoints G →*
      Multiplicative (GroupScheme.rationalCharacters G →+ ℝ) :=
  normLogarithm (LocalField.residueCardinality F) (rationalNormCharacters G)

private theorem residueCardinality_real_gt_one :
    (1 : ℝ) < (LocalField.residueCardinality F : ℝ) := by
  exact_mod_cast LocalField.residueCardinality_gt_one F

/-- Waldspurger's exponential relation at the actual residue cardinality. -/
theorem rationalNormLogarithm_spec (g : GroupScheme.rationalPoints G)
    (χ : GroupScheme.rationalCharacters G) :
    (LocalField.residueCardinality F : ℝ) ^
        (-(rationalNormLogarithm G g).toAdd χ) =
      LocalField.residueNormalizedAbsoluteValue F
        (GroupScheme.rationalCharacterEval χ g : F) :=
  normLogarithm_spec (residueCardinality_real_gt_one (F := F)) _ _ _

/-- The normalization premise of the generic comparison is discharged by the
actual field norm. Every logarithm coordinate is the corresponding integer order. -/
theorem rationalNormLogarithm_eq_intValuation (g : GroupScheme.rationalPoints G)
    (χ : GroupScheme.rationalCharacters G) :
    (rationalNormLogarithm G g).toAdd χ =
      ((rationalCharacterValuation G g).toAdd χ : ℝ) :=
  normLogarithm_eq_intValuation (residueCardinality_real_gt_one (F := F))
    (rationalNormCharacters G) (rationalCharacterValuation G)
    (fun g χ => fieldNormUnits_rpow F (GroupScheme.rationalCharacterEval χ g)) g χ

theorem rationalNormLogarithm_ker :
    (rationalNormLogarithm G).ker = rationalCommonNormKernel G :=
  normLogarithm_ker (residueCardinality_real_gt_one (F := F)) _

/-- The actual image in the integer dual; no rank or index assertion is implicit. -/
def rationalCharacterValuationImage :
    Subgroup (Multiplicative (GroupScheme.rationalCharacters G →+ ℤ)) :=
  characterValuationImage (GroupScheme.rationalCharacterEvalHom (G := G)) (fieldOrderUnits F)

/-- The canonical algebraic quotient by the source's actual norm kernel. -/
def rationalNormKernelQuotientEquiv :
    (GroupScheme.rationalPoints G ⧸ rationalCommonNormKernel G) ≃*
      rationalCharacterValuationImage G :=
  normKernelValuationQuotientEquiv _ _ _
    (fun a => (fieldNormUnits_eq_one_iff F a).symm)

@[simp]
theorem rationalNormKernelQuotientEquiv_mk (g : GroupScheme.rationalPoints G) :
    rationalNormKernelQuotientEquiv G (QuotientGroup.mk g) =
      ⟨rationalCharacterValuation G g, g, rfl⟩ :=
  normKernelValuationQuotientEquiv_mk _ _ _ _ g

/-- Only the abstract group commutator is asserted here. -/
theorem commutator_le_rationalCommonNormKernel :
    _root_.commutator (GroupScheme.rationalPoints G) ≤ rationalCommonNormKernel G := by
  rw [← rationalCharacterValuation_ker G]
  exact commutator_le_characterValuation_ker _ _

variable {G}
variable {H : GroupScheme (Spec (CommRingCat.of F))}

/-- Restriction of the actual norm characters follows evaluation under the point map. -/
theorem rationalNormCharacters_characterRestrict (f : H ⟶ G)
    (χ : GroupScheme.rationalCharacters G) (y : GroupScheme.rationalPoints H) :
    (rationalNormCharacters H (GroupScheme.characterRestrict f χ)).toMul y =
      (rationalNormCharacters G χ).toMul (GroupScheme.rationalPoints.map f y) := by
  simp only [rationalNormCharacters_apply, GroupScheme.rationalCharacterEval_characterRestrict]

/-- The actual integer coordinates are compatible with character restriction. -/
theorem rationalCharacterValuation_characterRestrict (f : H ⟶ G)
    (χ : GroupScheme.rationalCharacters G) (y : GroupScheme.rationalPoints H) :
    (rationalCharacterValuation H y).toAdd (GroupScheme.characterRestrict f χ) =
      (rationalCharacterValuation G (GroupScheme.rationalPoints.map f y)).toAdd χ := by
  simp only [rationalCharacterValuation_apply, GroupScheme.rationalCharacterEval_characterRestrict]

/-- The real logarithm coordinates have the same restriction compatibility. -/
theorem rationalNormLogarithm_characterRestrict (f : H ⟶ G)
    (χ : GroupScheme.rationalCharacters G) (y : GroupScheme.rationalPoints H) :
    (rationalNormLogarithm H y).toAdd (GroupScheme.characterRestrict f χ) =
      (rationalNormLogarithm G (GroupScheme.rationalPoints.map f y)).toAdd χ := by
  rw [rationalNormLogarithm_eq_intValuation, rationalNormLogarithm_eq_intValuation,
    rationalCharacterValuation_characterRestrict]

end Langlands.Plancherel
