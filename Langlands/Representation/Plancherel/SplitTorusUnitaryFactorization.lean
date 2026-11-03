import Langlands.Representation.Plancherel.SplitTorusNormFormula

/-! # Unitary-times-positive factorization on actual split tori -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry TensorProduct
open scoped TensorProduct CategoryTheory.MonObj NNReal
open Langlands.GroupScheme
open Langlands.AlgebraicGeometry.PointTopology

namespace Langlands.Plancherel.SplitTorus

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {A : CommGroupScheme (Spec (CommRingCat.of F))}

/-- Remove the positive character of the normalized real parameter. -/
def unitaryFactor (hA : IsSplitTorus A.toGrp)
    (χ : rationalPoints A.toGrp →* ℂˣ) : rationalPoints A.toGrp →* ℂˣ :=
  χ * (positiveCharacter hA (normalizedRealPart hA χ))⁻¹

theorem unitaryFactor_mul_positiveCharacter (hA : IsSplitTorus A.toGrp)
    (χ : rationalPoints A.toGrp →* ℂˣ) :
    unitaryFactor hA χ * positiveCharacter hA (normalizedRealPart hA χ) = χ := by
  apply MonoidHom.ext
  intro a
  change (χ a * (positiveCharacter hA (normalizedRealPart hA χ) a)⁻¹) *
    positiveCharacter hA (normalizedRealPart hA χ) a = χ a
  exact inv_mul_cancel_right _ _

theorem normalizedRealPart_unitaryFactor (hA : IsSplitTorus A.toGrp)
    (χ : rationalPoints A.toGrp →* ℂˣ) :
    normalizedRealPart hA (unitaryFactor hA χ) = 0 := by
  rw [unitaryFactor, normalizedRealPart_mul, normalizedRealPart_inv,
    normalizedRealPart_positiveCharacter, add_neg_cancel]

section CanonicalTopology

variable [IsAffine A.X.left]

local instance factorizationPointTopology : TopologicalSpace (rationalPoints A.toGrp) :=
  rationalPointTopology F A.X

/-- Removing the smooth positive character preserves smoothness. -/
theorem isOpen_ker_unitaryFactor (hA : IsSplitTorus A.toGrp)
    (χ : rationalPoints A.toGrp →* ℂˣ)
    (hχ : IsOpen (χ.ker : Set (rationalPoints A.toGrp))) :
    IsOpen ((unitaryFactor hA χ).ker : Set (rationalPoints A.toGrp)) := by
  let : Smooth A.X.hom := hA.smooth
  let : IsTopologicalGroup (rationalPoints A.toGrp) :=
    rationalPoint_isTopologicalGroup F A.toGrp
  apply Subgroup.isOpen_mono (H₁ := χ.ker ⊓
    (positiveCharacter hA (normalizedRealPart hA χ)).ker)
  · intro a ha
    change χ a * (positiveCharacter hA (normalizedRealPart hA χ) a)⁻¹ = 1
    rw [show χ a = 1 from ha.1,
      show positiveCharacter hA (normalizedRealPart hA χ) a = 1 from ha.2]
    simp
  · exact hχ.inter (isOpen_ker_positiveCharacter hA _)

/-- The smooth factor left after removing the positive character is unitary. -/
theorem norm_unitaryFactor (hA : IsSplitTorus A.toGrp)
    (χ : rationalPoints A.toGrp →* ℂˣ)
    (hχ : IsOpen (χ.ker : Set (rationalPoints A.toGrp)))
    (a : rationalPoints A.toGrp) :
    ‖(unitaryFactor hA χ a : ℂ)‖ = 1 :=
  (normalizedRealPart_eq_zero_iff hA (unitaryFactor hA χ)
    (isOpen_ker_unitaryFactor hA χ hχ)).mp
      (normalizedRealPart_unitaryFactor hA χ) a

/-- The actual smooth unitary factor together with the factorization identity. -/
def smoothUnitaryFactorization (hA : IsSplitTorus A.toGrp)
    (χ : rationalPoints A.toGrp →* ℂˣ)
    (hχ : IsOpen (χ.ker : Set (rationalPoints A.toGrp))) :
    {chiUnitary : (rationalPoints A.toGrp →* ℂˣ) //
      IsOpen (chiUnitary.ker : Set (rationalPoints A.toGrp)) ∧
      (∀ a, ‖(chiUnitary a : ℂ)‖ = 1) ∧
      chiUnitary * positiveCharacter hA (normalizedRealPart hA χ) = χ} :=
  ⟨unitaryFactor hA χ, isOpen_ker_unitaryFactor hA χ hχ,
    norm_unitaryFactor hA χ hχ, unitaryFactor_mul_positiveCharacter hA χ⟩

@[simp] theorem smoothUnitaryFactorization_val (hA : IsSplitTorus A.toGrp)
    (χ : rationalPoints A.toGrp →* ℂˣ)
    (hχ : IsOpen (χ.ker : Set (rationalPoints A.toGrp))) :
    (smoothUnitaryFactorization hA χ hχ).val = unitaryFactor hA χ := rfl

end CanonicalTopology

end Langlands.Plancherel.SplitTorus
