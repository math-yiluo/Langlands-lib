import Langlands.GroupScheme.Rational.CoordinateSemigroupStatement
import Langlands.GroupScheme.Rational.CoordinateWeightDecompositionStatement

/-! # Algebra of actual augmentation-weight support -/

set_option backward.isDefEq.respectTransparency false

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.CoordinateWeights

variable {k : Type u} [Field k]
    {S : CommGroupScheme (Spec (CommRingCat.of k))}
    {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]

/-- Products of actual eigenfunctions have the sum of their character labels. -/
theorem mul_mem_weightSpace (b : AutomorphicAction S.toGrp G)
    {χ ψ : characterLattice S} {f g : CharacterUnits.Coord G}
    (hf : f ∈ weightSpace b χ) (hg : g ∈ weightSpace b ψ) :
    f * g ∈ weightSpace b (χ + ψ) := by
  intro A _ _ s x
  have hχ : Lie.characterValue (χ + ψ) s =
      Lie.characterValue χ s * Lie.characterValue ψ s := by
    rw [Lie.characterValue, comp_groupHom_add, map_mul]
    rfl
  rw [map_mul, hf A s x, hg A s x, hχ, Units.val_mul, map_mul]
  ring

/-- Raw augmentation support is additively closed when coordinates have no zero divisors. -/
theorem add_mem_support [NoZeroDivisors (CharacterUnits.Coord G)]
    (b : AutomorphicAction S.toGrp G) {χ ψ : characterLattice S}
    (hχ : χ ∈ support b) (hψ : ψ ∈ support b) : χ + ψ ∈ support b := by
  obtain ⟨f, hf, hfw⟩ := hχ
  obtain ⟨g, hg, hgw⟩ := hψ
  let fg : augmentation G := ⟨f.val * g.val, by
    change Lie.coordinateOrigin G (f.val * g.val) = 0
    rw [map_mul, show Lie.coordinateOrigin G f.val = 0 from f.property, zero_mul]⟩
  refine ⟨fg, ?_, mul_mem_weightSpace b hfw hgw⟩
  intro hfg
  have hz : f.val * g.val = 0 := congrArg Subtype.val hfg
  rcases mul_eq_zero.mp hz with hz | hz
  · exact hf (Subtype.ext hz)
  · exact hg (Subtype.ext hz)

/-- The actual raw support, bundled without adding an identity or any new weight. -/
def supportSemigroup [NoZeroDivisors (CharacterUnits.Coord G)]
    (b : AutomorphicAction S.toGrp G) : AddSubsemigroup (characterLattice S) where
  carrier := support b
  add_mem' := add_mem_support b

@[simp] theorem coe_supportSemigroup [NoZeroDivisors (CharacterUnits.Coord G)]
    (b : AutomorphicAction S.toGrp G) :
    (supportSemigroup b : Set (characterLattice S)) = support b := rfl

/-- Same-character lifts from the augmentation quotient include its support in raw support. -/
theorem cotangentSupport_subset_support (b : AutomorphicAction S.toGrp G)
    (hlift : ∀ χ : characterLattice S,
      (augmentationWeightSpace b χ).map (cotangentMk G) = cotangentWeightSpace b χ) :
    cotangentSupport b ⊆ support b := by
  rintro χ ⟨q, hq, hqw⟩
  rw [← hlift χ] at hqw
  obtain ⟨f, hf, rfl⟩ := hqw
  refine ⟨f, ?_, hf⟩
  intro hz
  exact hq (by rw [hz, map_zero])

/-- Positive cotangent sums occur in augmentation support once same-weight lifts are known. -/
theorem closure_cotangentSupport_subset_support [NoZeroDivisors (CharacterUnits.Coord G)]
    (b : AutomorphicAction S.toGrp G)
    (hlift : ∀ χ : characterLattice S,
      (augmentationWeightSpace b χ).map (cotangentMk G) = cotangentWeightSpace b χ) :
    (AddSubsemigroup.closure (cotangentSupport b) : Set (characterLattice S)) ⊆ support b :=
  AddSubsemigroup.closure_le (S := supportSemigroup b) |>.mpr
    (cotangentSupport_subset_support b hlift)

/-- The universal property of positive closure gives containment for empty semigroups too. -/
theorem support_subset_iff_of_eq_closure (b : AutomorphicAction S.toGrp G)
    (heq : support b = (AddSubsemigroup.closure
      (RelativeRoot.actionWeightSupport b ⊤) : Set (characterLattice S)))
    (M : AddSubsemigroup (characterLattice S)) :
    support b ⊆ M ↔ RelativeRoot.actionWeightSupport b ⊤ ⊆ M := by
  rw [heq]
  exact AddSubsemigroup.closure_le

/-- The exact containment target follows from the exact equality target. -/
theorem augmentationLieContainment_of_semigroup
    (h : AugmentationLieSemigroupStatement.{u}) : AugmentationLieContainmentStatement.{u} := by
  intro k _ G hsm hAff hconn S hsplit b
  let := hAff
  exact support_subset_iff_of_eq_closure b (h k G hsm hAff hconn S hsplit b)

/-- A proof of the equality target suffices for the published conjunction. -/
theorem coordinateSemigroupComparison_of_semigroup
    (h : AugmentationLieSemigroupStatement.{u}) : CoordinateSemigroupComparisonStatement.{u} :=
  ⟨h, augmentationLieContainment_of_semigroup h⟩

end Langlands.GroupScheme.CoordinateWeights
