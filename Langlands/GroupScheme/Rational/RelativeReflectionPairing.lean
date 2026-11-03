import Langlands.GroupScheme.Rational.RelativeRootsCharacterSpan
import Langlands.GroupScheme.Rational.RelativeReflection
import Langlands.GroupScheme.Rational.RootReflectionAssembly
import Langlands.Representation.Aubert.General.RationalWeylRootAction

/-! # Whole-character pairing invariance of actual relative reflections -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry TensorProduct
open Langlands.LinearAlgebra.RationalSpan

namespace Langlands.GroupScheme

open Langlands.Aubert.General.RationalPointFamily RelativeRootSystem

variable {k : Type u} [Field k]
  {T : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))}

/-- Evaluation at a cocharacter on the full rational character space. -/
def rationalCocharacterEvaluation (ζ : cocharacterLattice T) :
    (ℚ ⊗[ℤ] characterLattice T) →ₗ[ℚ] ℚ :=
  (TensorProduct.AlgebraTensorModule.rid ℤ ℚ ℚ).toLinearMap.comp
    (((latticePairing T).flip ζ).baseChange ℚ)

@[simp] theorem rationalCocharacterEvaluation_toRat
    (ζ : cocharacterLattice T) (χ : characterLattice T) :
    rationalCocharacterEvaluation ζ (toRat χ) = (latticePairing T χ ζ : ℚ) := by
  simp [rationalCocharacterEvaluation, toRat, zsmul_eq_mul]

variable {i : T.toGrp ⟶ G} [Mono i.hom.hom.left] [IsAffineHom G.X.hom]

/-- A reflection on the root span preserves evaluation at a cocharacter
orthogonal to its root, provided roots and restricted characters span. -/
theorem IsRelativeReflection.rationalCocharacterEvaluation_invariant_of_span
    {α : characterLattice T} {w : relativeWeylGroup i}
    (h : IsRelativeReflection i α w)
    (hspan : relativeRootSpan i ⊔ (rationalCharacterRestrictRat i).range = ⊤)
    {ζ : cocharacterLattice T} (hαζ : latticePairing T α ζ = 0)
    (x : ℚ ⊗[ℤ] characterLattice T) :
    rationalCocharacterEvaluation ζ (relativeWeylFullRatAction i w x) =
      rationalCocharacterEvaluation ζ x := by
  obtain ⟨hα, f, hf, hw⟩ := h
  have hroot (y : relativeRootSpan i) :
      rationalCocharacterEvaluation ζ (relativeWeylFullRatAction i w y) =
        rationalCocharacterEvaluation ζ y := by
    rw [← coe_relativeWeylAction_apply, hw, Module.reflection_apply]
    simp only [Submodule.coe_sub, Submodule.coe_smul, map_sub, map_smul]
    have hz : rationalCocharacterEvaluation ζ (toRat α) = 0 := by
      rw [rationalCocharacterEvaluation_toRat, hαζ, Int.cast_zero]
    rw [hz, smul_zero, sub_zero]
  have hx : x ∈ relativeRootSpan i ⊔ (rationalCharacterRestrictRat i).range := by
    rw [hspan]
    exact Submodule.mem_top
  obtain ⟨y, hy, z, ⟨c, rfl⟩, hsum⟩ := Submodule.mem_sup.mp hx
  rw [← hsum, map_add, map_add, map_add, relativeWeylFullRatAction_restrictionRange]
  exact congrArg (· + rationalCocharacterEvaluation ζ (rationalCharacterRestrictRat i c))
    (hroot ⟨y, hy⟩)

/-- For an actual maximal split torus in a connected reductive group, every
root-span reflection preserves every character pairing orthogonal to its root. -/
theorem IsRelativeReflection.latticePairing_schemeWeylCharacterAction
    {α : characterLattice T} {w : relativeWeylGroup i}
    (h : IsRelativeReflection i α w)
    (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
    {ζ : cocharacterLattice T} (hαζ : latticePairing T α ζ = 0)
    (χ : characterLattice T) :
    latticePairing T (schemeWeylCharacterAction i w χ) ζ =
      latticePairing T χ ζ := by
  have he := h.rationalCocharacterEvaluation_invariant_of_span
    (hG.relativeRootSpan_sup_restrictionRange_eq_top i hi) hαζ (toRat χ)
  change rationalCocharacterEvaluation ζ
    (toRat (schemeWeylCharacterAction i w χ)) =
      rationalCocharacterEvaluation ζ (toRat χ) at he
  simp only [rationalCocharacterEvaluation_toRat] at he
  exact_mod_cast he

end Langlands.GroupScheme
