import Langlands.GroupScheme.Reductive.DominantMultipleRootData
import Langlands.GroupScheme.Reductive.DominantMultipleCoefficients
import Langlands.GroupScheme.Reductive.CovariantProducts
import Langlands.GroupScheme.HomogeneousCharacterProducts

/-! # Realized torus characters form a submonoid -/

set_option backward.isDefEq.respectTransparency false

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.DominantMultiple

open AffineCoordinates

variable {k : Type u} [Field k]
  {G H U : GroupScheme (Spec (CommRingCat.of k))}
  [IsAffineHom G.X.hom] [IsAffineHom H.X.hom]
  {T : CommGroupScheme (Spec (CommRingCat.of k))}

local instance : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
local instance : IsAffine H.X.left := isAffine_of_isAffineHom H.X.hom

/-- `f` is a normalized coordinate, left covariant for the character `χ` of `H` and right
invariant along `j`. -/
def IsRealizedCoordinate (i : H ⟶ G) (j : U ⟶ G) (χ : rationalCharacters H)
    (f : algebra G) : Prop :=
  f ∈ leftCovariantSubspace i (characterCoordinate H χ) ∧ f ∈ rightInvariantSubspace j ∧
    AffineLinearEmbedding.counit (corepresentation G) f = 1

theorem isRealizedCoordinate_zero (i : H ⟶ G) (j : U ⟶ G) :
    IsRealizedCoordinate i j 0 1 := by
  refine ⟨?_, ?_, ?_⟩
  · rw [mem_leftCovariantSubspace_iff_points]
    intro T h g
    rw [characterCoordinate_zero, map_one, map_one, map_one, one_mul]
  · intro T u g
    rw [map_one, map_one]
  · exact counit_eq_one_of_forall fun T => map_one _

theorem IsRealizedCoordinate.add {i : H ⟶ G} {j : U ⟶ G} {χ ψ : rationalCharacters H}
    {f g : algebra G} (hf : IsRealizedCoordinate i j χ f) (hg : IsRealizedCoordinate i j ψ g) :
    IsRealizedCoordinate i j (χ + ψ) (f * g) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [characterCoordinate_add]
    exact mul_mem_leftCovariantSubspace i _ _ hf.1 hg.1
  · intro T u x
    rw [map_mul, map_mul, hf.2.1 T u x, hg.2.1 T u x]
  · exact counit_eq_one_of_forall fun T => by
      rw [map_mul, pointAlgebraHom_one_apply, pointAlgebraHom_one_apply, hf.2.2, hg.2.2,
        map_one, one_mul]

/-- The torus characters realized by normalized covariant coordinates. -/
def realizedSet (tH : T.toGrp ⟶ H) (i : H ⟶ G) (j : U ⟶ G) :
    AddSubmonoid (characterLattice T) where
  carrier := {x | ∃ (χ : rationalCharacters H) (f : algebra G),
    rationalCharacters.equivCharacterLattice T (characterRestrict tH χ) = x ∧
      IsRealizedCoordinate i j χ f}
  zero_mem' := ⟨0, 1, by simp, isRealizedCoordinate_zero i j⟩
  add_mem' := by
    rintro _ _ ⟨χ, f, rfl, hf⟩ ⟨ψ, g, rfl, hg⟩
    exact ⟨χ + ψ, f * g, by simp, hf.add hg⟩

/-- A character of the ambient group gives a realized coordinate for its restriction when it is
trivial along `j`. -/
theorem isRealizedCoordinate_characterCoordinate (i : H ⟶ G) (j : U ⟶ G)
    (ψ : rationalCharacters G)
    (hU : ∀ (T : Over (Spec (CommRingCat.of k))) (u : T ⟶ U.X),
      characterEval ψ T (u ≫ j.hom.hom) = 1) :
    IsRealizedCoordinate i j (characterRestrict i ψ) (characterCoordinate G ψ) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [mem_leftCovariantSubspace_iff_points]
    intro T h g
    rw [pointAlgebraHom_characterCoordinate, pointAlgebraHom_characterCoordinate,
      pointAlgebraHom_characterCoordinate, characterEval_characterRestrict, map_mul,
      Units.val_mul]
  · intro T u g
    rw [pointAlgebraHom_characterCoordinate, pointAlgebraHom_characterCoordinate, map_mul,
      hU, mul_one]
  · exact counit_eq_one_of_forall fun T => by
      rw [pointAlgebraHom_characterCoordinate, map_one, Units.val_one]

end Langlands.GroupScheme.DominantMultiple
