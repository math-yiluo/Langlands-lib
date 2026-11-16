import Langlands.GroupScheme.Rational.LeviRetraction
import Langlands.GroupScheme.Rational.LeviMultiplication

/-! # Actual right-coset projections from subgroup multiplication -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.RelativeLevi

variable {S : Scheme.{u}} {L U P : GroupScheme S}
    (l : L ⟶ P) (r : U ⟶ P) [IsIso (subgroupMultiplication r l)]

/-- The actual right-coset map `P → U` obtained from the supplied
radical-times-Levi multiplication isomorphism. -/
def rightCosetProjection : P.X ⟶ U.X :=
  inv (subgroupMultiplication r l) ≫ fst U.X L.X

@[simp]
theorem comp_rightCosetProjection {T : Over S} (g : T ⟶ P.X) :
    g ≫ rightCosetProjection l r = leviComponent r l g := by
  simp only [rightCosetProjection, leviComponent]

/-- Equality under the coset map is exactly right-coset membership on the
original relative test scheme. -/
theorem rightCosetProjection_fibers (T : Over S) (g h : T ⟶ P.X) :
    g ≫ rightCosetProjection l r = h ≫ rightCosetProjection l r ↔
      g⁻¹ * h ∈ (SubgroupFunctor.range l).carrier T := by
  rw [comp_rightCosetProjection, comp_rightCosetProjection]
  constructor
  · intro he
    apply SubgroupFunctor.mem_range.mpr
    refine ⟨(radicalComponent r l g)⁻¹ * radicalComponent r l h, ?_⟩
    rw [MonObj.mul_comp, GrpObj.inv_comp]
    conv_rhs =>
      rw [← leviComponent_mul_radicalComponent r l g,
        ← leviComponent_mul_radicalComponent r l h, ← he]
    group
  · intro hz
    obtain ⟨z, hz⟩ := SubgroupFunctor.mem_range.mp hz
    have hh : h = g * (z ≫ l.hom.hom) := by
      rw [hz]
      group
    rw [hh, ← leviComponent_mul_radicalComponent r l g]
    have he :
        ((leviComponent r l g ≫ r.hom.hom) *
          (radicalComponent r l g ≫ l.hom.hom)) * (z ≫ l.hom.hom) =
        (leviComponent r l g ≫ r.hom.hom) *
          ((radicalComponent r l g * z) ≫ l.hom.hom) := by
      rw [MonObj.mul_comp, mul_assoc]
    rw [he]
    exact (leviComponent_product r l _ _).trans
      (leviComponent_product r l _ _).symm

end Langlands.GroupScheme.RelativeLevi
