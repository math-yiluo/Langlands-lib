import Langlands.GroupScheme.HomScheme.TorusSubgroupModuli

/-! # Composition of actual subgroup-family evaluation -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.GroupScheme.TorusSubgroupModuli

variable {S : Scheme.{u}} {G : GroupScheme S} {M T U : Over S}
variable {K : GroupScheme M.left}

/-- The actual source comparison for successive subgroup-family evaluation. -/
def familySourceComparison (K : GroupScheme M.left) (a : T ⟶ M) (b : U ⟶ T) :
    (baseChange b.left).obj ((baseChange a.left).obj K) ≅
      (baseChange (b ≫ a).left).obj K :=
  Descent.pullbackComparison a.left b.left (b ≫ a).left rfl K

/-- The evaluated subgroup inclusion preserves its projection to the original
ambient group scheme. -/
@[reassoc]
theorem familyHom_original
    (j : K ⟶ (baseChange M.hom).obj G) (a : T ⟶ M) :
    (familyHom j a).hom.hom.left ≫ pullback.fst G.X.hom T.hom =
      pullback.fst K.X.hom a.left ≫ j.hom.hom.left ≫
        pullback.fst G.X.hom M.hom := by
  simp only [familyHom, Grp.comp_hom_hom, Over.comp_left, Category.assoc,
    Descent.pullbackComparison_hom_fst]
  exact pullback.lift_fst_assoc _ _ _ _

/-- Successive evaluation of actual inclusions agrees with direct evaluation,
with the actual source pullback comparison made explicit. -/
theorem familyHom_evaluate_comp
    (j : K ⟶ (baseChange M.hom).obj G) (a : T ⟶ M) (b : U ⟶ T) :
    familyHom (familyHom j a) b =
      (familySourceComparison K a b).hom ≫
        familyHom j (b ≫ a) := by
  apply Grp.hom_ext
  apply Over.OverMorphism.ext
  apply pullback.hom_ext
  · simp only [familySourceComparison, Grp.comp_hom_hom, Over.comp_left, Category.assoc,
      familyHom_original,
      Descent.pullbackComparison_hom_fst_assoc]
  · exact (Over.w (familyHom (familyHom j a) b).hom.hom).trans
      (Over.w ((familySourceComparison K a b).hom ≫
        familyHom j (b ≫ a)).hom.hom).symm

/-- Successive subgroup-family evaluation equals evaluation along the composite
as a literal subgroup functor on every test scheme. -/
theorem evaluate_comp
    (j : K ⟶ (baseChange M.hom).obj G) (a : T ⟶ M) (b : U ⟶ T) :
    evaluate (familyHom j a) b = evaluate j (b ≫ a) := by
  rw [evaluate, familyHom_evaluate_comp]
  exact SubgroupFunctor.range_iso_comp (familySourceComparison K a b) _

end Langlands.GroupScheme.TorusSubgroupModuli
