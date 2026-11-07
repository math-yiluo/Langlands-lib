import Langlands.GroupScheme.Rational.ClassFunctions
import Langlands.GroupScheme.Dynamic.ActionUniqueness
import Langlands.GroupScheme.Dynamic.ActionConjugation
import Langlands.GroupScheme.Dynamic.LimitMap

/-! # The canonical class quotient is constant along cocharacter limits -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.ClassFunctions

variable {K : Type u} [Field K]
    (G : GroupScheme (Spec (CommRingCat.of K))) [IsAffineHom G.X.hom]
    (χ : (Gm (Spec (CommRingCat.of K))).toGrp ⟶ G)

/-- The actual canonical class quotient is invariant under cocharacter conjugation. -/
theorem rho_cocharacter_invariant :
    (AutomorphicAction.cocharacterAction χ).IsInvariantMorphism (rho G) := by
  intro T t g
  rw [AutomorphicAction.cocharacterAction_act, rho_conjugation]

/-- Every actual cocharacter limit has the same image in the canonical quotient. -/
theorem rho_eq_of_hasLimit {T : Over (Spec (CommRingCat.of K))}
    {g l : T ⟶ G.X} (hl : Dynamic.HasLimit χ g l) :
    g ≫ rho G = l ≫ rho G := by
  have : IsSeparated (quotient G).hom := by
    change IsSeparated (Spec.map _)
    infer_instance
  exact AutomorphicAction.HasLimit.comp_eq_of_invariant
    (AutomorphicAction.cocharacterAction χ) (rho G) (rho_cocharacter_invariant G χ)
    ((AutomorphicAction.cocharacterAction_hasLimit χ g l).mpr hl)

/-- The chosen dynamic limit of a point of the parabolic preserves its quotient image. -/
theorem rho_limit [IsSeparated G.X.hom]
    {T : Over (Spec (CommRingCat.of K))} (g : (Dynamic.parabolic χ).carrier T) :
    g.val ≫ rho G = Dynamic.limit χ g ≫ rho G :=
  rho_eq_of_hasLimit G χ (Dynamic.hasLimit_limit χ g)

end Langlands.GroupScheme.ClassFunctions
