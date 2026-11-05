import Langlands.GroupScheme.Absolute.SolvableUnipotentFactorizationStatement
import Langlands.GroupScheme.Absolute.TriangularTorusConjugacy
import Langlands.GroupScheme.Absolute.SolvableSplitExtensionOneDimensional

/-! # Rational factorization from the solvable torus quotient -/

universe u

open CategoryTheory AlgebraicGeometry
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

/-- The ordered factors of a test point obtained from the inverse of the subgroup
multiplication isomorphism, followed by the two product projections. -/
noncomputable def subgroupMultiplicationFactors
    {S : Scheme.{u}} {U T B : GroupScheme S} (a : U ⟶ B) (t : T ⟶ B)
    [IsIso (subgroupMultiplication a t)] {V : Over S} (b : V ⟶ B.X) :
    (V ⟶ U.X) × (V ⟶ T.X) :=
  let w := b ≫ inv (subgroupMultiplication a t)
  (w ≫ fst U.X T.X, w ≫ snd U.X T.X)

/-- The factors constructed by inverse multiplication have product equal to the
original test point, in the specified order. -/
theorem subgroupMultiplicationFactors_spec
    {S : Scheme.{u}} {U T B : GroupScheme S} (a : U ⟶ B) (t : T ⟶ B)
    [IsIso (subgroupMultiplication a t)] {V : Over S} (b : V ⟶ B.X) :
    ((subgroupMultiplicationFactors a t b).1 ≫ a.hom.hom) *
      ((subgroupMultiplicationFactors a t b).2 ≫ t.hom.hom) = b := by
  simpa only [subgroupMultiplicationFactors, Category.assoc, IsIso.inv_hom_id,
    Category.comp_id] using
      (comp_subgroupMultiplication_eq a t (b ≫ inv (subgroupMultiplication a t))).symm

/-- An isomorphism given by ordered subgroup multiplication factors every test point
in the same order. -/
theorem exists_factorization_of_isIso_subgroupMultiplication
    {S : Scheme.{u}} {U T B : GroupScheme S} (a : U ⟶ B) (t : T ⟶ B)
    [IsIso (subgroupMultiplication a t)] {V : Over S} (b : V ⟶ B.X) :
    ∃ (v : V ⟶ U.X) (s : V ⟶ T.X),
      (v ≫ a.hom.hom) * (s ≫ t.hom.hom) = b := by
  exact ⟨(subgroupMultiplicationFactors a t b).1,
    (subgroupMultiplicationFactors a t b).2, subgroupMultiplicationFactors_spec a t b⟩

/-- The scheme-level semidirect-product statement implies the ordered rational-point
factorization for every caller-supplied maximal torus. -/
theorem solvableUnipotentFactorization_of_semidirect
    (hsemi : SolvableMaximalTorusSemidirectStatement.{u}) :
    SolvableUnipotentFactorizationStatement.{u} := by
  intro k _ _ B _ _ _ hB T t ht
  obtain ⟨U, a, ha, hUs, hUc, hU, hn, _, hiso⟩ := hsemi k B hB T t ht
  let := hiso
  exact ⟨U, a, ha, hUs, hUc, hU, hn,
    fun b => exists_factorization_of_isIso_subgroupMultiplication a t b⟩

/-- The only structural input still needed for rational factorization is the solvable
torus quotient: the published one-dimensional classification supplies the splitting
input of the published triangular-conjugacy theorem. -/
theorem solvableUnipotentFactorization_of_solvableTorusQuotient
    (hquot : SolvableTorusQuotientStatement.{u}) :
    SolvableUnipotentFactorizationStatement.{u} :=
  solvableUnipotentFactorization_of_semidirect
    (solvableMaximalTorusSemidirectStatement_of_solvableTorusQuotient hquot
      (solvableSplitExtension_of_oneDimensional perfectFieldOneDimensionalUnipotent))

end Langlands.GroupScheme
