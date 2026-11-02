import Langlands.AlgebraicGeometry.EtaleEquivalenceRelationTupleDistinctReindex
import Langlands.AlgebraicGeometry.FiniteFreeSchemeActionQuotient
import Mathlib.Algebra.Group.ULift

/-! # Affine symmetric quotients of distinct related tuples -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.AlgebraicGeometry.EtaleEquivalenceRelation

/-- A universe-compatible symmetric group on the `n + 1` coordinates. -/
abbrev TuplePermutationGroup (n : ℕ) := ULift.{u} (Equiv.Perm (Fin (n + 1)))

variable (E : EtaleEquivalenceRelation.{u}) [IsSeparated E.s]

/-- The free action which permutes the coordinates of a distinct tuple. -/
def tuplePermutationAction (n : ℕ) :
    FiniteFreeSchemeAction (TuplePermutationGroup.{u} n) (E.tupleDistinctScheme n) where
  act g := E.tupleDistinctReindexIso g.down
  one := by
    apply E.tupleDistinct_hom_ext n
    intro i
    simp
  mul g h := by
    apply E.tupleDistinct_hom_ext n
    intro i
    simp
  free f := by
    intro g h hgh
    apply ULift.ext
    apply Equiv.ext
    intro i
    apply E.tupleDistinct_coordinates_injective n f
    simpa using congrArg (fun k => k ≫ E.tupleDistinctProjection n i) hgh

@[reassoc (attr := simp)]
theorem tuplePermutationAction_projection (n : ℕ) (g : TuplePermutationGroup.{u} n)
    (i : Fin (n + 1)) :
    ((E.tuplePermutationAction n).act g).hom ≫ E.tupleDistinctProjection n i =
      E.tupleDistinctProjection n (g.down i) :=
  E.tupleDistinctReindexIso_hom_projection g.down i

section Affine

variable [IsAffine E.U] [IsAffine E.R]

/-- The affine symmetric quotient of the distinct related tuples. -/
def tupleSymmetricQuotient (n : ℕ) : (E.tuplePermutationAction n).AffineQuotient :=
  (E.tuplePermutationAction n).quotient

/-- The scheme of unordered distinct related tuples of length `n + 1`. -/
abbrev tupleSymmetricScheme (n : ℕ) : Scheme.{u} :=
  (E.tupleSymmetricQuotient n).scheme

/-- The finite étale surjection from ordered to unordered distinct tuples. -/
abbrev tupleSymmetricMap (n : ℕ) :
    E.tupleDistinctScheme n ⟶ E.tupleSymmetricScheme n :=
  (E.tupleSymmetricQuotient n).map

instance tupleSymmetricScheme_isAffine (n : ℕ) : IsAffine (E.tupleSymmetricScheme n) :=
  (E.tupleSymmetricQuotient n).isAffine

instance tupleSymmetricMap_isFinite (n : ℕ) : IsFinite (E.tupleSymmetricMap n) :=
  (E.tupleSymmetricQuotient n).finite

instance tupleSymmetricMap_etale (n : ℕ) : Etale (E.tupleSymmetricMap n) :=
  (E.tupleSymmetricQuotient n).etale

instance tupleSymmetricMap_surjective (n : ℕ) : Surjective (E.tupleSymmetricMap n) :=
  (E.tupleSymmetricQuotient n).surjective

@[reassoc (attr := simp)]
theorem tupleSymmetricMap_invariant (n : ℕ) (g : Equiv.Perm (Fin (n + 1))) :
    (E.tupleDistinctReindexIso g).hom ≫ E.tupleSymmetricMap n =
      E.tupleSymmetricMap n :=
  (E.tupleSymmetricQuotient n).invariant (ULift.up g)

theorem tupleSymmetricMap_isPullback (n : ℕ) :
    IsPullback (E.tuplePermutationAction n).target (E.tuplePermutationAction n).source
      (E.tupleSymmetricMap n) (E.tupleSymmetricMap n) :=
  (E.tupleSymmetricQuotient n).isPullback

def tupleSymmetricMap_isColimit (n : ℕ) :
    IsColimit (Cofork.ofπ (E.tupleSymmetricMap n)
      (E.tupleSymmetricQuotient n).condition) :=
  (E.tupleSymmetricQuotient n).isColimit

/-- Descent of a morphism which is unchanged by all coordinate permutations. -/
def tupleSymmetricDesc (n : ℕ) {Y : Scheme.{u}} (f : E.tupleDistinctScheme n ⟶ Y)
    (hf : ∀ g : Equiv.Perm (Fin (n + 1)), (E.tupleDistinctReindexIso g).hom ≫ f = f) :
    E.tupleSymmetricScheme n ⟶ Y :=
  (E.tupleSymmetricQuotient n).desc f (fun g => hf g.down)

@[reassoc (attr := simp)]
theorem tupleSymmetricMap_desc (n : ℕ) {Y : Scheme.{u}}
    (f : E.tupleDistinctScheme n ⟶ Y)
    (hf : ∀ g : Equiv.Perm (Fin (n + 1)), (E.tupleDistinctReindexIso g).hom ≫ f = f) :
    E.tupleSymmetricMap n ≫ E.tupleSymmetricDesc n f hf = f :=
  (E.tupleSymmetricQuotient n).map_desc f (fun g => hf g.down)

theorem tupleSymmetric_hom_ext (n : ℕ) {Y : Scheme.{u}}
    (f g : E.tupleSymmetricScheme n ⟶ Y)
    (h : E.tupleSymmetricMap n ≫ f = E.tupleSymmetricMap n ≫ g) : f = g :=
  (E.tupleSymmetricQuotient n).hom_ext f g h

end Affine

end Langlands.AlgebraicGeometry.EtaleEquivalenceRelation
