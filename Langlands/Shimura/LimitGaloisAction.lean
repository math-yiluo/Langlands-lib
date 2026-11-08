import Langlands.Shimura.DecompositionGroupAction

/-! # Decomposition groups and Frobenius on limits of Galois actions

For a diagram of Galois actions on modules over a commutative ring, with a limit in the category
of actions that is preserved by the forgetful functor, the limit is unramified at a finite place
when every vertex is, and the projections intertwine the geometric Frobenius endomorphisms.
See `LimitGaloisAction.md`.
-/

noncomputable section

universe u t w uK

set_option autoImplicit false

namespace Langlands.Shimura.LimitGaloisAction

open CategoryTheory CategoryTheory.Limits
open Langlands.GaloisRepresentation (ClosureEmbedding)
open Langlands.Shimura.DecompositionGroupAction (IsUnramifiedAt IsUnramifiedAlong
  geometricFrobenius localRestriction)

variable {R : Type u} [CommRing R] {K : Type uK} [Field K] [NumberField K]
  (v : Global.FinitePlace K) {J : Type w} [Category.{t} J]
  (M : J ⥤ Action (ModuleCat.{u} R) (Field.absoluteGaloisGroup K)) [HasLimit M]
  [PreservesLimit M (Action.forget (ModuleCat.{u} R) (Field.absoluteGaloisGroup K))]

variable {v M} in
/-- If every vertex of the diagram is unramified at `v` along `ι`, so is its limit: an inertia
element acts on the limit by an endomorphism that is compatible with the identity on every
vertex, hence is the identity. -/
theorem isUnramifiedAlong_limit
    {ι : ClosureEmbedding (NumberField.FinitePlace.embedding (K := K) v)}
    (hM : ∀ j, IsUnramifiedAlong (ModuleCat.{u} R) v (M.obj j) ι) :
    IsUnramifiedAlong (ModuleCat.{u} R) v (limit M) ι := by
  intro i
  change (limit M).ρ (localRestriction v ι i.val) = 𝟙 (limit M).V
  apply (isLimitOfPreserves (Action.forget (ModuleCat.{u} R) _) (limit.isLimit M)).hom_ext
  intro j
  have hc := (limit.π M j).comm (localRestriction v ι i.val)
  have hj : (M.obj j).ρ (localRestriction v ι i.val) = 𝟙 (M.obj j).V := hM j i
  change (limit M).ρ (localRestriction v ι i.val) ≫ (limit.π M j).hom =
    𝟙 (limit M).V ≫ (limit.π M j).hom
  rw [hc, hj, Category.comp_id, Category.id_comp]

variable {v M} in
/-- If every vertex of the diagram is unramified at `v`, so is its limit. -/
theorem isUnramifiedAt_limit (hM : ∀ j, IsUnramifiedAt (ModuleCat.{u} R) v (M.obj j)) :
    IsUnramifiedAt (ModuleCat.{u} R) v (limit M) :=
  isUnramifiedAlong_limit hM

omit [PreservesLimit M (Action.forget (ModuleCat.{u} R) (Field.absoluteGaloisGroup K))] in
/-- The projections of the limit intertwine the geometric Frobenius endomorphisms at `v`
along `ι`. -/
theorem geometricFrobenius_limit_π
    (ι : ClosureEmbedding (NumberField.FinitePlace.embedding (K := K) v)) (j : J) :
    geometricFrobenius (ModuleCat.{u} R) v (limit M) ι ≫ (limit.π M j).hom =
      (limit.π M j).hom ≫ geometricFrobenius (ModuleCat.{u} R) v (M.obj j) ι :=
  DecompositionGroupAction.geometricFrobenius_naturality (limit.π M j) ι

end Langlands.Shimura.LimitGaloisAction
