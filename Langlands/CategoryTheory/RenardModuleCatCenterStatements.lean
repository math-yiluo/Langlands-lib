import Mathlib.Algebra.Algebra.Basic
import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.Algebra.Ring.Subring.Basic
import Mathlib.CategoryTheory.Center.Linear

/-!
# Renard A.X: the center of the category of unital modules

Source: Renard, *Représentations des groupes réductifs p-adiques* (French edition
dated 9 July 2026), Appendix A.X "Centre d'une catégorie", printed page 269 /
PDF page 275: for the category `M(A)` of unital modules over a unital ring `A`,
the center of the category is naturally identified with the center of `A`.

The center of a category is Mathlib's `CatCenter C = End (𝟭 C)`. The category
`M(A)` is the actual category `ModuleCat.{max u v} R` of unital left `R`-modules
with carriers in universe `max u v`, for an arbitrary ring `R : Type u` and an
independent universe `v`. The natural map is Mathlib's existing ring
homomorphism `Linear.toCatCenter (Subring.center R) (ModuleCat.{max u v} R)`,
which uses the scoped `Subring.center R`-linear structure of
`ModuleCat.Algebra.instLinear`; its component at `M` is `m ↦ (c : R) • m`.

Only propositions are stated here; none of them is proved or assumed.
-/

universe u v

open CategoryTheory
open scoped ModuleCat.Algebra

namespace Langlands.Renard

variable (R : Type u) [Ring R]

/-- Normalization of the map in Renard A.X: the component at a unital left
module `M` of the image of a central element `c` under the scalar-action ring
homomorphism `Linear.toCatCenter (Subring.center R) (ModuleCat.{max u v} R)` is
left multiplication by `(c : R)` on `M`. -/
@[pp_with_univ]
def ModuleCatCenterScalarComponentStatement : Prop :=
  ∀ (c : Subring.center R) (M : ModuleCat.{max u v} R) (m : M),
    ((Linear.toCatCenter (Subring.center R) (ModuleCat.{max u v} R) c).app M).hom m =
      (c : R) • m

/-- Renard A.X, example: the scalar-action ring homomorphism from the center of
`R` to the center `CatCenter (ModuleCat.{max u v} R)` of the category of unital
left `R`-modules is bijective. -/
@[pp_with_univ]
def ModuleCatCenterBijectiveStatement : Prop :=
  Function.Bijective (Linear.toCatCenter (Subring.center R) (ModuleCat.{max u v} R))

/-- Renard A.X, example: there is a ring isomorphism from the center of `R` to
the center of the category of unital left `R`-modules whose underlying ring
homomorphism is exactly the scalar-action map
`Linear.toCatCenter (Subring.center R) (ModuleCat.{max u v} R)`. -/
@[pp_with_univ]
def ModuleCatCenterRingEquivStatement : Prop :=
  ∃ e : Subring.center R ≃+* CatCenter (ModuleCat.{max u v} R),
    e.toRingHom = Linear.toCatCenter (Subring.center R) (ModuleCat.{max u v} R)

/-- Renard A.X, example: the center of the category `ModuleCat.{max u v} R` of
unital left `R`-modules is canonically identified with the center of the ring
`R`, through the scalar-action ring homomorphism. The two clauses are the
bijectivity of that map and the existence of a ring isomorphism whose underlying
ring homomorphism is that map. -/
@[pp_with_univ]
def ModuleCatCenterIdentificationStatement : Prop :=
  ModuleCatCenterBijectiveStatement.{u, v} R ∧ ModuleCatCenterRingEquivStatement.{u, v} R

end Langlands.Renard
