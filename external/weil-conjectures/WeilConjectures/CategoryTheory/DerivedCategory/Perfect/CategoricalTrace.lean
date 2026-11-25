/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.Perfect

/-!
# The categorical trace of an endomorphism of a perfect complex

Let `A` be a commutative ring. The category `D^b_fin(A)` of the trace formula chapter is the
full subcategory of perfect complexes of `D(A)`, those quasi-isomorphic to a bounded complex
of finitely generated projective modules. A perfect complex `P` is dualizable for the derived
tensor product, with dual `P^∨ = RHom_A(P, A)`, coevaluation `A ⟶ P ⊗ᴸ P^∨` and evaluation
`P^∨ ⊗ᴸ P ⟶ A`; for an endomorphism `v` of `P` the categorical trace
`tr_A(v | P) = ev_P ∘ sym ∘ (v ⊗ 1) ∘ coev_P` is an endomorphism of the unit `A`, read as the
scalar by which it acts on `H⁰(A) = A`.

## Main definitions

- `DerivedCategory.perfect`: the perfect complexes, as an object property of `D(A)`, and
  `DerivedCategory.Perf`: the category `D^b_fin(A)`.
- `DerivedCategory.unitEndScalar`: the degree-`0` scalar `End_{D(A)}(A) ⟶ A`.
- `DerivedCategory.IsPerfect.categoricalTrace`: the categorical trace `tr_A(v | P) ∈ A`.

## Implementation notes

`D(A)` only carries a braiding up to `Nonempty` (`DerivedCategory.nonempty_braidedCategory`), so
the trace is defined for an arbitrary braiding instance; the intended one is the Koszul
symmetry, for which `DerivedCategory.trace_eq_algebraMap_sum_negOnePow_linearMapTrace`
identifies the trace with the alternating sum of the traces of the components. The right dual
used is an arbitrary choice of one; the categorical trace does not depend on it.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

namespace DerivedCategory

variable (R : Type u) [CommRing R] [HasDerivedCategory.{u} (ModuleCat.{u} R)]

/-- Blueprint `definition-categorical-trace`: Perfect complex and its categorical trace (the
category `D^b_fin(A)`).

The perfect complexes of `D(A)`, those quasi-isomorphic to a bounded complex of finitely
generated projective `A`-modules, as an object property. Over a local ring such as
`A = A_{E,n}` these are the complexes quasi-isomorphic to a bounded complex of finitely
generated free modules (`DerivedCategory.IsPerfect.exists_free`). -/
def perfect : ObjectProperty (DerivedCategory (ModuleCat.{u} R)) :=
  fun C ↦ C.IsPerfect

/-- Blueprint `definition-categorical-trace`: the category `D^b_fin(A)` of perfect complexes, as a
full subcategory of `D(A)`. -/
abbrev Perf : Type _ := (perfect R).FullSubcategory

/-- The degree-`0` cohomology of the unit of `D(A)` is `A`: the unit is `A` placed in degree
`0`. -/
noncomputable def homologyZeroUnitIso :
    (homologyFunctor (ModuleCat.{u} R) 0).obj (𝟙_ (DerivedCategory (ModuleCat.{u} R))) ≅
      ModuleCat.of R R :=
  (homologyFunctor (ModuleCat.{u} R) 0).mapIso (singleFunctorObjUnitIso _).symm ≪≫
    (singleFunctorCompHomologyFunctorIso (ModuleCat.{u} R) 0).app (𝟙_ _)

/-- Blueprint `definition-categorical-trace`: the identification `End_{D(A)}(A) ⟶ A` sending an
endomorphism of the unit `A` of `D(A)` to its degree-`0` scalar, the image of `1` under the
induced endomorphism of `H⁰(A) = A`. -/
noncomputable def unitEndScalar (φ : 𝟙_ (DerivedCategory (ModuleCat.{u} R)) ⟶ 𝟙_ _) : R :=
  ((homologyZeroUnitIso R).inv ≫ (homologyFunctor (ModuleCat.{u} R) 0).map φ ≫
    (homologyZeroUnitIso R).hom).hom (1 : R)

@[simp]
lemma unitEndScalar_id : unitEndScalar R (𝟙 _) = 1 := by
  simp [unitEndScalar]

variable {R}

/-- Blueprint `definition-categorical-trace`: Perfect complex and its categorical trace.

For a perfect complex `P ∈ D^b_fin(A)` and an endomorphism `v : P ⟶ P`, the categorical trace
`tr_A(v | P) = ev_P ∘ sym ∘ (v ⊗ᴸ 1) ∘ coev_P ∈ End_{D(A)}(A)`
(`CategoryTheory.MonoidalCategory.trace`, for a chosen right dual of the dualizable `P`), read
as an element of `A` through its degree-`0` scalar (`DerivedCategory.unitEndScalar`). The
braiding `sym` is the given braiding of `D(A)`. -/
noncomputable def IsPerfect.categoricalTrace [BraidedCategory (DerivedCategory (ModuleCat.{u} R))]
    {P : DerivedCategory (ModuleCat.{u} R)} (hP : P.IsPerfect) (v : P ⟶ P) : R :=
  letI : HasRightDual P := hP.isDualizable.some
  unitEndScalar R (MonoidalCategory.trace v)

end DerivedCategory
