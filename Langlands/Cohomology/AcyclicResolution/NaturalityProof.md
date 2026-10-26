# Naturality of the resolution comparison: proof

Author: Worker 718. The proof applies Worker 61's published theorem
`Langlands.Cohomology.AcyclicResolution.comparison_naturality` (module
`Langlands.Cohomology.AcyclicResolution.Comparison`).

This pair proves Worker 3's published statement
`Langlands.Cohomology.ResolutionComparisonNaturalityStatement` (module
`Langlands.Cohomology.AcyclicResolution.Statement`). It adds one theorem and no
definitions, axioms or instances.

Composition `f ≫ g` is `f` followed by `g`. `A[0]` stands for
`(CochainComplex.single₀ C).obj A`, the cochain complex with `A` in degree zero and zero
elsewhere. `Hⁿ(F φ)` abbreviates
`(F.mapHomologicalComplex _ ⋙ HomologicalComplex.homologyFunctor D _ n).map φ`, the map
that `φ` induces on the degree-`n` cohomology of `F` applied termwise.

## Theorem

`Langlands.Cohomology.resolutionComparisonNaturalityStatement :
ResolutionComparisonNaturalityStatement.{u, v, u', v'}`

The theorem has exactly the statement's type, with the same four universe parameters:
`u` and `v` for the objects and morphisms of `C`, and `u'` and `v'` for those of `D`. No
universe is fixed or identified with another, and no hypothesis is added.

Unfolded, it says the following. Let `C : Type u` be an abelian category with
`Category.{v} C` and `[HasInjectiveResolutions C]`, let `D : Type u'` be an abelian
category with `Category.{v'} D`, and let `F : C ⥤ D` be an additive functor (`F` need not
be left exact). Let `A` and `B` be objects of `C`, let `K` and `L` be cochain complexes in
`C` indexed by `ℕ`, and let `ε : A[0] ⟶ K` and `η : B[0] ⟶ L` be quasi-isomorphisms. Let
`f : A ⟶ B` and let `g : K ⟶ L` be a cochain map with
`ε ≫ g = (CochainComplex.single₀ C).map f ≫ η`. Let `I` be an injective resolution of `A`
and `J` one of `B`, and let `φ : K ⟶ I.cocomplex` and `ψ : L ⟶ J.cocomplex` be cochain
maps with `ε ≫ φ = I.ι` and `η ≫ ψ = J.ι`. Then for every `n : ℕ`,

`Hⁿ(F g) ≫ Hⁿ(F ψ) ≫ (J.isoRightDerivedObj F n).inv =
Hⁿ(F φ) ≫ (I.isoRightDerivedObj F n).inv ≫ (F.rightDerived n).map f`.

Here `I.isoRightDerivedObj F n` is Mathlib's identification of `(F.rightDerived n).obj A`
with the degree-`n` cohomology of `F` applied to `I.cocomplex`. The terms of `K` and `L`
are arbitrary; no acyclicity is assumed. The statement's Markdown records the source
correspondence (Cartan–Eilenberg, *Homological Algebra*, Chapter V); this proof does not
change it.

## Proof

Worker 61's module `Langlands.Cohomology.AcyclicResolution.Comparison` defines
`comparison F I φ n := Hⁿ(F φ) ≫ (I.isoRightDerivedObj F n).inv` and proves
`comparison_naturality F ε η f g hg φ ψ hφ hψ n`:

`Hⁿ(F g) ≫ comparison F J ψ n = comparison F I φ n ≫ (F.rightDerived n).map f`,

under `[QuasiIso ε]` (it does not use `QuasiIso η`). Its own proof takes
`h := InjectiveResolution.desc f J I`, obtains a homotopy `g ≫ ψ ≃ φ ≫ h` from
`AcyclicResolution.homotopyOfComp ε` (both composites with `ε` equal
`(single₀ C).map f ≫ J.ι`), transports it by `F.mapHomotopy` and
`Homotopy.homologyMap_eq`, and finishes with Mathlib's
`InjectiveResolution.isoRightDerivedObj_inv_naturality` for `h` over `f`.

The implemented proof of the statement:

1. `intro` introduces all universally quantified data. The two quasi-isomorphism
   hypotheses enter as anonymous local instances; `comparison_naturality` uses the one
   for `ε` as its `[QuasiIso ε]` argument.
2. `have h := AcyclicResolution.comparison_naturality F ε η f g hg φ ψ hφ hψ n`.
3. Rewriting `h` twice with the equation of `AcyclicResolution.comparison` and once with
   `Category.assoc` turns `(Hⁿ(F φ) ≫ (I.isoRightDerivedObj F n).inv) ≫
   (F.rightDerived n).map f` into the right-associated form of the statement; the left
   side becomes `Hⁿ(F g) ≫ Hⁿ(F ψ) ≫ (J.isoRightDerivedObj F n).inv`.
4. `exact h` closes the goal.

## Verification

A development `lean_check` of this module, inspecting the theorem, reported zero errors
and zero warnings. The theorem's type is the constant
`Langlands.Cohomology.ResolutionComparisonNaturalityStatement` with level parameters
`u, v, u', v'`. It depends only on the axioms `propext`, `Classical.choice` and
`Quot.sound`. This is not acceptance: independent review and the project's validation are
separate.

## Scope

This module proves only `ResolutionComparisonNaturalityStatement`. The other components
of Worker 3's family (`ResolutionLiftStatement`, `AcyclicResolutionComparisonStatement`,
`ResolutionComparisonIndependenceStatement`,
`ResolutionComparisonTransformationStatement`, `AcyclicResolutionEquivarianceStatement`)
and their conjunction `AcyclicResolutionComparisonStatements` are not proved here. This
pair does not edit the statement pair, the `Lift` pair, the `Comparison` pair or anything
they import.
