# Lifting right resolutions into injective resolutions: proof

Authors: Worker 259, following the proof route that Worker 61 gave in the task
objective.

This pair proves Worker 3's published statement
`Langlands.Cohomology.ResolutionLiftStatement` (module
`Langlands.Cohomology.AcyclicResolution.Statement`). It adds one theorem and
no definitions, axioms or instances.

## Theorem

`Langlands.Cohomology.resolutionLiftStatement : ResolutionLiftStatement.{u, v}`

The theorem has exactly the statement's type, with the same two universe
parameters: `u` for the objects and `v` for the morphisms of the category. No
universe is fixed or identified with another, and no hypothesis is added.

Unfolded, it says the following. Let `C : Type u` be an abelian category with
`Category.{v} C`, let `A` be an object of `C`, let `K : CochainComplex C ℕ`, and
let `ε : (CochainComplex.single₀ C).obj A ⟶ K` be a quasi-isomorphism, so that
`ε` is a right resolution of `A` whose terms are arbitrary. Let `I` be any
injective resolution of `A`, with augmentation `I.ι` and complex
`I.cocomplex`. Then:

1. there is a cochain map `φ : K ⟶ I.cocomplex` with `ε ≫ φ = I.ι`;
2. any two cochain maps `φ ψ : K ⟶ I.cocomplex` with `ε ≫ φ = I.ι` and
   `ε ≫ ψ = I.ι` are homotopic, that is, `Nonempty (Homotopy φ ψ)`.

This is the case `f = 𝟙 A` of Cartan–Eilenberg, *Homological Algebra*, Chapter V,
Proposition 1.1a, with an injective resolution as the target. The statement's
Markdown records the source correspondence; this proof does not change it.

## Proof

The proof uses only the published construction in
`Langlands.Cohomology.AcyclicResolution.Lift` (Worker 61). That module assumes a
quasi-isomorphism `ε : A[0] ⟶ K` and a target complex `L` whose terms are all
injective. For an injective resolution `I`, the instance `I.injective` that
Mathlib's `InjectiveResolution` provides supplies this for `L = I.cocomplex`.

- Existence. Take `φ := AcyclicResolution.lift ε (𝟙 A) I.ι`. The lemma
  `AcyclicResolution.comp_lift` gives
  `ε ≫ φ = (CochainComplex.single₀ C).map (𝟙 A) ≫ I.ι`. Rewriting with
  `CategoryTheory.Functor.map_id` and `Category.id_comp` turns the right side
  into `I.ι`.
- Uniqueness up to homotopy. If `ε ≫ φ = I.ι` and `ε ≫ ψ = I.ι`, then
  `ε ≫ φ = ε ≫ ψ` (the term `hφ.trans hψ.symm`), and
  `AcyclicResolution.homotopyOfComp ε φ ψ` turns this equation into a
  `Homotopy φ ψ`. That construction needs neither an augmentation of the target
  nor its exactness, only the injectivity of its terms.

The proof begins by introducing the universally quantified data. The
quasi-isomorphism hypothesis enters as a local instance, which `lift` and
`homotopyOfComp` take as their `[QuasiIso ε]` argument.

## Verification

A development `lean_check` of this module, inspecting the theorem, reported
zero errors and zero warnings. The theorem's type is the constant
`Langlands.Cohomology.ResolutionLiftStatement` with level parameters `u, v`. It
depends only on the axioms `propext`, `Classical.choice` and `Quot.sound`. This
is not acceptance: independent review and the project's validation are
separate.

## Scope

This module proves only `ResolutionLiftStatement`. The other components of
Worker 3's family (`AcyclicResolutionComparisonStatement`,
`ResolutionComparisonIndependenceStatement`,
`ResolutionComparisonNaturalityStatement`,
`ResolutionComparisonTransformationStatement`,
`AcyclicResolutionEquivarianceStatement`) and their conjunction
`AcyclicResolutionComparisonStatements` are not proved here. This pair does not
edit the statement pair, the `Lift` pair or anything they import.
