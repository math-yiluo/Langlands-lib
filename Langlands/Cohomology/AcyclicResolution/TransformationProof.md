# The resolution comparison commutes with derived natural transformations

Module `Langlands.Cohomology.AcyclicResolution.TransformationProof` proves the
published statement `Langlands.Cohomology.ResolutionComparisonTransformationStatement`
(module `Langlands.Cohomology.AcyclicResolution.Statement`, component 5 of the
acyclic-resolution comparison family).

## Theorem

```lean
theorem Langlands.Cohomology.resolutionComparisonTransformationStatement :
    ResolutionComparisonTransformationStatement.{u, v, u', v'}
```

The theorem keeps all four universe parameters of the statement: `C : Type u`
with `Category.{v} C`, and `D : Type u'` with `Category.{v'} D`. No universe is
fixed or identified with another, and the proof adds no hypotheses.

The statement says the following. Let `C` be an abelian category with injective
resolutions, `D` an abelian category, `F G : C ⥤ D` additive functors and
`α : F ⟶ G` a natural transformation. Let `ε : (single₀ C).obj A ⟶ K` be a
quasi-isomorphism into a cochain complex `K` indexed by `ℕ`. Let `I` be an
injective resolution of `A`, and `φ : K ⟶ I.cocomplex` a cochain map with
`ε ≫ φ = I.ι`. Then for every `n : ℕ`

    Hⁿ(α_K) ≫ Hⁿ(G φ) ≫ (I.isoRightDerivedObj G n).inv
      = Hⁿ(F φ) ≫ (I.isoRightDerivedObj F n).inv ≫ (NatTrans.rightDerived α n).app A,

where `Hⁿ` is `HomologicalComplex.homologyFunctor D _ n` and
`α_K = (NatTrans.mapHomologicalComplex α _).app K`. In words: the comparison
maps `Hⁿ(F K) ⟶ Rⁿ F A` and `Hⁿ(G K) ⟶ Rⁿ G A` of the statement module
intertwine `Hⁿ(α_K)` with Mathlib's derived transformation `Rⁿ α` at `A`.

## Implemented proof

The proof consists of three rewriting steps.

1. Mathlib's `InjectiveResolution.rightDerived_app_eq α I n` computes the
   derived transformation on the resolution `I`:
   `(NatTrans.rightDerived α n).app A = (I.isoRightDerivedObj F n).hom ≫
   Hⁿ(α_{I.cocomplex}) ≫ (I.isoRightDerivedObj G n).inv`. Rewriting with it and
   with `Iso.inv_hom_id_assoc` cancels `(I.isoRightDerivedObj F n).inv ≫
   (I.isoRightDerivedObj F n).hom`. The right side becomes
   `Hⁿ(F φ) ≫ Hⁿ(α_{I.cocomplex}) ≫ (I.isoRightDerivedObj G n).inv`.
2. `Functor.comp_map` unfolds the composite functors
   `F.mapHomologicalComplex _ ⋙ homologyFunctor D _ n`. Then
   `Functor.map_comp_assoc`, used from right to left, combines the two homology
   maps on each side. The goal becomes
   `Hⁿ(α_K ≫ G φ) ≫ inv = Hⁿ(F φ ≫ α_{I.cocomplex}) ≫ inv`.
3. The naturality square of the natural transformation
   `NatTrans.mapHomologicalComplex α _ : F.mapHomologicalComplex _ ⟶
   G.mapHomologicalComplex _` at `φ` is
   `F φ ≫ α_{I.cocomplex} = α_K ≫ G φ`. Rewriting with it makes the two sides
   syntactically equal, which closes the goal.

The proof uses neither the quasi-isomorphism hypothesis on `ε` nor the
augmentation compatibility `ε ≫ φ = I.ι`. The identity holds for every cochain
map `φ : K ⟶ I.cocomplex`. It also uses no acyclicity or left exactness, which
matches the statement's remark that this is an identity of maps before any
acyclicity assumption. The proof does not use the lift construction in
`Langlands.Cohomology.AcyclicResolution.Lift` or the comparison module
`Langlands.Cohomology.AcyclicResolution.Comparison`. It imports only the
statement module.

## Provenance

The statement Markdown cites the mathematical source: Cartan–Eilenberg,
*Homological Algebra*, V.4, p.87, together with the comparison of V.3,
equation (2). The derived transformation is obtained by applying the natural
transformation to a resolution and passing to cohomology. Mathlib's
`NatTrans.rightDerived` is built the same way. It applies
`NatTrans.mapHomotopyCategory α _` to Mathlib's chosen injective resolutions in
the homotopy category and then takes homology. `rightDerived_app_eq` gives the
resulting formula for an arbitrary injective resolution `I`. The Lean proof is the
naturality argument described there: the square commutes because `α` is natural
with respect to the lift `φ`.

## Checks

`lean_check` (environment `3b864ddf-f0af-4c18-8903-c6f813a0ce0f`) compiles the
module with no errors or warnings, at the default heartbeat limit. The theorem
depends only on the axioms `propext`, `Classical.choice` and `Quot.sound`.
