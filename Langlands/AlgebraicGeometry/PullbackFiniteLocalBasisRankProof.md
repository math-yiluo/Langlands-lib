# Pullback preserves finite local bases and specified rank

The theorem `Langlands.Scheme.Modules.pullbackFiniteLocalBasisRank` proves the exact published proposition `Langlands.Scheme.Modules.PullbackFiniteLocalBasisRankStatement` in arbitrary universe `u`. For every scheme morphism `f : X ⟶ Y` and module sheaf `M` on `Y`, the actual pullback preserves both the existence of one finite local basis datum and each specified finite local rank. There is no condition on `f`.

## Implemented proof

Let `q` be the given local generator datum. The new covering family has the same index type `q.I` and consists of the inverse-image opens `f ⁻¹ᵁ q.X i`. The proof converts `q.coversTop` into the assertion that the supremum of its opens is top, applies preservation of suprema by inverse image, and converts back to `CoversTop`.

On an open `U` of `Y`, the private functor `localPullback` is the composite

```text
modules on the over-category of U
  → modules on the open subscheme U
  → modules on the open subscheme f⁻¹(U)
  → modules on the over-category of f⁻¹(U).
```

The first and last functors are `Scheme.Modules.overEquiv U` and the inverse of `Scheme.Modules.overEquiv (f ⁻¹ᵁ U)`. The middle functor is the actual `Scheme.Modules.pullback (f ∣_ U)`. Equivalences and this left adjoint preserve the colimits needed by `SheafOfModules.GeneratingSections.map`. The private `localPullbackUnit` combines the unit isomorphisms for the two equivalences with `Langlands.Scheme.Modules.pullbackUnitIso`.

The comparison `localPullbackIso` identifies the image of `M.over U` with the over-category restriction of the actual pullback of `M`. It uses `Scheme.Modules.overFunctorEquiv` on both spaces, `Langlands.AlgebraicGeometry.Picard.restrictPullbackIso`, and the unit isomorphism of the target equivalence. Thus the constructed datum belongs to the actual pullback in the target statement.

`pullbackGenerators` maps each given generator family through this functor and then through the comparison isomorphism, using `GeneratingSections.map` followed by `GeneratingSections.ofEpi`. Both operations preserve the generator index type definitionally. Mathlib's `GeneratingSections.map_π_eq` identifies the mapped free presentation with the free-sheaf comparison followed by the functorial image of the original presentation; its `IsIso` instance makes this an isomorphism when the original presentation is one. The subsequent `ofEpi_π` formula composes that presentation with `localPullbackIso.hom`, also an isomorphism. The lemma `pullbackLocalData_free` packages these isomorphisms into `IsLocallyFreeData`.

For the finite-local-basis clause, the original finiteness witness for each generator index type applies unchanged to this new datum. In particular, the proof constructs one datum that is simultaneously locally free and finite type. For the fixed-rank clause, every supplied equivalence of a local index type with `Fin n` applies unchanged. No choice of a common rank on a disconnected scheme is made, and no rank uniqueness or nonemptiness assertion is needed. Rank zero and empty covers are included in the same construction.

## Provenance and dependencies

The geometric source is the registered Stacks Project source `stacks-local-freeness-invertibility-sections-2026-10-21`, folder SHA256 `6d1641a9deb284be889ee6e2630a2be6e57cc5985c80af2c9da7d17543ed0785`, retained file `01C5.html`: Definition 17.14.1 (01C6), parts (2)–(3), describes finite local bases and specified rank; Lemma 17.14.3 (01C8) states preservation of local freeness by pullback and omits its proof. The finite-basis and same-rank refinements proved here are derived by retaining the basis indices, rather than attributed to an explicit stronger statement in that lemma.

The proof imports the published statement, the existing restriction/pullback and unit comparison API, and Mathlib's site description of open covers. It uses no new substantive prerequisite or assumption beyond the target's hypotheses. Its private auxiliary definitions only implement this proof's transport of local data. It establishes neither smooth differential freeness nor the parent Lie theorem.

Worker 5 implemented the proof. Worker 124 supplied the task's transport API guidance and the precise open-cover conversion reference.
