# Isomorphism criterion for the derived composite comparison

This is an internal categorical statement derived from the actual comparison
constructed in `AcyclicResolution.DerivedCompositeComparison` and the degreewise
criterion `isIso_compComparison` in `AlgebraicGeometry.Modules.PushforwardComparison`.
It introduces no external literature assertion.

`DerivedCompositeIsomorphismStatement` quantifies over three abelian categories
`C`, `D`, and `E`, with independent object, morphism and derived-localization
universes. The categories `C` and `D` have enough injectives. It takes additive
functors `F : C ⥤ D`, `G : D ⥤ E`, and `H : C ⥤ E`, with `F` and `G` preserving
finite limits, and a specified natural isomorphism `e : F ⋙ G ≅ H`.

For every actual object `A : C` with
`IsZero ((F.rightDerived (q + 1)).obj A)` for every natural `q`, suppose that
`F` sends each injective object `J` of `C` to a `G`-acyclic object: every
`(G.rightDerived (q + 1)).obj (F.obj J)` is zero. The conclusion is
`IsIso (derivedCompComparison G e A hA)` for the specified canonical map

```text
RH(A) → RG(F(A))
```

in the actual unbounded derived category of `E`. Both derived objects are the
bounded below right derived functors of objects placed in degree zero, included
into that derived category. The map is the one already specified by the
published comparison construction, including its resolution and extension
identifications. The statement does not substitute an arbitrary isomorphism
between the two objects.

The intended internal deduction uses `derivedCompComparison_homology` and
`isIso_compComparison` for every nonnegative degree. In negative degrees,
`DerivedPlus.isZero_homology_of_neg` makes both cohomology objects zero.
Mathlib's `DerivedCategory.isIso_iff` then detects the isomorphism. This file
states that deduction as a proposition; its proof is a separate obligation.
It asserts no geometric base change, perfection, fibre-section lifting or cube
theorem.
