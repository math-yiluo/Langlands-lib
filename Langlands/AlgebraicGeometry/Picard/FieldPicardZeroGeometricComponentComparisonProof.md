# Geometric Picard-zero families and the full Picard origin component

`Langlands.AbelianScheme.fieldPicardZeroGeometricComponentComparison` proves
the exact published proposition
`Langlands.AbelianScheme.FieldPicardZeroGeometricComponentComparisonStatement.{u}`.
Its only universe parameter is the arbitrary universe `u`, and it has no
additional premise.

For every field `k : Type u`, abelian scheme `A` over `Spec k`, parameter
`P : Over (Spec k)`, actual rigidified family `L`, local finite type of `P.hom`,
and full universality of `L` on every test scheme, it gives the equivalence
at every actual geometric point `s : Spec K ⟶ P.left`, with `K : Type u`
algebraically closed:

```text
IsPicardZeroFamily A (relativePullback (Over.homMk s rfl) L)
  ↔ Set.range s ⊆ connectedComponent (fullPicardOriginPoint k A L hL).
```

Here the abbreviated pullback denotes the published
`RigidifiedLineBundle.relativePullback A.X.hom (unitSection A)
(unitSection_comp A)` functor applied to the actual family. The left side
retains its quantification over all further geometric fibres. The origin
and connected component on the right are the published `fullPicardOriginPoint`
and Mathlib's actual `connectedComponent`.

## Implemented proof

The proof supplies the published theorem
`Langlands.AbelianScheme.smoothFamilyPicardZeroComparison` from
`SmoothFamilyPicardZeroComparisonProof` to
`fieldPicardZeroGeometricComponentComparison_of` in
`FieldPicardZeroComponentForward`. The smooth-family theorem proves the exact
aggregate comparison without additional premises. The reduction combines the
following two implications.

For the forward implication, its family conjunct turns the Picard-zero
condition into an actual smooth-family witness over `K`. The witness has a
geometrically integral parameter, two rational endpoints and an actual line
bundle with both endpoint isomorphisms. The proof transports the witness to
the parameter-first relative space for `A` and normalizes it along the unit
section. The normalizing bundle restricts trivially at each rational endpoint
because every line bundle on `Spec K` is trivial. Full universality then
classifies the normalized rigidified family by a map to `P`. Its image
contains the published origin and the range of `s`. Geometric integrality of
the witness parameter implies irreducibility, so this image is preconnected
and lies in the origin component.

For the reverse implication,
`isPicardZeroFamily_of_mem_originComponent` in
`FieldPicardZeroComponentAssembly` invokes the published theorem
`Langlands.AbelianScheme.fieldPicardZeroComponentConstancy`. It compares `s`
with the geometric point obtained from the trivial parameter over
`AlgebraicClosure k`. Every point of the latter maps to the published origin,
and its pulled-back family is isomorphic to the relative trivial family by
the full universal property. It is therefore Picard-zero, and constancy on
the common connected component gives the exact geometric-family condition
at `s`.

This route compares both geometric points inside the supplied `P`. It needs
no separate assumption identifying an origin component after field extension.
The published smooth-family comparison accounts for the actual family
condition in the forward implication, and the published constancy theorem
concludes that same condition in the reverse implication.

## Provenance and scope

This is a derived assembly of the two companion helper modules and the
published smooth-family and constancy proofs. The helpers retain the carried
argument of historical Worker 860. Worker 2104 adapted it to the published
constancy theorem, supplied the published smooth-family proof, and wrote this
final assembly and explanation. Imported results retain the authorship and
source provenance documented in their own companions.

The proof adds no field, projectivity, representability, group-law,
base-change, openness or dual-existence premise. Its dependencies precede
geometric-point and all-test-scheme Picard-zero openness; neither openness
statement, a supplied-open-locus-to-component corollary, nor an assumed
`IsPicardZeroOpenLocus` is used. The target pair, its imported closure, and
the other protected statement closures are unchanged.
