# Classification by disjoint coproduct families and descent of labels

This internal module assembles constant-scheme families and descends their
classifying morphisms from covers. Throughout, `G,H` are group schemes over
an arbitrary scheme `S`. No scheme representing isomorphisms is assumed. The refinement identities
are imported from the existing `IsomorphismPresheaf` module.

`LocalGroupIso.constantFamily r` takes an arbitrary type `D : Type u` and a
family `r : D → LocalGroupIso G H (Over.mk (𝟙 S))`. It gives an all-test
natural isomorphism family over the actual scheme
`GroupIsomorphismScheme.constantParameter S D`. This is the coproduct of
copies of `S` indexed by `D`, and the definition uses `LocalGroupIso.coproduct`.
The label type may be empty or infinite.

`constantFamily_refine_injective` assumes that equal restrictions of two
representatives to a test scheme force their labels to agree or that test
to be empty. Under exactly this disjointness assumption, the family is
injective on morphisms from every relative scheme test. The more general
`coproduct_refine_injective` allows nonconstant components and additionally
assumes injectivity on each component. Its proof pulls back the component
cover twice, once for each candidate morphism. On each resulting overlap,
equal families give equal component morphisms by injectivity and
disjointness. Empty overlaps have unique morphisms, so they impose no
artificial equality of labels. Equality then follows from the open covers.

## Descent on arbitrary covers

For any subcanonical Grothendieck topology `J` on `Over S`,
`eq_of_refine_coveringSieve` and `eq_of_refine_cover` detect equality of
natural isomorphism families on a covering sieve or covering family.
To compare two values on an arbitrary test, pull back the covering sieve
to that test. Naturality makes the values agree there; separatedness of
the representable presheaf of `H` gives equality on the original test.

Given a family `E` over `U` that is injective on every test, and a natural
isomorphism family `e` over `T`, suppose a `J`-cover of `T` has morphisms
into `U` classifying the restrictions of `e`. Then
`existsUnique_classify_of_cover` produces a unique morphism `T → U`
classifying `e` on the original test. `classifyOfCover` chooses this morphism,
and `refine_classifyOfCover` records its classification equation.
Injectivity of `E` makes the local morphisms compatible. Subcanonicity
glues them as morphisms into `U`, and the preceding equality-detection
lemma proves the global classification equation.

These descent results retain the chosen topology as a parameter and
require its subcanonicity and the stated covering condition. They apply
to arbitrary relative tests, including nonaffine, disconnected, nonreduced,
and empty schemes. They assert no local existence or reductive-group
classification theorem by themselves.

## Provenance

This is internal categorical infrastructure for the constant
outer-isomorphism chart. It combines the existing all-test `LocalGroupIso`
interface, actual scheme coproducts and representable-sheaf descent. It is
not a separately quoted theorem of the reductive-group literature.

`terminalBasePoint` is the canonical map of a test scheme to the base object; `terminalBasePoint_unique` proves its uniqueness.
