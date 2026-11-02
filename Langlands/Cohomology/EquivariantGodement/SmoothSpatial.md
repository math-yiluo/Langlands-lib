# Smooth compact spatial maps for the full equivariant Godement complex

This is an internal construction from the actual spatial maps in
`EquivariantGodement/Spatial.lean`, the degreewise smooth-part functor and its
inclusion in `DivisibleSystem/ScalarExtension.lean`, and the existing smooth
section and homology constructions in `EquivariantSections.lean`. It restricts
the constructed proper compact Godement maps to smooth vectors and proves
their functoriality and their compatibility with the original inclusions.
Its provenance is these constructions and their proved laws; it asserts no
additional theorem from the literature.

The ring, group, spaces and module carriers share universe `u`. The group is
a topological group, the coefficient ring is commutative, and the individual
group translations on each space are continuous. Let `f : X → Y` be continuous
and equivariant, and suppose `hp : IsProperMap f`. The source category is the
full category of ordinary topological equivariant sheaves of modules. No
smoothness of the input sheaf or stable-neighbourhood condition is required.

Write `K_X(F)` for the compact-section complex of the full Godement complex of
`F`. Each term of its smooth part consists of pairs of an actual compact
section and a proof that an open subgroup fixes that section.
`smoothCompactComplexMap f hf hp` is the natural chain map

`K_Y(f_*F)^sm → K_X(F)^sm`

in the existing smooth representation category. It applies the existing
`smoothPartComplex` to `compactComplexMap f hf hp`; it constructs no new
resolution. The existing `smoothCompactComplex` functor is definitionally
this degreewise smooth part. `smoothCompactRepComplexMap` forgets the
smoothness witnesses and is a map of the existing smooth compact-section
complexes in algebraic representations.

`smoothCompactComplexMap_apply` specifies every degree. For a smooth compact
section `s`, remove first its smoothness proof and then its compactness proof.
The resulting global section is sent by the component at the top open of
`(Godement.Spatial.complexMap f hf F).f n`. The resulting section has the
compactness and smoothness proofs furnished by proper pullback and restriction
of an intertwiner. `smoothCompactComplexMap_apply_zero` identifies the degree-zero
map with `Godement.Spatial.zeroMap f hf F`: a stalk family is pulled back by
`x ↦ stalkMap f hf F.obj x (s (f x))`. This is a formula for a term of the
complex, with no identification of degree-zero homology needed.

`smoothCompactComplexMap_inclusion_square` states that inclusion of smooth
vectors in all compact sections commutes with the constructed spatial map.
Its proof is the naturality of the existing `smoothPartComplexInclusion`.
`smoothCompactComplexMap_inclusion_triangle` further forgets compact support
and obtains the constructed `globalComplexMap`. The chain maps for the identity
spatial map are identities, and those for `g ∘ f` are the map for `g` on
`f_*F` followed by the map for `f` on `F`. These are
`smoothCompactComplexMap_id` and `smoothCompactComplexMap_comp`; their
counterparts for `smoothCompactRepComplexMap` state the same equations after
forgetting smoothness.

`smoothCompactCohomologyMap f hf hp q` takes degree `q` homology of the
underlying algebraic-representation chain map and bundles the resulting
intertwiner in the full smooth representation category. Its objects are the
existing `smoothCompactCohomology` objects: homology of the smooth
compact-section complexes with the proved smoothness of their actions.
Naturality follows from chain naturality and functoriality of homology,
using the faithful inclusion of smooth representations. The identity and
contravariant composition laws follow in the same way from the proved chain
laws. They are recorded as `smoothCompactCohomologyMap_id` and
`smoothCompactCohomologyMap_comp`.

`smoothCompactCohomologyMap_inclusion_square` states that the underlying map
commutes with `forgetSmooth` into compact Godement cohomology.
`smoothCompactCohomologyMap_inclusion_triangle` further composes with
`forgetSupport` into global Godement cohomology. The first equation is homology
of the actual chain square, and the second uses the proved compact
cohomology triangle.

The construction uses smooth compact sections of the **full** Godement
resolution of arbitrary equivariant sheaves. The separately constructed
Godement resolution in the smooth sheaf category remains a distinct object.
No exactness of the smooth-part functor, commutation of smooth part with
homology, comparison with that smooth resolution, acyclicity, or
derived-functor identification is asserted here. Analytic or étale
realization and arithmetic or Harris specialization remain separate
obligations.
