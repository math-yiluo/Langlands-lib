# Actual coarse Jacquet extraction and return through refinement

Author: Worker 19.

This internal construction specializes exact smooth image filtrations to every
supplied refinement `S` of an arbitrary coarse positive block shape `B`. It uses
the actual normalized upper Jacquet functors and their published transitivity
comparison, keeping the entire coarse product Levi.

The shared lemmas in [`ExactSmoothSubquotients`](ExactSmoothSubquotients.md)
and [`ShortExactFunctorLaws`](../Derivative/ShortExactFunctorLaws.md) prove
that an exact smooth functor preserves
surjective maps and actual subquotients. Complete a surjective intertwiner by
the actual inclusion of its kernel and apply short exactness. An actual
subquotient has an injective/surjective presentation; map both arrows and apply
the existing actual presentation criterion.

`normalizedRefinedJacquet_mapsShortExact` applies the published exactness of the
actual refined quotient maps to the underlying smooth intertwiners. Its input
objects need no finite length. The zero-map instance is proved on actual
coinvariant representatives. `refinedJacquetImageFiltration` is the resulting
actual invariant-image filtration, with every step and every coarse block
retained. `iteratedCoarseJacquetIso` selects the component of the published
normalized Jacquet transitivity isomorphism.

For an admissible finite-length ambient smooth representation `π`, finite length
implies finite group-algebra generation. The published actual Jacquet length
theorem gives finite length of the coarse Jacquet module. Transitivity carries
an irreducible actual `D` in the composed Jacquet module to the refinement of
this coarse object. Exact-functor extraction supplies an irreducible actual
`E` in the coarse Jacquet module with `D` in its refined Jacquet module.
Conversely any actual `E` in the coarse module and any `D` in its refinement
give `D` in the composed module by preservation of actual subquotients,
transitivity of the occurrence relation, and normalized Jacquet transitivity.

No irreducibility of `π` is needed. Neither the extraction input nor its output
is promoted to a quotient of a whole Jacquet module. The field and carrier
universes remain independent, and the supplied topology and normalization are
unchanged. This construction does not identify the composed Levi with the
standard flattened Levi, factor an irreducible coarse constituent into block
representations, or prove a local rank-three transfer.

## Provenance and dependency audit

This is an internal adapter derived from the existing actual quotient and
finite-length interfaces. It does not reproduce a separately cited assertion
from the rank-three literature. Its direct imports are
`Filtration.ExactSmoothSubquotients`,
`Filtration.ExactConstituentExtraction`, `Filtration.SubquotientAlgebraProof`,
`Classification.FiniteLengthProof`, and
`Parabolic.RefinementJacquetTransitivityProof`, all under
`Langlands.Representation`.

The exact-image and actual-grade helper pairs describe their elementary
quotient, kernel, range, and composition-series arguments. In the generic
transport lemmas here, completing a surjection by its actual kernel produces
the range–kernel equality `Submodule.range_subtype`. The subquotient
presentation criterion in `Classification.SupercuspidalSupport` is proved by
ranges, kernels, and first isomorphism theorems. The imported
`smoothSubquotientTransitivity` pulls an invariant subspace back along the
presentation's surjection, then composes the actual quotient maps. These are
algebraic constructions, with no cuspidal-support assertion.

For refined exactness, the used body is
`CuspidalSupport.RefinedJacquetLengthProof.map_exact`. It identifies the
underlying maps with actual refined-unipotent coinvariant maps. Smoothness of
the middle object, finite compact containment of the refined unipotent, and
the averaging-based coinvariant injection theorem give injectivity. The
coinvariant range–kernel and surjection laws give the other two conclusions.
It has no finite-length hypothesis and does not invoke its module's later
finite-length-detection conclusion. The zero-map instance in this adapter is
checked directly on quotient representatives.

For finite length of the coarse object, the used result is
`Parabolic.normalizedJacquetFiniteLength` in
`Classification.FiniteLengthProof`. Its proof inducts on the semisimple-rank
measure `n - B.length`. Actual normalized Jacquet admissibility is proved
through the stable-image canonical lift and small block Iwahori subgroups;
finite generation is proved from finitely many ambient generators and the
compact parabolic quotient. The rank induction splits the representation
into a quasicuspidal part and a complement without nonzero quasicuspidal
subquotients. The former has finite length by compact-coefficient
semisimplicity on the determinant-unit subgroup and a finite fixed-vector
generating space. The latter has finite length by summing the lengths of its
proper refined Jacquet modules. A strict invariant-subspace inclusion has a
nonzero quotient detected by one such refinement, so the finite sum bounds
all strict chains. Flattened quotient surjectivity and the strictly smaller
refinement measure supply the induction step. These arguments are over the
actual Levi group algebras.

The quasicuspidal splitting just used is the natural compact-coefficient
projector construction, not a decomposition by global supercuspidal supports.
Its proof discharges its analytic inputs by determinant-unit isotypic
complements, finite fixed-level strata, total compactness and exhaustion, and
the Harish-Chandra criterion. That criterion is proved using actual Cartan
support estimates, contraction and averaging, and vanishing of actual proper
refined coinvariants. No ordered quotient coverage or multisegment
classification is used to supply that splitting or the finite-length
argument.

For transitivity, the used body of
`normalizedRefinementJacquetTransitivity` descends the full quotient map
through each of the two radicals and constructs the inverse by the actual
factorization of the full radical. The inverse-half normalizing characters
multiply to the composed inverse half. Checking representatives proves the
equivariant comparison and its naturality. Selecting its object component
introduces no premise.

Recursive traversal of the imports at Library base
`0acb0c6492f21de608601e6283ccd1944725452a`, including this adapter and its two
new extraction helpers, gives 301 project modules. The classification-named
modules are `ConstituentRelations`, `FiniteLengthStatement`,
`FiniteLengthProof`, `Segments`, `Supercuspidal`,
`SupercuspidalContragredientAux`, `SupercuspidalContragredientStatement`,
`SupercuspidalSupport`, and `SupercuspidalTwist`. The latter modules supply
actual definitions, twist transport, duality and elementary presentation
laws; their presence does not provide a classification conclusion. The
proof routes described above contain none of the eight excluded
classification conclusions, their proof successors, general ordered
quotient coverage or full multisegment classification. In particular this
adapter uses no global support decomposition, local length-three
irreducibility, or coarse-constituent uniqueness assertion.

Declaration inspection of
`exists_irreducible_coarseJacquet_subquotient` retains independent `uF,uV`
and reports only `propext`, `Classical.choice`, and `Quot.sound`. This unit
provides ambient extraction and return for a supplied arbitrary refinement;
it does not establish either repeated-factor transfer.
