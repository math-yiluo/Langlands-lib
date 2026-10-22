# Finite unramified stages after base extension

`UnramifiedBaseChangeStageExistence` is a proposition. This module states it
and does not prove it.

Fix a prime `p`, finite extensions `F` and `E` of the specified `Q_p`, and
a compatible finite extension `E/F`. Fix also the algebra structure
`Fbar → Ebar` whose composite with `F → Fbar` agrees with
`F → E → Ebar`. Here both closures are the existing `AlgebraicClosure`
types. The statement applies to every such specified map, in arbitrary
common carrier universe `u`. The extension `E/F` need not be Galois.

Let `L` be an actual finite intermediate field of `Fbar/F`, with its
`FiniteIntermediateExtension` finiteness certificate. Assume `L/F` is
Galois and that the canonical absolute ramification indices of `F` and
`L.asPadicField` agree. The conclusion supplies an actual finite
intermediate field `M` of `Ebar/E` such that:

- `M/E` is Galois.
- The canonical absolute ramification indices of `E` and `M.asPadicField`
  agree.
- For every element `a` of `L`, its image under
  `L → Fbar → Ebar` belongs to `M`.

The `asPadicField` wrappers retain the field operations of the intermediate
fields and use the composite scalar maps from `Q_p`. The index equalities
are the project's canonical unramifiedness convention, not equalities of
indices computed from unrelated valuation structures. Finiteness of both
stages is part of their packages. Degree-one source or base extensions are
included.

The containment refers to the same specified closure map as in the
absolute restriction map. It therefore supports constructing an induced
map `L → M` whose composite into `Ebar` is the prescribed map on `L`.
That construction and its algebra and scalar-tower instances are not
provided by this statement module. The proposition does not require `M/F`
to be normal, specify the degree of `M/E`, or assert that `M` is the
smallest possible overfield.

## Provenance

This is a derived p-adic specialization of the unramified-extension
classification in Jean-Pierre Serre, *Local Fields*, translated by
Marvin Jay Greenberg, Springer, 1979, Chapter III, section 5, Theorems 2
and 3 and their corollaries, printed pages 54–55 (PDF pages 61–62).
The retained original is registered as `serre-1979-local-fields`.

Theorem 2 constructs unramified extensions from finite separable residue
extensions and identifies when they are Galois. Theorem 3 identifies
embeddings of an unramified extension into a finite extension with the
corresponding residue-field embeddings. For the present specialization,
one can take a finite residue extension of `E` containing the required
residue image of `L`, lift it to an unramified extension, and use this
embedding correspondence. Finite residue fields make this lift Galois.
Normality of `L/F` identifies the image of any resulting `F`-embedding
with its specified image in `Ebar`. Realizing these extensions in the
given closures and comparing the canonical index convention remain
formal proof obligations.

Serre does not state this exact specified-closure containment proposition
on those pages. The proposition isolates the derived arithmetic input
needed to compare finite representatives under absolute restriction.
It asserts no norm identity, cohomology identity, or absolute invariant
existence theorem.

Authored by Worker 154.
