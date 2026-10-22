# Smooth rational adelic functions

For a number field `K : Type u` and any natural rank `n`, this file constructs
subspaces of the actual continuous complex-valued, rational-left-invariant
functions on `GL_n(A_K)`. It uses the published adelic matrix group and its
finite/infinite product decomposition. The coefficient field is the usual
complex field; the infinite smoothness is real `C∞` smoothness.

The construction distinguishes two different finite-place conditions.
`smoothSubrepresentation` requires real smoothness on each infinite slice and
local constancy on each finite slice. In addition to the continuity already
present in the ambient carrier, this is precisely Borel--Jacquet's smoothness
condition in section 4.1. `finiteSmoothSubrepresentation` instead requires one
open subgroup of the finite adelic matrix group to fix the entire function.
Its carrier reuses `Langlands.smoothVectors` applied to the actual finite right
action. No equivalence between these two conditions is asserted.

`infiniteSlice` is the actual restriction `a ↦ f(a,b)` at fixed finite matrix
`b`. The infinite-smooth subspace is the intersection of the inverse images of
the published real-smooth function submodule under these linear restrictions.
Local constancy in every finite slice also defines a complex submodule.
Both submodules are preserved by full adelic right translation: the product
decomposition sends translation by `(g∞,gf)` to translation of the infinite
argument by `g∞` and the finite argument by `gf`. All closure and action
obligations are proved in Lean.

The stronger common-open-stabilizer subspace is also preserved by the full
adelic action. Its fixing subgroup is transported by conjugation by the finite
component. An open stabilizer implies local constancy on each finite slice,
using the open coset `bL`. Consequently the intersection of this subspace with
the infinite-smooth subspace embeds into the slice-wise smooth space.
Both function spaces carry the actual restricted right-translation
representation, with their inherited complex linear structure.

The existing `HasFiniteLevel` predicate requires a compact open subgroup.
Such a level supplies an open stabilizer. Conversely, given an explicitly
supplied compact open subgroup `C`, an open stabilizer `L` can be intersected
with `C` to obtain compact open level. Compactness follows because an open
subgroup is closed. This file does not assume or prove the existence of a
compact open subgroup in the finite adelic matrix group.

The specified-central-character smooth subrepresentation is the intersection
with the published actual idele-class central-character subrepresentation.
These remain ambient function spaces: no compact-type finiteness, finiteness
under the center of the enveloping algebra, growth condition or cuspidality is
silently imposed. In particular, these are not yet automorphic representations.
The distinction in Borel--Jacquet section 4.6 between full group representations
and automorphic Hecke modules remains in force.

## Source and construction correspondence

- A. Borel and H. Jacquet, *Automorphic forms and automorphic representations*,
  Corvallis Part I, section 3.2 and section 4.1, printed p.194
  (one-based PDF page 189), for the product group, right translations, compact
  finite levels, and the slice-wise definition of smoothness.
- Section 4.2, printed pp.194--195 (PDF pages 189--190), for the additional
  automorphic conditions not yet imposed here; sections 4.6--4.7, printed
  pp.196--197 (PDF pages 191--192), for the representation and finite-level
  distinctions.
- Registered literature ID: `borel-jacquet-1979-automorphic`.
- Actual source: `/home/taskhub/central-library/Borel-Casselman--Automorphic Forms, Representations and L-Functions (Corvallis)--1979/Part I.pdf`.
- SHA256: `3b9fe0145da81d870ef8967be83635cd440a2581fe043e64e63324e22dec4db5`.

The intersections, inverse-image submodules, conjugated fixing subgroups and
compact intersection argument are intrinsic constructions, with their proofs
implemented directly. They do not invoke an existence, admissibility,
factorization or classification theorem.

The imported project mathematics is published under
`Langlands.Automorphic.Ambient`, `Langlands.Global.ArchimedeanGL` and
`Langlands.Representation.Smooth.SmoothPart.Definitions`. The finite group
has its actual matrix-units topology over the restricted-product finite adele
ring. Infinite coordinates retain the actual completion topology through the
published multiplicative homeomorphism. No topology on the function space
beyond the already specified ambient realization is needed for these algebraic
subrepresentations.
