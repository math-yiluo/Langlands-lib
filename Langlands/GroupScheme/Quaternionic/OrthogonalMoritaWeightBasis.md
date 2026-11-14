# Multiplicity counts from a supplied orthogonal Morita weight basis

This internal derived helper constructs the repeated basis and cancels the
degree factor in the multiplicity calculation for a supplied
`OrthogonalMoritaComparison`. It assumes an arbitrary field extension `L/K`,
a finite-dimensional division `K`-algebra `D`, a first-kind involution
`sigma`, and a form `q` on `Fin m -> D`.

`OrthogonalMorita.rowBasis` takes any `L`-basis `b` of the split natural row
module `(Fin n ⊕ Fin n) -> L`. It forms `degree` copies of that basis and
pulls them back through the comparison's actual `rowEquiv`. The resulting
basis of `L tensor_K (Fin m -> D)` is indexed by `Fin degree × I`, where
`I` indexes `b`. Under `rowEquiv`, its vector at `(j,i)` is exactly
`Pi.single j (b i)`.

Suppose an actual cocharacter `f` of the original isometry group is given,
and every pulled-back basis vector at `(j,i)` belongs to the actual
extended all-test cocharacter weight space of the integer `w i`.
If `degree > 0` and `finrank K D = degree^2`, then
`weight_card_of_rowBasis` proves, for every integer `c`,

`Nat.card {i : I // w i = c} =
 degree * finrank D (cocharacterWeightSpace q f c)`.

The underlying `cocharacterWeightBasis_card_copies` theorem proves the
same formula for any supplied homogeneous basis with that product index.
It identifies the matching product indices with
`Fin degree × {i : I // w i = c}`, applies the weight-basis count from
`CocharacterWeightBasis`, uses `finrank K D = degree^2`, and cancels the
positive common factor `degree`. This proof works when the set of
matching indices is empty, and weights assigned to different indices may
coincide.

The basis construction uses the supplied Morita row equivalence. It does
not use or prove the comparison's group-action intertwining law. In
particular, the homogeneous-basis hypothesis is an explicit remaining
obligation: it must follow from the actual split eigenvector law and its
cocharacter transport before this helper can be applied to the host
`SpinCoverVectorWeightsStatement`. This module constructs no Morita
comparison, vector characters or split eigenbasis.

The content is derived solely from the existing Morita comparison data,
ordinary product bases, the all-test weight-space dimension count, and
natural-number cancellation; there is no additional literature assertion.
There is no characteristic, infinitude, centrality or nondegeneracy
hypothesis. The base fields and division algebra lie in universe `u`;
the finite split-basis index may lie in any universe.
