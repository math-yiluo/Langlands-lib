# Spectral presentations attached to actual cuspidal classes

This internal construction attaches supplied unramified spectra to the actual
cuspidal operator realizations of `CuspidalOperatorRealization`. It retains a
number field `F : Type uF`, complex coefficients, the explicit compactness
assumption on the additive adele quotient, and positive rank `r + 1`. The
local-factor carrier universe `uV` is independent of `uF`.

`CuspidalSpectralPresentation S` stores a nonzero subspace invariant under the finite adelic group
inside the finite form image of `S`, a family of actual bundled smooth local
representations, reference vectors fixed by the local integral subgroup away
from a finite tensor exceptional set, and a genuine finite tensor presentation
onto that selected subspace. The presentation includes nonzero reference
vectors outside that exceptional set and an equivariant linear equivalence
onto the actual form subspace. Here finite refers to the finite adelic action;
no finite-dimensionality of the selected subspace is required.

It also stores a finite spectral exceptional set and the existing
`FiniteTensorPresentation.UnramifiedData`. Thus the tensor exceptional set is
contained in the spectral exceptional set, the factors are irreducible and
admissible away from the latter, and the supplied eigenvalue multisets satisfy
the normalized spherical Hecke equations on the entire fixed space of the
actual local component. All these are genuine input data and evidence; their
existence for arbitrary cuspidal objects is not assumed or proved.

The exported numerical `spectralSystem` is precisely the system of this
unramified data. The component construction reuses the nonzero complementary
tensor vector supplied by the existing presentation construction. Each local
component is an actual nonzero embedded form subspace. Its cuspidality follows
by containment in the selected finite slice, then in the cuspidal realization.
The `hasSpectrum` theorem retains the whole-fixed-space scalar equations,
without introducing any new normalization.

For a full-operator equivalence `e : S.Equivalence T`, the finite slice is
transported to its actual image in `T`. Composing its finite representation
equivalence with the original tensor equivalence gives
`transportedPresentation`. The factor family, reference vectors, and
exceptional sets remain unchanged. Existing same-family transport of actual
unramified data then defines `transport`. Its spectral system is
definitionally the original one. The actual local components have equal
smooth classes by the existing comparison of presentations with identical
tensor data. The target is cuspidal by containment in the target's own cusp
image, not by identifying constant terms of arbitrary equivalent embeddings.

`CuspidalOperatorRealization.IsoClass.HasSpectralSystem c s` is a Prop-valued
existential relation: an actual representative of `c` has a complete
presentation with numerical system `s`. The representative theorem proves
that this relation holds exactly when such a presentation can be supplied on
any specified actual representative of `c`. Its forward proof extracts a
full equivalence from equality of classes and transports the witness; the
reverse proof uses the specified representative itself. The factor universe
remains explicit in this relation.

The presentation and the class relation allow enlarging the finite exceptional
set by restriction of the supplied data. `PositiveRankCuspidalClass` has the
corresponding relation with its retained rank, and fixed-rank insertion
recovers the fixed-rank relation definitionally.

The provenance is internal composition of actual subspace, tensor,
unramified-data, and quotient constructions. There is no new identification
with original literature. This module proves representative-independent
existence for a *supplied class-system pair*. It does not prove that a class
has any presentation, that different slices or different factor families
give the same spectrum, or that spectra determine the cuspidal class. Finite
factorization, spectral existence and uniqueness, full automorphic-category
exhaustion, and realized isobaric constructions remain separate obligations.
