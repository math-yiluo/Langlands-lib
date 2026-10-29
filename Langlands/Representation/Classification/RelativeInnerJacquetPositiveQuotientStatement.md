# Positivity of an inner Jacquet count and inner quotients

`GLRelativeInnerJacquetPositiveQuotientStatement` is a proposition definition.
For every prime, compatible p-adic field and topology, positive rank, ordered
coarse block shape `B` and actual refinement `S`, take an irreducible
Levi-cuspidal representation `ω` of `(B.flatten S).Levi F.Carrier`. The real
vectors `v₀` and `t` are arbitrary. Write
`τ = RelativeJacquetMultiplicity.fineTwist T B S ω v₀ t`.

For every irreducible admissible representation `μ` of `B.Levi F.Carrier`,
and every natural number `m` with a supplied witness
`HasJordanHolderMultiplicity (innerJacquet T B S μ) τ m`, the statement asserts
that `0 < m` if and only if an actual surjective intertwiner
`innerInduced T B S τ → μ` exists. The supplied multiplicity witness includes
an actual finite composition series of the inner Jacquet representation and
counts its factors equivalent to `τ`.

The universes `uF`, `uV` and `uW` are independent and belong to the field, fine
representation and coarse representation, respectively. The inner induced
carrier lies in `max uF uV`; its quotient may have carrier universe `uW`.
No unitarity, relative genericity, chamber condition, support certificate or
constituent assumption is imposed.

The statement uses the published actual functors without changing their
normalization. `innerInduced` is upper normalized refined induction with right
translation and positive half-modulus covariance. `innerJacquet` is normalized
opposite Jacquet on its actual coinvariants, using the positive upper
half-modulus. The fine twist is the real determinant twist with coordinates
`-v₀(k) + t(parent(k))`, transported along the inverse of the actual
`flattenedLeviEquiv`. The absolute value is residue-normalized.

This is an internal derived interface for the positivity clause of the generic
relative comparison. Its intended proof uses the following published inputs.
A positive actual factor count selects a grade equivalent to `τ`. Pulling the
actual series to the flattened product Levi gives an actual cuspidal
subquotient there. `fineTwistIrreducibleAdmissible` supplies irreducibility and
cuspidality of the flattened twist;
`flattenedRefinedOppositeJacquetAdmissibility` supplies admissibility of the
pulled Jacquet representation. Then
`CuspidalSupport.leviCuspidalConstituent_maps` extracts an actual embedding of
that twist into the pulled Jacquet representation, including when their
carrier universes differ. Transport back to the refined subgroup gives a
nonzero intertwiner. Refined normalized second adjointness, as expressed by the
inner clause of `fineOppositeJacquetQuotientDetection`, turns this map into an
actual inner quotient. Conversely, a quotient gives a nonzero Jacquet map by
the same adjointness, and
`SimpleMapMultiplicityDetectionProof.positive_of_simple_map` proves positivity
of the supplied count. The independent-carrier extraction theorem is imported
from `CuspidalSupport.ConstituentUniverse`; the adjointness clauses are proved
by `Parabolic.normalizedSecondAdjointness`.

This rationale describes the intended derivation, not a proof in this file or
a literal transcription of a numbered literature theorem. Existence of a
finite-series count remains a premise. Ambient multiplicity equality,
construction of generic totals, and the irreducible head consequence require
separate results.
