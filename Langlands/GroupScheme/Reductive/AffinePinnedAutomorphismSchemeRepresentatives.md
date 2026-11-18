# Pinned automorphism representatives from representation-free classification

This internal conditional reduction supplies a full automorphism representative
for each supplied `AffinePinnedModel M`, with smooth separated structure
morphism. It assumes relative full-centre quotient existence and a
representation-free constant-family classification on the actual identity
pullback `M.groupOver (𝟙 M.base)`.

The classification hypothesis provides, for every supplied reductive full-centre
quotient of that pullback, a type `D`, a natural local self-isomorphism family on
`constantParameter M.base D`, and a bijective inverse-inner-twist decomposition
on every relative scheme test. No automorphism representative is an input to
this hypothesis. The type of labels can be infinite.

The proof pulls the reductivity of `M.group` along the identity map and uses
`ReductiveRelativeAdjointQuotientExistenceStatement.of_affine` to choose an
actual quotient with reductive target `A`. The target is smooth and affine.
`GroupIsomorphismScheme.ofNormalizedFamily` applied to the supplied
classification data therefore gives a smooth separated representative for the
self-isomorphisms of the identity pullback.

Finally, `baseChangeIdIso M.group` identifies that pullback with `M.group`.
The existing source-precomposition and target-postcomposition constructions
transport the representative through this isomorphism. They retain its actual
parameter, so its smoothness and separatedness are unchanged.

The provenance is the existing relative adjoint quotient conversion, the
normalized-family representative and its product geometry, and the existing
parameter-preserving transport interfaces. The theorem does not prove the
classification hypothesis or the adjoint-existence hypothesis, and it performs
no global descent.

`affinePinnedAutomorphismRepresentatives_of_pinnedLabelCompleteness` supplies
the preceding classification premise using `AffinePinnedModel.constantPinnedFamily`
for `M` compared with itself, with both base maps the identity. Its orbit
bijection is the existing
`AffinePinnedModel.constantPinnedFamily_orbit_bijective`. This specialization
keeps four inputs explicit: the affine pinned isomorphism theorem, relative
adjoint quotient existence, fppf local pinned normalization, and open label
completeness for each model compared with itself. The last input only concerns
concretely pinned comparisons and assumes no automorphism representative.

`affinePinnedAutomorphismRepresentatives_of_pinnedClassification` reduces the
remaining inputs to the exact affine pinned isomorphism theorem alone. It
supplies open self-label completeness using
`AffinePinnedModel.openPinnedLabelCompleteness`, which applies the existing
local full-lattice label theorem under that same affine hypothesis. It supplies
local normalization using the published
`AffinePinnedModel.hasFppfLocalPinnedRepresentatives` and adjoint quotient
existence using the published `relativeAdjointQuotientExistence`.
These are the independently proved local-label, normalization and quotient
results; this specialization introduces no new classification argument.

`affinePinnedAutomorphismSchemeOfPinnedClassification` chooses the full
representative for a supplied model from the resulting existence theorem.
Its subtype retains proofs of smoothness and separatedness. The exact affine
pinned isomorphism theorem remains an explicit input, so this constructor is
conditional and does not establish the task's global target by itself.

The module is named `AffinePinnedAutomorphismSchemeRepresentatives` to keep its
full scheme construction alongside the existing
`AffinePinnedAutomorphismRepresentatives` module, whose representatives are
individual pinned group automorphisms. The latter module's public definitions
are reused unchanged.
