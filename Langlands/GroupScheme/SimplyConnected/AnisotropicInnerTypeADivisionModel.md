# Anisotropic inner type A and actual division norm-one models

This internal module generalizes the implemented finite-stage pinning route
in `InnerTypeANormOneReduction` and combines it with the published
`CentralSimpleUnits.matrixNormOneSplitRank` theorem. It holds over every field
and in every characteristic, at every universe parameter.

`HasCentralDivisionNormOnePresentation G degree` is a proposition asserting that
there exists a finite-dimensional central division algebra `D` over the base
field, of reduced degree exactly `degree`, together with an actual group-scheme
isomorphism from `G` to its reduced-norm-one group. It requires an actual model,
not merely a Dynkin label, and makes no assertion about a chosen algebra being
canonical.

`normOnePresentation_of_simplyConnected_innerTypeA` constructs a central-simple
norm-one presentation of reduced degree `n + 1` for an affine, locally finite type,
simply connected group equipped with actual Tits-index data satisfying
`HasInnerTypeA n`. This uses the full type-A Cartan matrix and the full absolute
Galois star action. No separate absolute almost-simplicity premise is needed.
The implementation follows the existing reduction: pass the Galois pinning to
a finite stage, use the simply connected coroot span to make its star action
trivial, compare its based root datum with that of the special linear group,
apply the pinned isomorphism theorem, and descend the resulting inner form
with `specialLinearInnerFormNormOne`. The four inputs to that reduction are
all supplied by their published proof theorems.

`CentralSimpleUnits.exists_division_algEquiv_of_splitRank_zero` starts with an
arbitrary finite-dimensional central simple algebra whose actual norm-one
group has split rank zero. Wedderburn--Artin supplies a matrix presentation
`A ≃ M_m(D)` with `m > 0`. Transport of split rank and the published formula
`splitRank SL_m(D) = m - 1` force `m = 1`. The one-by-one matrix algebra
isomorphism then supplies an actual algebra isomorphism `A ≃ D`.

`centralDivisionNormOnePresentation_of_anisotropic_innerTypeA` combines the
two results. Anisotropy is the Library convention `splitRank G = 0`.
The algebra isomorphism preserves reduced degree and induces an actual
isomorphism on reduced-norm-one group schemes, giving a central division
model of reduced degree exactly `n + 1`.

The provenance is an internal generalization and composition of published
constructions. This module does not construct an algebra anti-equivalence from
a relative Weyl symmetry, prove that an arbitrary anisotropic group has inner
type A, or finish the local rank-one Tits-index enumeration.
