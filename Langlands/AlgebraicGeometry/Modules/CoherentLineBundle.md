# Local finiteness of affine sections and tensoring by line bundles

For an actual scheme-module sheaf `M`, `HasLocallyFiniteSections M` means that
each point lies in an affine open `U` for which the actual section module
`Γ(M, U)` is finitely generated over `Γ(X, U)`. No quasi-coherence is part of
this definition.

Restriction along an open immersion preserves `HasFiniteAffineSections`.
Conversely, finite affine sections of a restriction give finite sections on
affine opens contained in the image. These assertions use the actual
semilinear section isomorphisms of open restriction. Finiteness on arbitrary
open neighborhoods can therefore be refined to affine neighborhoods.

For a quasi-coherent module, the local condition is equivalent to
`HasFiniteAffineSections`: the forward implication is
`HasLocallyFiniteSections.finiteAffineSections`, and the reverse is
`of_finiteAffineSections`. The implemented proof first identifies section
restriction from an affine `U` to `D(f)` as localization of modules away
from `f`, using the two extension and annihilation properties in
`QuasicoherentLocal.IsLocalizingAt`. Finite generation ascends to each such
localization and descends from any family whose functions span the unit
ideal. Given an arbitrary affine `U` and a point of it, a finite affine
neighborhood `V` supplies a common basic open of both `U` and `V`. These
common basic opens cover `U`; their functions span the unit ideal, giving
finite generation of `Γ(M, U)`.

For `M` quasi-coherent and `N` locally free of rank one in the actual
`Picard.IsLocallyFreeRankOne` sense, `tensorObj M N` is quasi-coherent.
If `M` also has finite affine sections, so does this tensor product.
The local comparison `tensorRestrictionTrivialization` composes the
inverse of the proved tensor-restriction comparison with a trivialization
of `N` and the tensor right unitor. Thus the tensor restricts to `M` on each
trivializing open. Quasi-coherence follows by sheaf locality; finite affine
sections follow by the local condition above. No noetherian, separated,
proper, or dimension hypothesis is needed.

This is internal infrastructure for coherent support induction. It derives
from the published restriction, quasi-coherence, and sheaf tensor APIs,
Mathlib's localization and finite-generation descent theorems, and the
`CoherentClosure` interface. It does not assert an Euler polynomial,
generic devissage, or ample positivity.
