# Continuous irreducible representations over a normal subgroup

This internal module supplies two technical pieces for the Clifford theory of
a compact nonarchimedean group: continuity as openness of the kernel, and a
model of coinduction whose carrier lives in the universe of the inducing
representation.

## Continuity

`isContinuous_iff_isOpen_ker`: on a compact nonarchimedean topological group
`G`, a finite-dimensional complex representation (a
`FiniteRepresentation.{0, uG, uV} ℂ G`) is continuous exactly when its kernel
is open. This is the published
`Weil.bundledRepresentationContinuity_iff.mpr Weil.representationContinuity`
(module `Langlands.Weil.Representation.ContinuityBridgeProof`), applied with
the whole group as the open compact subgroup.

## Coinduction with a small carrier

For a subgroup `H` of finite index and a finite-dimensional representation `θ`
of `H` on `V : Type uW`:

- `transportRep e ρ` transports a representation along a linear equivalence
  `e` of carriers, and `transportEquiv e ρ` is the resulting equivalence.
- `coindCoordEquiv H θ` identifies the space of the coinduction
  `θ.coind H.subtype` with `Fin n → V`, `n` the number of right cosets, by the
  Library's coset coordinates `FiniteRepresentation.Induction.coordinates`
  followed by an enumeration of the cosets.
- `coindRep H θ` is the transported coinduction and `coindObj H θ` the
  corresponding `FiniteRepresentation.{0, uG, uW} ℂ G`, with carrier in the
  universe of `V`; `coindObjEquiv H θ` is the equivalence with
  `θ.coind H.subtype`.
- `finrank_coindObj`: `dim (coindObj H θ) = [G : H] * dim V`.
- `ker_coindRep`: the transported representation has the same kernel as the
  coinduction.
