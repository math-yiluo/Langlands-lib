# Actual source inducing-representative comparisons

This derived module proves the routine source
normalization comparisons when the actual base inducing representative
is moved within its unitary unramified orbit, and states the remaining
comparison for the actual source integrals.

## Source and fixed data

Waldspurger (2003), registered `waldspurger-2003-plancherel`, SHA256
`4b6a6162cd0b3863703fb2f65d1698f926caf813114917f2084c16e38f2e30f7`,
VI.1, printed pp.295–296 (PDF pp.61–62), defines coherent sections over
actual inducing representatives and their equivalences. VI.3, printed
pp.302–305 (PDF pp.68–71), and VII.2, printed p.319 (PDF p.85), use the
resulting source wave packets and inverse-degree orbit products. The
Lean reindexing adapters and remaining integral target are derived
interfaces for that source independence.

All declarations are in
`Langlands.HarishChandraSchwartz.RationalSemistandard.SourceRepresentativeComparison`.
They retain an arbitrary nonarchimedean local field, an affine locally
finite type connected reductive ambient group, an intrinsic
semistandard triple, its actual Levi model, genuine cocharacter
presentation and actual compact picture. Field and representation
carrier universes are independent, including nonsplit groups and
positive characteristic.

The central quotient is the actual literal Levi modulo
`model.splitCenter a`, for a supplied algebraic split component `a`.
Its Borel measurable space and inverse-invariant Haar are fixed.
The scheme-point image also retains normality, and the actual
valuation-image finite-index premise is displayed for source integrals.

## Proved representative comparisons

For a fixed `OrbitClass O`, the first inducing object is the existing
`orbitRepresentative model a ha mu O`. The second is any actual
irreducible admissible `pi'`, with square-integrability and the exact
statement that its class represents `O`. The comparison is the existing
`orbitSmoothSectionsBaseEquiv`. It reindexes by actual unchanged
inducing objects through `unitaryOrbitRepresentativeBaseEquiv`; no
linear comparison map is supplied by the caller.

* `degree_recentered` identifies the actual
  `representationFormalDegree` of the two base objects on the same
  central quotient and Haar. It composes the two evaluations of the
  already constructed `SourceDegree.orbitDegree`.
* `coefficient_recentered` identifies `SourcePacket.coefficientMap` at
  every actual inducing representative before and after reindexing.
* `pairing_recentered` does the same for `SourceForm.pairing`, including
  the canonical inverse-formal-degree normalization in both arguments.

The latter two proofs evaluate at the displayed representatives using
the existing representative-evaluation theorems. The remaining maps,
section values and square-integrability proof inputs agree by
reduction and proof irrelevance. Thus these assertions preserve actual
coefficient values and all coherent smooth data already provided by
the published section equivalence.

## Exact remaining integral target

`RepresentativeSourceComparisonStatement` is an **unproved Prop-valued
target**. It fixes a maximal split torus, generic cocharacter, and
actual compact with the existing
`BruhatTits.SpecialCompact.SpecialCompactProperties`; the coefficient
compact and both scalar compacts equal this same compact.

For every orbit `O`, every actual `pi'` representing that orbit, and
both sets of primitive `OrbitPacketData`, it concludes:

1. equality, as actual functions on ambient rational points, between
   the source packet before reindexing and the packet of the reindexed
   smooth section;
2. equality of `SourceForm.weightedOrbitForm` on every two sections
   before and after that reindexing.

These are the actual prescribed density-weighted integrals against
`SourceMeasure.normalizedOrbitMeasure`; they retain its I.1 scale and
reciprocal unramified self-twist factor. No arbitrary integral,
measure or output comparison is taken as data. Each `OrbitPacketData`
retains the existing reflection and central-split-character statements,
actual compact and its two factorizations, forward/reverse continuations
and their open nonempty full-domain-contained regions, generic
irreducibility region and full-unitary inverse regularity. None of
these preceding obligations is proved by this target.

The target isolates the remaining density/source-measure transport
through a change of base representative. The elementary coefficient,
pairing and degree comparisons above are already proved. It asserts
no unscaled comparison across different compact pictures, no general
model transport, no new standard Schwartz estimate, and no averaging
or synthesis factorization law. Those comparisons keep their
prerequisites (the normalized Weyl/intertwiner comparisons of V.3, the
standard-Levi Plancherel wave-packet Schwartz statements and the
semistandard spectral families) and the separate constructions of the
invariant spectral families.
