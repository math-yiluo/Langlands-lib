# Canonical effective expansions of full relative local restrictions

This derived construction applies the published canonical effective unitary
expansion to the full local restriction of an actual relative Weil
representation. It supplies a constructor of the existing
`RelativeGlobal.WitnessedGenerator` that fills its Weil coefficient,
nonnegativity and exact-expansion fields automatically.

## Inputs and universes

Let `F` and `E` be number fields in universe `uF`, with the supplied algebra and
Galois instances, `c` an actual fundamental-class family, and `v` a finite place
of `F`. The relative Weil group, local p-adic field, local Weil group and their
topologies are the existing actual constructions.

`localUnitaryExpansion` takes an actual finite-dimensional complex
representation `S` of that relative Weil group, its continuity and unitarity
proofs, and a supplied continuous local homomorphism `ι`. Unitarity means an
invariant positive definite Hermitian form. Continuity uses the usual
finite-dimensional complex endomorphism topology. The carrier universe `uW`
is independent of `uF`.

The general local constructor requires neither irreducibility nor positive
rank of `S` or of its local restriction. It does not need an automorphic object
or a characterization of the supplied continuous map.

## Construction and intrinsic laws

The published `RelativeWeilGroup.localComponent` restricts `S` along `ι` on
the original carrier. Its published continuity theorem and
`FiniteRepresentation.isUnitary_restrict` supply the hypotheses of
`LocalWeil.effectiveUnitaryExpansion`. This returns an element of the additive
submonoid of coefficientwise nonnegative integer functions on the genuine
local unitary irreducible basis.

`localUnitaryExpansion_spec` identifies its full exact realization after
unitary-basis inclusion with the existing `RelativeGlobal.localExactClass`.
Thus it recovers the entire restricted representation, including all
multiplicities. `localUnitaryExpansion_degree` is the original representation's
carrier dimension, cast to the integers, because restriction keeps that carrier.
These are direct applications of the published full-class and degree laws.

`localUnitaryExpansion_eq_of_expansion` applies the published left inverse of
exact realization after unitary inclusion. Every supplied expansion of this
same full exact class therefore has the constructed coefficients, even if the
supplied expansion has no nonnegativity proof.
`localUnitaryExpansion_eq_of_equiv` restricts an actual invertible intertwiner
and applies the published isomorphism invariance of the canonical effective
expansion. This compares objects in the same carrier universe and at the same
supplied local map. It makes no comparison between different local maps.

## Existing witnessed generators

With the existing compactness instance for the additive adele quotient,
`WitnessedGenerator.ofUnitarySupport` accepts an actual irreducible unitary
relative Weil representation, an actual full cuspidal realization, its
spectral presentation, and their genuine weak association. It also accepts a
place above `v`, a reciprocity candidate, the continuous local map with its
`IsLocalRelativeWeilMap` proof, and local irreducibility and admissibility for
the embedded automorphic component.

The automorphic coefficient element and its actual
`PadicSupercuspidal.IsUnitaryLatticeSupport` witness remain supplied inputs.
They retain genuine normalized-induction subquotient data and multiplicities.
The constructor copies all these data into the reviewed `WitnessedGenerator`
and fills precisely its three Weil expansion fields by `localUnitaryExpansion`,
its submonoid membership proof and its full exact-expansion theorem. Continuity
of the global representation comes from weak association. The existing degree,
paired-span membership and projection laws then apply to this same record.

`WitnessedGenerator.weilElement_eq_localUnitaryExpansion` proves that every
existing witnessed generator already has these canonical Weil coefficients,
by the preceding uniqueness law. It does not identify different automorphic
support witnesses.

The spectral presentation's model factors have independent universe `uP`.
The automorphic local component and support carriers use `uF`, the universe of
the actual form space. No carrier resizing, topology or finite-dimensionality
hypothesis is imposed on those smooth automorphic factors.

## Provenance and scope

Henniart, *Une preuve simple des conjectures de Langlands pour GL(n) sur un corps
p-adique* (2000), sections 2.4–2.5, printed pages 445–446 (PDF pages 7–8),
observes unitarity of the full local restriction of a unitary global Weil
representation and uses its entire local class for the Weil generator map.
The registered source is `henniart-2000-simple-proof`, SHA256
`be283c3e8187f1eed365537c72379c3e06e7791756954c2ac783c6beea2979de`.
The canonical coefficient packaging and constructor in this module are internal
derived content, using the published exact Jordan–Hölder coefficient inverse
and effective unitary expansion proof.

This module works at a fixed finite relative level. It does not construct a
fundamental-class family, continuous local map, global representation,
automorphic object, associated pair or automorphic unitary support. It does
construct the full effective Weil expansion from the supplied continuous
unitary representation and map; no Weil expansion witness is requested.
Absolute global comparisons, local-map independence, automorphic support
existence or uniqueness, lattice isometry, ambient spanning and correspondence
existence remain separate obligations. In particular, this does not complete
the absolute-global scope of Henniart's section 2.5.
