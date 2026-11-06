# Cohomological triviality of finite Galois units

The module proves that the dimension-one norm criterion makes the actual
units representation of every finite Galois extension cohomologically
trivial. The fields lie in arbitrary common `Type u`. No perfectness or
characteristic hypothesis is added.

`HasDimensionLEOne.finite_units_tate_isZero` first proves vanishing in
every Tate degree for the whole Galois group. For each Sylow subgroup,
the proof passes to its fixed field. That field is finite separable over
the base and inherits the norm criterion by the arithmetic bridge.
Finite-relative Hilbert 90 and the norm-to-second-cohomology theorem give
zero first and second ordinary cohomology over that fixed field. The
group-cohomology isomorphism induced by the fixed-field Galois
correspondence identifies these with the restricted units coefficients.
The ordinary-to-Tate comparison transfers the two positive degrees, and
the existing p-group theorem gives vanishing in every integer degree on
the Sylow subgroup. The existing Sylow-detection theorem then gives the
claim for the full Galois group.

`HasDimensionLEOne.finite_units_cohomologicallyTrivial` applies this result
over the fixed field of each arbitrary subgroup. The subgroup is
isomorphic to the Galois group over its fixed field. Reindexing the actual
Tate complex through this isomorphism, with the identity linear
isomorphism on `Additive Lˣ`, transports the result to the restriction of
the original units representation.

This is a derived internal consequence of
[the arithmetic norm bridges](DimensionLEOneArithmetic.md),
[finite-relative Hilbert 90](../ClassFieldTheory/Local/RelativeH1Proof.md),
[the p-group vanishing theorem](../Cohomology/Tate/PGroupTateVanishingProof.md),
[Sylow detection](../Cohomology/Tate/SylowTateVanishingProof.md), and
[Tate reindexing](../Cohomology/Tate/Reindex.md). It packages their actual
cohomology results using
[`IsCohomologicallyTrivial`](../Cohomology/Tate/CohomologicallyTrivial.md).
It does not assert tensor stability, identify torus scheme cocycles with
lattice-valued cohomology, or prove the existence of a Borel subgroup.

Worker 1333 authored this packaging and its proofs. The imported
vanishing and comparison results retain their existing authorship.
