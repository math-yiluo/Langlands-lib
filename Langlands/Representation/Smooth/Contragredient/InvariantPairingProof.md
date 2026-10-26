# Perfectness of an invariant pairing with one admissible side

Author: Worker 166.

`Langlands.smoothInvariantPairingDuality` proves the published proposition
`Langlands.SmoothInvariantPairingDualityStatement` with independent universes
`uG`, `uV`, and `uW`. This is an internal derivation from the Library's smooth
lifting, admissibility, exact contragredient, and admissible bidual results.
It has no external source attribution.

Write `D` for the actual smooth contragredient. Simultaneous invariance of
`b : W →ₗ[ℂ] V →ₗ[ℂ] ℂ` gives a full-dual intertwiner from `σ` to `ρ.dual`.
The calculation applies invariance to `w` and `ρ g⁻¹ v`, matching the
inverse-argument dual action. Smoothness of `σ` lets `smoothLift` restrict
this map to `F : σ → D(ρ)`. The same construction with the transposed
bilinear map and smoothness of the admissible `ρ` gives
`C : ρ → D(σ)`. Evaluation of these maps is respectively `b w v` and
`b w v` with the arguments reversed. The two explicit nondegeneracy
hypotheses imply zero kernels, and linearity then proves both maps injective.

Compact-open cofinality and admissibility of `ρ` make `D(ρ)` admissible by
`isAdmissible_smoothContragredient_of_compact_cofinal`. Admissibility passes
through the injection `F` by `isAdmissible_of_injective`, so `σ` is admissible
without an additional premise. Exact smooth duality, applied to the injection
`C` between smooth representations, makes `D(C) : D(D(σ)) → D(ρ)`
surjective. Admissible bidual reflexivity makes the canonical evaluation map
`σ → D(D(σ))` surjective as well. Evaluation on each `v` shows that their
composition is exactly `F`. Taking successive preimages proves surjectivity
of `F`.

Finally, `Representation.IntertwiningMap.ofBijective` turns `F` into an actual
representation equivalence. Its evaluation identity with the supplied `b` is
definitional. The argument keeps zero carriers and trivial groups and adds no
finite-dimensional ambient space, finite-length, irreducibility, carrier
topology, norm, or second admissibility assumption.

This proof supplies a generic criterion. It constructs no induction or Jacquet
pairing and proves none of their analytic, admissibility, or nondegeneracy
hypotheses. It does not establish induction duality, Jacquet duality, second
adjointness, relative multiplicity comparison, or the irreducible-head
consequence.
