# Top homology of the reversed dual of a punctual complex

Author: Worker 1015.

For a commutative ring `R : Type u`, an integer `g`, and a cochain
complex `L` of `R`-modules supported in degrees at least zero,
`reversedDualTopHomologyIsoCokernel` constructs

```
(reversedDual g L).homology g ≅
  cokernel (ModuleCat.ofHom (L.d 0 1).hom.dualMap).
```

The reversed dual is supported in degrees at most `g`, so its outgoing
differential at `g` is zero. Mathlib's `isoHomologyι` identifies its
homology there with the opcycles, and `opcyclesIsoCokernel` identifies
the opcycles with the cokernel of the incoming differential.
The degree-`g` and degree-`g-1` terms are duals of `L.X 0` and
`L.X 1`, respectively. The implementation uses the duals of
`L.XIsoOfEq` to transport these index equalities. Naturality of the
differential gives a commuting square of isomorphisms and hence the
displayed cokernel isomorphism. No boundedness above, finite generation,
freeness, or local-ring hypothesis is needed for this construction.

For a local ring, a chosen equivalence `e₀ : L.X 0 ≃ₗ[R] R`, and an
equality `firstDifferentialOrderIdeal L e₀ = maximalIdeal R`,
`reversedDualTopHomologyIsoResidueField` composes the displayed
isomorphism with `firstDifferentialDualCokernelIsoResidueField`.
Its target is the actual `ResidueField R` as an `R`-module.

`punctualModelReversedDualTopHomologyIsoResidueField` specializes to a
noetherian local ring and a `PunctualMinimalModel R g K`. It assumes
that degree-zero homology of `K` after extension to each first-order
quotient `R/J`, with `m² ≤ J ⋖ m`, is not isomorphic to `R/J`.
The model's homotopy equivalence transports this hypothesis to its
complex. Its minimality puts the first differential in `m`, and its
finite freeness supplies freeness in degree one.
`firstDifferentialOrderIdeal_eq_maximal` then identifies the order
ideal with `m`, yielding the residue-field isomorphism. The construction
also applies when `g = 0`; it makes no positive-dimension assumption.

This is internal supporting algebra using the existing reversed-dual,
minimal-model, first-differential, and dual-cokernel constructions.
It proves no vanishing in other degrees and does not assert the
punctual-complex proposition or regular-local finite-length acyclicity.
