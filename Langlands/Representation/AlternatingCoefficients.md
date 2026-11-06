# Postcomposition on alternating maps

This internal construction uses a field `k`, a group `G`, a `k`-module `M`,
and coefficient modules `V` and `W`, in five independent universes. The
representation `AlternatingCoefficients.action ρ q` acts on the actual
alternating maps from `Fin q → M` to `V` by postcomposition:
`(g · f)(x) = ρ g (f x)`. The action laws follow pointwise from those of `ρ`.
The group acts only on the values; there is no action on the arguments.

`map A q` postcomposes with an existing coefficient intertwiner `A`.
Its equivariance is the original coefficient equivariance evaluated at each
tuple. The pointwise formulas are definitional equalities.

If `M` is finite dimensional, `G` has a topology, and `ρ` is smooth in the
existing open-subgroup sense, `isSmooth` proves that `action ρ q` is smooth
for every natural degree, including zero. Choose a finite basis of `M`.
There are finitely many tuples of basis indices. Smoothness supplies an open
subgroup fixing each corresponding value of `f`; their finite intersection
fixes all these values. Mathlib's `Module.Basis.ext_alternating` then proves
that it fixes the whole alternating map. The argument allows a zero-dimensional
domain and requires neither a topology on the modules nor a dimension bound
on the coefficient module.

The provenance is internal linear algebra and the already defined notion of
smoothness, using Mathlib's actual alternating maps and finite basis. No new
identification with an external source is claimed. This module constructs no
differential, cohomology, automorphic occurrence, or finite-dimensionality of
the alternating-map space.
