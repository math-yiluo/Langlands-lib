# Exactness of character-equivariant functionals

This internal adapter concerns the actual `Whittaker.functionals U θ ρ`: the
algebraic linear functionals satisfying `ℓ(ρ(u)v) = θ(u)ℓ(v)`. It reuses the
published character-localization quotient and its exactness theorem. It does
not postulate exactness or change the functional space.

The existing `functionalsComap (N := U) (θ := θ) f` from `Whittaker.Transport`
is the linear map given by precomposition with an intertwiner `f`.
`functionalsComap_injective` shows that a surjective intertwiner induces an
injective pullback.
`functionalsLocalizationDualEquiv_natural` proves compatibility with the
published equivalence between these functionals and the algebraic dual of the
character-localized quotient, by evaluation on quotient classes.

The algebraic part works over any field and keeps the group and all three
representation-carrier universes independent. For intertwiners `i : ρ → σ` and
`p : σ → τ`, with `p` surjective and `range i = ker p`,
`functionalsComap_range_eq_ker` proves the middle exactness of the reversed
sequence. A functional on `σ` that vanishes on `range i` factors through `p`;
surjectivity of `p` then proves character equivariance of the descended
functional. This uses Mathlib's description of the range of a dual map as the
annihilator of its kernel. No topology is needed for this part.

For complex representations of a topological group, assume `U` is a limit of
compact subgroups in the Library's sense, the scalar-valued character `θ` is
locally constant, and `σ` is smooth. Then
`functionalsComap_surjective_of_smooth` proves that every equivariant
functional on `ρ` extends along an injective intertwiner `i : ρ → σ`.
The proof applies the published
`Jacquet.Localization.map_injective_of_smooth` with the trivial acting
subgroup, dualizes that injection using
`LinearMap.dualMap_surjective_of_injective`, and transports the resulting
extension through `functionalsLocalizationDualEquiv`.

The extension is purely algebraic on representation carriers; no continuity
of linear functionals, admissibility, finite dimension, or finite length is
assumed. Together the three exactness conclusions give the reversed short
exact sequence of functional spaces when their stated hypotheses all hold.
This module supplies the adapter needed to count Whittaker constituents later;
it does not prove a constituent classification or a multiplicity assertion.
Its provenance is internal derivation from the published Library and Mathlib
results named above, with all maps and equalities implemented explicitly.
