# Quotient models with continuous local sections

This internal construction applies to topological spaces `X : Type u` and
`Y : Type v`, with independent universes and no separation assumptions.
`HasContinuousLocalSections f` means that every point of `Y` belongs to an
open subset `U` with a continuous map `s : U → X` satisfying
`f (s z) = z.val`. A single section near each target point suffices; the
sections need not agree on overlaps or pass through every point of a fiber.

Such sections imply surjectivity. If `f` is also continuous, they imply
`IsQuotientMap f`. For the reverse direction of the openness criterion,
suppose `f ⁻¹' W` is open and fix `y ∈ W`. Choose a local section on `U`.
The image in `Y` of `s ⁻¹' (f ⁻¹' W)` is open because the inclusion of `U`
is an open map. It contains `y` and lies in `W` by the section identity.
Thus `W` is open. Continuity of `f` gives the other direction.

Given a setoid `r` on `X`, the construction
`quotientHomeomorphOfLocalSections r f hf hfib hs` assumes continuity,
the exact fiber equivalence `r x x' ↔ f x = f x'`, and continuous local
sections. It descends `f` to the existing carrier `Quotient r`.
The fiber equivalence makes the descended map injective, and the sections
make it surjective. The quotient-map openness criteria for `f` and the
canonical quotient projection identify the two topologies. The formula on
representatives is `⟦x⟧ ↦ f x`.

`compactSpace_quotient_of_local_sections` transports compactness of `Y`
back along that homeomorphism. The source quotient always carries its
canonical coinduced topology. No arbitrary replacement topology is used.

Provenance: this is a derived internal topological construction, proved from
the definitions of local sections, open subspaces, quotient topologies and
equivalences. For the dynamic-parabolic application, existence of an actual
proper quotient scheme, the exact fiber identity, algebraic local sections,
and compactness of its local-field points remain separate obligations.
This module does not prove any of those existence results or the full
dynamic-parabolic compactness target.

Author: Worker 125.
