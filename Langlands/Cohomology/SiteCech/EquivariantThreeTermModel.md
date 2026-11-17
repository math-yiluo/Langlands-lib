# Assembling exact equivariant three-term models

This internal construction works with abelian categories `E` and `D` and a
faithful functor `V : E ⥤ D` preserving zero morphisms. An
`EquivariantThreeTermModel V T` supplies three objects of `E`, two consecutive
arrows, an isomorphism from each image under `V` to the corresponding term of
the ordinary short complex `T`, and both commuting differential squares.
It does not assume that the two lifted arrows form a complex.

`zero` proves that their composite is zero. After applying `V` and composing
with the lower comparison isomorphism, the two squares reduce the composite
to the zero composite in `T`. The lower isomorphism and faithfulness of `V`
reflect this equality. `complex` is the resulting actual short complex of `E`,
and `restrictionIso` uses the supplied term isomorphisms and squares to identify
its image with `T` as a short complex.

If `V` also preserves homology, `exact` reflects exactness of `T`. Its proof
transports ordinary exactness across `restrictionIso` and applies Mathlib's
faithful homology reflection. In particular this applies when `V` preserves
finite limits and finite colimits, by the existing Mathlib instance.

`cochainLift` applies the construction to the segment of a chain complex `P`
in degrees `n+2`, `n+1`, `n`. Its inputs include ordinary exactness at `n+1`
and an actual lifted middle cochain with its specified restriction equation.
Its output is the existing `EquivariantCochainLift`, with the automatically
proved equivariant exactness and both supplied differential squares, so the
existing primitive descent theorem applies to injective coefficients.

The construction is derived from short-complex isomorphisms and faithful
homology reflection; it has no external source. It supplies neither geometric
lifts nor their compatibility, ordinary exactness, or the lifted cochain.
Those remain explicit inputs. It does not prove the analytic comparison.
