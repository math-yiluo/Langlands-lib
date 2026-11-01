# Arithmetic pullback on continuous rational-invariant functions

Author: Worker 2.

This internal construction precomposes actual complex-valued functions by
`AdelicGLTransport.adelicEquiv n e` for a number-field isomorphism
`e : K ≃+* L`. The fields have independent universes, and the rank is any
natural number, including zero. The map fixes the complex values; it is
complex linear. Rational-matrix covariance proves rational left invariance
of the result. Continuity of the actual group map proves continuity of each
pulled-back function.

`arithmeticComap` maps the existing `ContinuousRationalFunctions L n` into
`ContinuousRationalFunctions K n`. Its identity, contravariant composition
and two inverse identities are proved using the actual arithmetic matrix
identities. `arithmeticEquiv` bundles the resulting continuous complex-linear
equivalence with inverse pullback along `e.symm`. Both directions are
continuous for the existing topologies induced from compact-open continuous
functions, by Mathlib's continuous precomposition theorem. The evaluation
formulas specify the underlying functions in both directions.

The right-translation covariance uses the actual adelic matrix equivalence.
The finite and infinite covariance formulas also use the actual inclusions
of those whole factors.

`centralCharacterEquiv` restricts the map to the actual central-character
spaces. The new character is the arithmetic pullback `HeckeCharacter.comap e χ`.
The scalar-idele covariance and surjectivity of the full group and idele
maps prove both directions of the transformation rule. Its full right-action
covariance is inherited from the ambient calculation.

`levelEquiv` restricts pullback to the fixed-vector submodule for any actual
finite subgroup. The target subgroup is its preimage under `finiteEquiv n e`.
Surjectivity of this group map and injectivity of pullback prove both directions
of fixedness. The underlying homeomorphism preserves and reflects openness
and compactness of the subgroup. Thus `HasFiniteLevel` is preserved and reflected,
with no choice of a new level or existence theorem hidden in the construction.

`infiniteOrbitSpan_arithmeticComap` proves equality of the orbit span for the
preimage infinite subgroup and the linear image of the original orbit span.
The two inclusions use the actual factor covariance and the inverse group map.
`infiniteOrbitEquiv` bundles the resulting continuous linear equivalence, and
`isInfiniteFinite_arithmeticComap_iff` transfers module finiteness through that
equivalence. This is valid for every supplied subgroup; no identification of
the transported subgroup with a standard maximal compact is asserted.

`galoisAut` sends an actual rational field automorphism to inverse arithmetic
pullback on these functions. Contravariant composition gives the left-action
law for the existing composition convention on field automorphisms.
`galoisAction` is an installable distributive action; the module installs no
global action instance. Its evaluation formula uses `adelicAut n (σ⁻¹)`.
The central-character equation transforms by `HeckeCharacter.galoisAut σ`
with this same inverse convention.

For a CM field, `complexConj` is direct pullback by the actual arithmetic
involution. It fixes complex values and is complex linear. Its evaluation
formula uses the existing `CMConjugation.adelicConj`, and its square is the
identity by the field involution and contravariant composition. Restricting
the field involution to rational scalars identifies this operation with
`galoisAut`. Its central character becomes `χ.complexConj`, using the existing
idele-class argument-conjugation convention, and finite level is preserved
and reflected.

For this CM specialization, the actual `standardInfiniteCompact` is its
own preimage under the infinite-factor transport. The proof combines the
existing CM compact-preservation result with the proved involutivity of
the infinite arithmetic map. The general orbit-span result therefore proves
preservation and reflection of finiteness under this actual standard compact
subgroup. This assertion is specific to CM conjugation.

This is transport between ambient continuous rational-invariant spaces.
Preservation of automorphic smoothness, enveloping-center finiteness,
growth, cuspidality or representation occurrence is not asserted. The general
field-isomorphism result does not identify standard compact subgroups.

Provenance is internal composition of the existing actual ambient spaces
and arithmetic matrix-group transport, together with compact-open
precomposition and the existing CM compact-preservation construction.
No new identification with literature is introduced.
