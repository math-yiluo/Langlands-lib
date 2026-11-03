# Morphism descent and prescribed isomorphisms for nonaffine models

This proposition targets the relative morphism and essential uniqueness
parts of Brian Conrad, *Weil and Grothendieck approaches to adelic points*
(December 31, 2011), printed pp. 5–6, Theorem 3.4(1),(3).
The factorization and equality clauses retain the weaker individual
hypotheses supported by Mathlib's affine-transition limit theorems.
The extension from ring spectra to arbitrary cofiltered affine base
schemes and an arbitrary fixed scheme is a derived categorical formulation.

All objects share an arbitrary universe `u`. Let `D` be a small cofiltered
diagram of affine schemes, `c` a supplied limit cone, and `t` a compatible
family of maps from its levels to a scheme `S`. Fix `p : c.pt → S` with
`c.πᵢ ≫ tᵢ = p`, and arbitrary scheme models `a : X → S`, `b : Y → S`.
Neither `S`, `X`, nor `Y` is assumed affine. No separatedness is required.

The construction `SchemeLimitModelMaps` supplies actual relative
morphism subtypes `LevelHom` and `LimitHom`, and their actual base change
maps `restrict` and `toLimit`. `ModelMorphismDescent` asserts three claims:

1. If `a` is quasi-compact and quasi-separated and `b` is locally of finite
   presentation, every actual morphism over the limit base equals
   `toLimit i fi` for an actual morphism `fi` over some level.
2. If `a` is quasi-compact and `b` is locally of finite type, two morphisms
   at any two levels with the same limit restriction have equal
   restrictions at some common later level. This clause requires neither
   quasi-separatedness of `a` nor finite presentation of `b`.
3. If both models are quasi-compact, quasi-separated, and locally of
   finite presentation, every prescribed isomorphism between their limit
   base changes, commuting with projection to the limit base, comes from
   an actual level isomorphism commuting with the level projection. Its
   `toLimit` morphism equals the prescribed isomorphism's morphism.

In Mathlib the three conditions in the last clause express finite
presentation. Applying the second clause to the underlying maps of two
such level isomorphisms gives eventual equality, hence their eventual
uniqueness as isomorphisms. The equality is the equality of the actual
restricted maps, not an assumed presentation relation.

For a directed ring system as in Conrad, take the opposite diagram of
spectra and the supplied spectral limit cone. This proposition supplies
the existence and equality criteria for the stated relative Hom-colimit
bijection and descent of a prescribed identification; an explicit adapter
to a chosen set-colimit construction is a separate obligation. It does
not assert the existence of a first model, descent of any of the
properties in Theorem 3.4(2), arithmetic realizations, or topological
model independence. This file defines a proof target and contains no
proof of these three descent assertions.
