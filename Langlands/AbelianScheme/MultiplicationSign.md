# Inversion and signs in integer multiplication

This internal construction uses the published multiplication maps and isogeny
stability laws. It applies to every commutative group object `G : Grp (Over S)`
over every scheme `S`, without smoothness, properness, or connectedness assumptions.

`multiplicationNegOneIso G` is the automorphism whose forward and inverse maps
are both multiplication by `-1`. The two inverse identities follow from
`multiplication_mul`, since `(-1) * (-1) = 1`, and `multiplication_one`.
On sections, the published `points_multiplication` formula identifies this map
with inversion.

`isIsogeny_of_isIso` uses the forgetful functors to give the underlying scheme
morphism an isomorphism instance. Mathlib then supplies finiteness, flatness,
and surjectivity. In particular, multiplication by `-1` is an isogeny.

`isIsogeny_multiplication_neg_iff` proves that multiplication by `-n` is an
isogeny exactly when multiplication by `n` is one. Composition with the
inversion automorphism proves one direction, using the published composition
law for multiplication and stability of isogenies. Applying that implication
to `-n` proves the other direction.

`isIsogeny_multiplication_of_positive` reduces every nonzero integer to a
positive natural number. For a nonnegative integer, nonzeroness gives strict
positivity. For a negative successor, the sign equivalence reduces the claim
to the positive successor. The hypothesis that every positive multiplication
is an isogeny remains explicit. This module does not prove that geometric
hypothesis for abelian schemes.

The provenance is internal: all claims follow from integer arithmetic,
functoriality of isomorphisms, and the imported published constructions. There
is no additional literature theorem or geometric assertion in this unit.
