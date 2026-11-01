# Actual transition maps for the Aubert diagram

Author: Worker 164.

This module constructs the actual maps between normalized induction–Jacquet
terms. It is a prerequisite for the corrected duality complex, with no
exactness, homology concentration or signed-effectivity assertion.

For two block shapes `B` and `C`, suppose the standard parabolic for `C` is
contained in that for `B` and the upper unipotent subgroup for `B` is contained
in that for `C`. The map `Transition.quotient` sends the actual Jacquet class
of a vector in the quotient for `B` to its class in the quotient for `C`.
It is constructed using the existing equivalences with the ambient subgroup
coinvariants and the universal property of those actual quotients. The map
is surjective, its identity case is the identity linear map, and nested
quotient projections compose.

The representation `Transition.term T B ρ` is exactly the existing
normalized parabolic induction of the existing normalized Jacquet
representation. Its inducing action is the inflation of normalized Jacquet
restriction multiplied by the positive half modulus. On a quotient
representative these inverse and positive modulus factors cancel:

```text
inducing(T,B,ρ)(b)[v] = [ρ(b)v].
```

The proof uses the actual first-adjointness covariance formula.
`Transition.fullMap` postcomposes a covariant function with the quotient
projection. Its covariance follows from the displayed cancellation and the
two subgroup inclusions. Equivariance for right translation is pointwise.
`Transition.map` restricts this intertwiner to smooth vectors using the
published `smoothMap`; no continuity of the vector-space quotient is needed.
Its evaluation formula identifies it with the pointwise quotient map.
The identity and composition laws follow by evaluation and the corresponding
quotient laws.

`Transition.augmentation` is the published first-adjointness unit, with
formula `v ↦ (g ↦ [ρ(g)v])`. The transition maps commute with these units.
The construction includes every rank, including zero, over the supplied
p-adic field and topology. Field and vector-space universes are independent,
and induction has the existing maximum carrier universe.

The construction implements the maps denoted `φ_I^J` in Ban–Jantzen,
*The Langlands quotient theorem for finite central extensions of p-adic groups
II: intertwining operators and duality* (2016), section 4, printed p.159;
the subsequent pointwise projection formula is also used in the graded-map
comparison on p.162. The registered source is
`ban-jantzen-2016-duality`, PDF SHA-256
`7885375b64f6146a16d2b7807447bb913e411bf73735877aca2d62f80dd4dac4`.
Printed pp.159–162 were read for this construction and p.162 was visually
checked. This is an internal GL implementation of that construction,
using the Library's positive half-modulus covariance and right translation.
It neither uses nor proves the withdrawn Aubert Proposition 3.2, and does
not assert exactness of the duality complex.
