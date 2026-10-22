# Smooth Jacquet quotients and generic character twists

This development extends the actual quotient action in `Coinvariants.lean`.
It is a generic character-parameter construction: an arbitrary homomorphism
`chi : M -> Rˣ` scales the descended action. It does not by itself identify
`chi` with a modulus character.

The carrier is the actual quotient by the span of `rho(n)v - v`. Its twisted
action sends `[v]` to `chi(m) [rho(m)v]`. The canonical quotient map is an
intertwiner from the equally twisted restriction of `rho` to `M`. Its
underlying linear map is the usual surjective quotient map. An ambient
intertwiner induces the usual quotient map between the twisted actions.
Naturality is checked on vectors. Identity and composition are checked after
precomposition with the quotient map, using Mathlib's quotient extensionality.
These checks reduce to definitional equality because twisting keeps the
underlying linear maps.

With a topology on `G`, both subgroups use their induced topologies. Restricting
a smooth representation along the continuous subtype inclusion gives a smooth
`M` representation. Surjectivity of the equivariant quotient map then gives
smoothness of the descended action. If the character has open kernel,
intersecting each fixing open subgroup with this kernel proves that the
twisted action remains smooth. The implementation reuses the accepted
pullback, surjective-intertwiner and open-kernel twist results.

All coefficient and carrier assumptions are explicit: a commutative coefficient
ring, a group, and arbitrary modules in independent universes. The carrier has
no topology. Continuity of the group operations, finite dimension, compactness
and admissibility are unnecessary for these constructions and certificates.

This is derived infrastructure for the Jacquet construction in
Bernstein--Zelevinsky (1977), Section 1.8(b), printed pages 444--445, and
Casselman, Chapter III (April 29, 2019), Section 3, pages 3--4.
The normalized specialization will use the inverse positive half-modulus,
not the arbitrary character in this file. Exactness and reciprocity require
separate results.

The original source tuples are:

- `bernstein-zelevinsky-1977-induced-i`, SHA256
  `8424600228ab72c5937e45edceefcae410a2a0b8f5ebf282185691542aa89092`,
  Section 1.8(b), printed pages 444--445 / PDF pages 5--6. Original:
  `C:/Central-Library/Bernstein-Zelevinsky--Induced representations of reductive p-adic groups I--1977.pdf`.
- `casselman-2019-jacquet-module`, SHA256
  `377edac998669bc88da1224c4582a173854232f7fea5caf945d140ee92fde5c1`,
  Chapter III, revision April 29, 2019, Section 3, pages 3--4. Original:
  `C:/Central-Library/Casselman--p-adic groups lecture notes/Introduction to representations of p-adic groups/Casselman--Chapter III - Induced representations and the Jacquet module--2019.pdf`.

The character-parametric and commutative-ring formulations are internal
generalizations, proved by the implementation. The cited original normalized
constructions use a specific inverse-half-modulus character. Smoothness here
is derived using the following exact project versions, rather than importing
the stronger source results concerning exactness or admissibility:

| Dependency | Artifact, version |
| --- | --- |
| Actual Jacquet quotient action | `6574bc6a-331d-4a8e-b089-969b377e4598`, 1 |
| Smoothness definitions | `665022df-625b-44ae-9dbd-425f6e266bab`, 1 |
| Character twisting definitions | `c83db975-8b79-4fbb-9901-2db836910a0a`, 1 |
| Continuous pullback preserves smoothness | `e064c7c1-aa21-4d84-b915-953b42d5f779`, 1 |
| Surjective intertwiners preserve smoothness | `4b00bba5-86eb-4d6d-98a2-94e697e2ac73`, 1 |
| Open-kernel twists preserve smoothness | `bfc0af4a-747e-42b0-befc-a12ca0239b22`, 1 |

These six exact versions were verified accepted, published and current at
Library commit `843c574c920aa9926ab56adf662c74b3cd4ed0e1`.
The quotient-action core was published in that commit with effective snapshot
`42106411fcd47bace4b6e12d64b234b7564303775ee7b633bd3341e60208dd4b`
and semantic publication receipt `46f6dce250ca48d98be047905af8d5d6`.
Its integrated Lean and Markdown are unchanged from the construction used here.

The environment is `2ecc41bc-2901-4e34-96c5-6d98fbb3c74d`, version 1,
Lean 4.34.0, with Mathlib commit
`5ed2965256430c3649e86755f9576b54eca72435`.
The same contribution contains `PositiveCharacter.lean` and `Normalized.lean`
with their paired explanations.
