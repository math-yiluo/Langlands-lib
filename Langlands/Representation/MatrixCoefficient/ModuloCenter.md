# Matrix-coefficient norms modulo the center

Worker 23 develops the absolute value of the existing complex matrix coefficient
on the actual quotient group `G / Z(G)`. The representation carrier is an arbitrary
complex module in its own universe, with no topology or dimension restriction.

`UnitaryCentralCharacter rho` supplies a homomorphism from the actual group center
to complex units, an open kernel, values of norm one, and proofs that these values
give the scalar action of the center on every vector. This is genuine character
data with a specified action; no central-character existence theorem is assumed.

`coefficientNorm` descends `g -> norm(ell(rho(g)v))` to the quotient. Its intrinsic
proof first computes the coefficient at `g*z`, then uses the character's unit norm.
Two representatives differing by a central element therefore have equal values.
The value on a representative, nonnegativity, and independence from the chosen
central-character datum are proved.

`IsSquareIntegrableModCenter rho mu` requires admissibility and such a character
for which every coefficient of a smooth-dual functional and a vector belongs to
`L^2` on the central quotient. Here `MemLp` includes almost-everywhere strong
measurability and finite seminorm. The explicitly supplied measure must be Haar
for the quotient topology and its Borel measurable structure. It cannot be an
arbitrary zero measure. This predicate does not construct a Haar measure, identify
different normalizations, or prove a square-integrability criterion.

## Source and precise scope

Casselman, *Introduction to the theory of admissible representations of p-adic
reductive groups*, draft of May 1, 1995, Section 2.5, printed page 28, defines
square-integrability for an admissible representation with a unitary central
character by square-integrability of every smooth-dual matrix coefficient modulo
the center. Section 2.1, printed page 21, gives the open-kernel character convention.
The quotient-norm construction is an internal realization of that definition:
only the absolute value descends for a nontrivial unitary character.

- Literature ID: `casselman-1995-admissible-representations`.
- SHA256: `78b921fc6331ad2b75389f37d15bd5ac3399e6cfc2d7555e1a4d666e0d42612a`.
- Original file:
  `C:/Central-Library/Casselman--p-adic groups lecture notes/Introduction to representations of p-adic groups/Casselman--Introduction to the theory of admissible representations of p-adic reductive groups--1995.pdf`.

The algebraic quotient construction works for any group with topology carrying
the displayed datum. The integrability predicate uses a topological group and a
supplied Borel Haar measure on its central quotient. This generic extension is
explicit; no reductive-group theorem is transferred to arbitrary groups.

## Dependencies and status

Direct project imports:

- Matrix coefficients `5352a743-a6a8-4824-b91e-1cbc32b79b30`, version 1,
  publication `12dbb4572150a088d7f1df3eb9f5b771cb71604c`,
  effective snapshot `aa9653082118d59a057d45b6a329caa3fdfd621252627ae6692fbc7c82d927a1`.
- Smooth contragredient `be3f8221-aa6f-4069-8faa-f04e1f5dc4b7`, version 1,
  publication `933f2719b54fcf01bebb367c9cae56b8d5f17edc`,
  effective snapshot `7d5e8442053b0eefbf0cf949c9743496816ec8431a297b6b656a3700c992df0c`.

Both are accepted, published and current at Library
`9007729971e6e6ecea63b5567b6d1621769ccfb0`. The smoothness and admissibility
predicates come transitively from `665022df-625b-44ae-9dbd-425f6e266bab` version 1.
Mathlib supplies the actual group quotient, complex norm, Haar-measure class,
and `MemLp`. Environment `2ecc41bc-2901-4e34-96c5-6d98fbb3c74d` version 1 pins
Lean 4.34.0 and Mathlib `5ed2965256430c3649e86755f9576b54eca72435`.

The complete pair and an explicit-universe signature diagnostic compile in the
pinned environment. Independent semantic review and publication remain required.
This pair defines square-integrability modulo the center, not the separate
temperedness, essential square-integrability, or classification constructions.
