# Hecke characters and prescribed local components

Author: Worker 2.

`Langlands.Global.HeckeCharacter K` is the group of continuous multiplicative
maps from the actual quotient `IdeleClasses K` to `ℂˣ`. It includes nonunitary
characters; `HeckeCharacter.IsUnitary` separately requires the complex absolute
value to equal one at every idele class. This is the quasi-character convention
in the sources. The module uses the actual number field `K : Type u` and has
no abstract substitute for its idele-class group.

`onIdeles` pulls back along the continuous quotient map. Conversely,
`ofIdeleCharacter χ hχ` descends a continuous idele character whose values on
all diagonal elements are one. Its multiplicativity is supplied by the
group-quotient lift, and its continuity follows from the quotient topology.
`ideleCharacterEquiv` implements both directions and proves the two inverse
identities. The kernel requirement is proved using an actual range witness for
each principal idele. This is ordinary quotient descent; existence of a
character with specified local restrictions is not assumed.

The local characters `finiteComponent` and `infiniteComponent` are compositions
with the continuous single-place maps. `atInfinity` and `atFinite` are the
restrictions to the whole infinite and finite idele factors. Multiplication
and inversion of characters are pointwise and commute with these local maps.
`IsUnramifiedAt` means triviality on the subgroup of units of the local valuation
subring, represented inside the units of the local field.
`HasFiniteOrder` requires a strictly positive power equal to the identity.

`HasPrescribedFiniteComponents` compares actual continuous characters on a
finite set of local multiplicative groups, including their exact place indices.
`HasPrescribedInfinityComponent` compares the whole archimedean character.
These are definitional predicates, not an extension/existence theorem.
CM infinity weights, conjugation, regularity, character extension and almost
everywhere unramifiedness remain separate constructions or theorem obligations.

## Original sources and correspondence

André Weil, *Basic Number Theory*, second edition, Springer, 1973,
Chapter VII §3, pp.114–117, especially Definition 5 on p.115 and the
unramified convention after Definition 7 on p.117; and §4, p.118:
continuous quasi-characters, their pointwise group structure, the actual
idele-class quotient, identification with idele characters trivial on
principal ideles, and restrictions to local multiplicative groups.
Worker 2 read these passages and the adelic definitions cited in `Adelic.md`.

Literature ID `weil-1973-basic-number-theory`, retained original
`C:/Central-Library/Weil--Basic number theory (book, 2nd edition)--1973.pdf`,
SHA256 `32fff78f8ccc5d6378907941e26746c34e20fc3adf5096508844cfe8a301e33b`.
Printed page `p` is PDF page `p + 17`.

Henniart (2000), §2.2 p.444, uses continuous quasi-characters of the same
quotient for twisting. Sections 3.4–3.6, pp.449–451, impose additional
unitarity, conjugate self-duality, regularity and prescribed components.
Those additional existence results are not fields of `HeckeCharacter`.
Literature ID `henniart-2000-simple-proof`, SHA256
`be283c3e8187f1eed365537c72379c3e06e7791756954c2ac783c6beea2979de`.
The original was read directly at the stated passages.

The Lean equivalence is a derived implementation of the quotient identification
on Weil p.118. The prescribed-component predicates spell out equalities using
these actual restrictions; they are not attributed as independent theorems to
Weil. No local reciprocity, global class field theorem, algebraic infinity type,
or automorphic induction is introduced or proved by this module.
