# Rank-one inputs for actual local Weil groups

Author: Worker 20.

For a supplied finite p-adic field `F : PadicField p`, this module uses the
published actual Weil group `Weil.Local.localWeilGroup F`, its actual
residue-degree map, and `F.canonicalTopologicalData`. It connects continuous
field quasicharacters to genuine continuous Weil representations and their
classes in the exact-sequence Grothendieck group.

## Conditional reciprocity transport

`ReciprocityCandidate F` abbreviates the published type of continuous group
isomorphisms from the actual topological Weil abelianization to `F.Carrierˣ`.
No element of this type is constructed, assumed to exist, or selected.
`reciprocityUnits F e` composes the actual quotient projection with a
specified candidate `e`. Its inverse is never applied to the nonabelian Weil
group.

`fieldCharacter F e χ` uses the published continuous character descent and
transport equivalence to obtain a field quasicharacter from a Weil character.
`weilCharacter F e η` is the actual composite of `η` with `reciprocityUnits`.
`weilCharacter_eq_symm` identifies it with the inverse of that same published
equivalence. The two inverse identities follow from the equivalence laws,
without choosing lifts from the abelianization.

`representation F e η` constructs the continuous character line for this
Weil character using `FiniteRepresentation.continuousCharacterLine`.
Its complex vector-space rank is proved to be one. `virtualClass F e η`
is its actual class in the published exact-sequence Grothendieck group of
continuous representations. The representation carrier universe `uV` is
independent of the field universe `uF`, and the virtual degree is proved
to be one. `virtualClass_fieldCharacter` proves that transporting an existing
Weil character to the field and back preserves its actual virtual class.

## Normalization and source

The constructors above work for a specified candidate `e`. The geometric
normalization theorems additionally require the explicit hypothesis

```text
LocalReciprocityCandidateRelation F.canonicalTopologicalData
  (localResidueDegree F) e.
```

`reciprocityUnits_order` specializes the order equality contained in that
relation to the quotient class of a Weil element. The abelianized degree
after quotient projection is the actual degree by construction.
`reciprocityUnits_geometricFrobenius` then applies the published degree-one
identity for `localGeometricFrobenius F` and converts from multiplicative
integer notation. The result says its image has normalized valuation order
positive one, as required by the geometric-Frobenius convention.

This normalization is Deligne, *Les constantes des équations fonctionnelles
des fonctions L* (1973), section 2.3, printed page 523, retained PDF page 23.
Registered source: `deligne-1973-local-constants`; SHA256:
`b03f483c4eeca79b75e34b88f41406fe4c9e16ba621480ce859697c93e8d5844`.
The original passage was read and its retained-file hash checked. No
source-specific errata entry was found in the project literature or notes.
Deligne's statement that geometric Frobenius corresponds to a uniformizer
is used here conditionally through the published reciprocity relation,
not as an axiom or a proved local class field theorem.

The implementation is a derived construction on
`Langlands.Weil.Local.Assembly`,
`Langlands.ClassFieldTheory.Local.ReciprocityRelations`, and the paired
`Langlands.Weil.Representation.CharacterLine`. The original source supplies
the normalization; universe lifting and insertion into the exact quotient
are implementation constructions, not assertions attributed to Deligne.
No unpublished draft is reused.

This module supplies rank-one inputs for a later nonabelian local-constant
system specification. It defines no epsilon function, assumes no existence
or uniqueness of such a system, and asserts no uniqueness of a reciprocity
candidate from these single-field relations.
