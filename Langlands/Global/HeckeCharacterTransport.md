# Arithmetic transport of actual Hecke characters

Author: Worker 2.

For number fields `K` and `L` in independent universes, `HeckeCharacter.comap e`
precomposes an actual continuous complex idele-class character with the published
continuous arithmetic equivalence `AdelicFunctoriality.ideleClassEquiv e`.
The character may be nonunitary. The coefficient group remains `ℂˣ` and the
source remains the actual quotient by principal ideles with its quotient topology.
Continuity and multiplicativity follow from composition of continuous monoid maps.

Identity and composition are proved from the actual arithmetic equivalence laws.
Pullback is contravariant: for `e : K ≃+* L` and `f : L ≃+* M`, pullback along
`e.trans f` first pulls a character back along `f`, then along `e`.
It commutes with multiplication, inverse and natural powers.
`comapEquiv e` is a multiplicative equivalence from the characters of `L` to
those of `K`, whose actual inverse is pullback along `e.symm`. Both inverse
identities follow from the arithmetic identity and composition laws.

`comap_onIdeles` gives the formula on actual idele representatives.
`comap_finiteComponent` and `comap_infiniteComponent` give the exact local
formulas at the corresponding pulled-back places. Each uses the units map of
the actual completed-field isomorphism, rather than a selected abstract local
field. The formulas follow by applying the character to the published
compatibility of arithmetic transport with insertion of one local unit.

Unitarity is preserved and reflected by surjectivity on actual idele classes.
Finite order is preserved and reflected with the same strictly positive
exponent, using the injective multiplicative character equivalence.
Unramifiedness is preserved and reflected at the corresponding finite places:
the actual completion isomorphism preserves membership in the valuation subring
for both the value and inverse of a unit. The resulting integral-unit subgroup
correspondence and surjectivity of the map on local units prove both directions.

`galoisAut` sends an actual rational field automorphism to the multiplicative
character equivalence given by pullback along its inverse. The composition law
makes this a monoid homomorphism to character automorphisms, and `galoisAction`
bundles the resulting installable multiplicative left action. No global action
instance is installed. Its value is `χ (ideleClassAut (σ⁻¹) x)`; inverse pullback
is necessary for the left action law. Unitarity and finite order are preserved
and reflected.

For a CM field, `complexConj` pulls back by the actual field involution.
`complexConj_apply` is definitionally `χ (ideleClassComplexConj x)`, exactly the
evaluation convention already used by the published Harris setup and CM
character statements. The character operation is involutive, multiplicative,
and commutes with inversion. The Galois action of CM conjugation equals this
direct pullback because the arithmetic involution equals its inverse.
Unitarity and finite order are again preserved and reflected. No existing
statement definition is modified.

Provenance is internal composition of the published arithmetic transport and
actual Hecke-character constructions. This module does not introduce new
literature identifications. No existence or extension theorem for characters,
reciprocity, or character classification is assumed or proved.
