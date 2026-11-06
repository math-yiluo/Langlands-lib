# From scalar abelian duality to actual character lines

This internal reduction isolates the scalar input to the nonabelian dual
functional equation. `AbelianExpressionDualityStatement` asserts, for every
prime and every finite intermediate field of the specified algebraic closure,
that the two actual abelian epsilon expressions have product one. The first
uses the supplied field quasicharacter, additive character and Haar measure;
the second uses normalized absolute value times the inverse quasicharacter,
the additive character scaled by minus one, and the supplied dual Haar measure.
The measure condition is precisely `FourierDualMeasures`, including convergence
of the second Bochner integral and reflection on every Schwartz–Bruhat test.
No scalar identity is proved by defining this proposition.

`characterLineDuality_of_abelianExpressionDuality` proves that this scalar
identity implies the previously published `CharacterLineDualityStatement`.
It descends an arbitrary continuous character of the actual Weil subgroup
through the topological abelianization equivalence and the supplied reciprocity
equivalence. The inverse equivalence identity identifies its actual character
class with the class of a field character. Normalized reciprocity and
`normTwistedDual_characterClass` identify the norm-twisted full contragredient
class with the normalized absolute-value twist of the inverse field character.
Rank-one agreement from the supplied `IsSystem` then replaces both system values
by the actual scalar expressions, and the retained scalar premise proves their
product is one. Equality of complex values gives equality in the complex units.
The field and representation carrier universes remain independent throughout.

`dualFunctionalEquation_of_generation_of_abelianExpressionDuality` combines
this adapter with the published degree-zero generation and character-line
assembly reduction. Both actual generation and scalar duality remain explicit
premises. This module proves neither premise, does not strengthen `IsSystem`,
and is not a proof of the host task's unconditional target.

The provenance is internal: the proof uses the published topological
abelianization and character-transport equivalences, normalized reciprocity,
actual exact character-class duality and twist laws, and the existing conditional
assembly. No additional original-literature theorem is claimed.
