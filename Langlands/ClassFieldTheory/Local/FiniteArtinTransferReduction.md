# Finite Artin transfer reduced to the inverse-cup character comparison

> **The hypothesis `FiniteCupArtinCharacterComparison` is false. Do not cite
> `arithmeticReciprocityOfCup_eq_symbol`, `arithmeticTransfer` or `geometricTransfer`.**
> These three theorems take that proposition as a hypothesis, so they say nothing. Its
> negation is the statement `FiniteCupArtinCharacterComparisonFails` (module
> `Langlands.ClassFieldTheory.Local.FiniteCupArtinComparisonFailureStatement`), proved as
> `finiteCupArtinCharacterComparisonFails` (module
> `Langlands.ClassFieldTheory.Local.FiniteCupArtinComparisonFailureProof`). The true
> comparison is `finiteGeometricCupArtinCharacterComparison`. The transfer squares for the
> carry symbols are proved from it in `FiniteGeometricCupArtinComparison`
> (`arithmeticTransfer_of_geometricCupComparison`, `geometricTransfer_of_geometricCupComparison`).
> The other declarations of this module (`canonicalClassFormation`, `fundamentalClass`,
> `fundamentalClass_spec`, `cup_bijective`, `geometricSymbol`, `fundamentalClass_restriction`)
> do not use the false hypothesis. The Lean text is unchanged. The rest of this file is the
> original description, including its remarks about proving the comparison, which do not
> apply.

This internal construction isolates the finite arithmetic input to actual
transfer compatibility. Its only unproved mathematical premise is the
exact proposition `FiniteCupArtinCharacterComparison`; the file does not
prove or assume the unconditional common-closure reciprocity target.

The canonical invariant family used by `FiniteArtinSymbol` satisfies the
published finite class-formation axioms. Its exact relative invariant
image supplies the chosen positive `fundamentalClass`. The published Tate
cup theorem and class-formation theorem prove bijectivity of cup with
every such class. The existing restriction theorem identifies the chosen
class after a change of base field with the chosen class for the new base.
These facts are proved from Library inputs, not added as hypotheses.

Assuming `FiniteCupArtinCharacterComparison`, every character evaluates
arithmetic inverse-cup reciprocity on a unit norm class as the corresponding
carry symbol. The concrete `abelianizedArtinSymbol` has those same character
values. Finite character separation therefore identifies the two elements
of the actual finite Galois abelianization.

The proved inverse-cup transfer square then yields `arithmeticTransfer` for
the concrete carry-symbol maps. The transfer is the actual finite-coset
product in the relative Galois groups, and the units map is the actual
field inclusion. The finite Galois top field is Galois over both base
fields; the middle field need not be normal over the lower base.
Precomposing each arithmetic symbol with unit inversion defines
`geometricSymbol`, and the same square at the inverse unit proves
`geometricTransfer`.

The character comparison remains an explicit prerequisite to be proved
independently. Passage from these finite Galois squares to the profinite
and Weil transfer squares is also a separate obligation. No candidate
family or full system relation is concluded here.
