# Real characters of a standard Levi and the coroot annihilator

`Langlands.GroupScheme.standardLeviCharacterAnnihilator`
proves `StandardLeviCharacterAnnihilatorStatement.{u}`. For an arbitrary base
field, the range of real rational character restriction from the represented
standard Levi `L` to the supplied maximal split torus `T` is
`corootAnnihilator i D J` for the selected simple roots `J` and the supplied
reflection data `D`.

The source is David Renard, *Représentations des groupes réductifs p-adiques*,
French version dated 9 July 2026, V.3.13, printed page 112 (PDF page 118).
The registered source is `renard-2026-representations-groupes-reductifs-padiques`,
with SHA256 `7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
The statement documentation explains the identification of Renard's
`𝔞*_M ⊂ 𝔞*_∅` with the character restriction image and the arbitrary-field
formulation. [Paired statement](LeviCentralCompatibilityStatements.md)

## Lean proof

For a selected root `α`, the class of `D.representative α` is a generator of
the Weyl group of the closed Levi root subset. The published
`rootSubsetWeylGroup_standardLevi` identifies this group with the classes of
rational normalizer points in the standard Levi. The representing map
`j : L ⟶ G` therefore lifts a representative of this class to a rational
point of `L`. By cancelling `j` in the conjugation identity, the lift acts
on the factored torus `t : T.toGrp ⟶ L` by the same automorphism.
`weylAction_torusCharacterRestrict` gives invariance of the restricted
integral characters, which extends to the real tensor product. The real
reflection formula then forces the pairing with the coroot of `α` to
vanish, since the real root vector is nonzero.

For the reverse inclusion, choose a split component `a : A.toGrp ⟶ L`.
`standardLeviCentralDirections` gives `f : A ⟶ T` with `f` followed by `i`
equal to `a` followed by `j`, and with real cocharacter image equal to the
root annihilator of `J`. Cancelling `j` identifies `a` with the composite
through `t`, and tensoring character restriction preserves this composite
in reverse order. By `ker_restrictReal_eq_rootSpan_of_range`, restriction
from `T` to `A` has kernel the real span of `J`. The complement furnished
by `standardLeviRealDecomposition` makes this restriction injective on
`corootAnnihilator i D J`. Applying `renardLeviCentralDecomposition` to the
identity of `L` supplies surjectivity from the real characters of `L` to
those of `A`. A vector in the coroot annihilator can therefore be matched
on `A` by a real rational character of `L`. The first inclusion puts that character's
restriction to `T` in the same annihilator, and injectivity there shows
the two vectors are equal.
