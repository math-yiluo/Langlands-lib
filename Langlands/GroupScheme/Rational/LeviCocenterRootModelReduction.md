# Removing derived semisimplicity from the Levi cocenter inputs

This internal supporting construction reduces the four structural inputs of
`LeviCocenterRootModelAssembly` to three:
`RootDatumExistenceStatement`,
`DerivedMaximalTorusProductSurjectivityStatement`, and
`DerivedMaximalTorusIntersectionStatement`, all at arbitrary universe `u`.
The global derived semisimplicity proposition is derived from the first two.
These three remaining propositions are explicit premises, so this module does
not prove the unconditional host target.

`IsDerivedSubgroup.hasFiniteCenter_of_rootDatum_product` passes from an arbitrary
field to its algebraic closure. Published field-extension preservation supplies
connected reductivity of the ambient group, and the proved derived base-change
identity supplies the actual derived inclusion. The published maximal-torus
existence theorem chooses an ambient maximal torus over the closure; proved
finite-Galois splitting makes it split there. The geometric compatible-torus
construction then places an actual split maximal torus of the derived subgroup
inside this chosen ambient torus.

The supplied root-existence proposition supplies an actual ambient root datum.
The resulting `derivedTorusCentralComplement`, together with the supplied
maximal-torus product surjectivity, gives an actual finite full derived centre
over the closure by `DerivedTorusFiniteCenter`. The published
`HasFiniteCenter.of_fieldExtension` reflects finiteness of the full
scheme-theoretic centre to the original field. It constructs a closed centre
representative there and descends its finiteness; nonreduced test schemes are
retained throughout.

`finiteDerivedCenter_of_rootDatum_product` chooses that actual finite group
scheme and its inclusion over the original field, returning `FiniteCenter D`.
`derivedSubgroupSemisimple_of_rootDatum_product` combines its full finite centre
with published connected reductivity of every actual derived subgroup. Thus
semisimplicity is no longer an independent structural premise.

`TorusCentralizerFiniteGaloisModel.cocenterRootDescent_of_rootDatum_product_intersection`
applies the previous assembly with this derived semisimplicity proof. It returns
the same genuine base and `CocenterRootDescentData` for the supplied model's
retained rational torus, finite Galois field, actual ambient root datum,
actual quotient composite, and canonical base change of the original separating
cocharacter. The auxiliary maximal torus chosen only for the finite-centre proof
does not replace any of those retained data. Ordinary Galois representations
and the invariant selected subset are exactly those of the existing assembly.

`splitTorusCentralizerCocenterRootModel_of_rootDatum_product_intersection` packages
the unchanged exact `SplitTorusCentralizerCocenterRootModelStatement.{u}` under
the three remaining explicit structural premises. No simple connectedness,
perfectness, characteristic restriction, or chosen parabolic is introduced.

The provenance is internal composition of the named published constructions,
the separately submitted finite-centre construction, and the retained actual
root-model assembly. This module makes no new original-literature transcription
and leaves the previously submitted assembly pair unchanged.
