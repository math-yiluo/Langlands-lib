# Faithfully flat local extensions with closed residue fields

This internal derived construction supports tests of scheme morphisms on local
rings with separably closed residue fields. It has no reducedness, noetherian,
Henselian, or characteristic assumption.

`ClosedResidueLocalExtensionStatement.{u}` says that every commutative local ring
`R : Type u` has a commutative local `R`-algebra `B : Type u` such that `B` is
faithfully flat over `R`, the algebra map is local, and the residue field of `B`
is algebraically closed. `closedResidueLocalExtension` proves this proposition.
Faithful flatness also implies that `R → B` is injective, so this construction
retains nilpotents.

The more general `exists_faithfullyFlat_local_with_residue` starts with a local
ring homomorphism `f : R → K` into any field `K` in the same universe and
constructs such an extension with residue field isomorphic to `K`.

For this, take the polynomial ring `A = MvPolynomial K R` and evaluate its
coefficients through `f`, sending the variable indexed by `k` to `k`. Evaluation
is surjective, so its kernel is maximal. Let `B` be the localization of `A` at
this kernel. Evaluation sends each denominator to a nonzero element of `K`,
so it extends to a surjection `B → K`. This map is local, and the induced
map from the residue field of `B` is a bijective field homomorphism.

The composite `R → B → K` is `f`, so locality of `f` shows that `R → B`
reflects units. Polynomial freeness and localization give flatness, and the
Mathlib theorem that a flat local homomorphism of local rings is faithfully
flat gives the required faithful flatness. Finally take `K` to be an algebraic
closure of the residue field of `R` and transport algebraic closedness along
the constructed residue-field isomorphism.

The provenance is the explicit polynomial and localization construction above,
using Mathlib's evaluation, localization, residue-field, and faithfully flat
algebra APIs. This result does not assert Henselianity or construct any
comparison between reductive groups.
