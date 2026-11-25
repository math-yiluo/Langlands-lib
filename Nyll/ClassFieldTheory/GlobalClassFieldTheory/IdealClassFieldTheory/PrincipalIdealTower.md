# Galois towers of abelian extensions in an abstract Galois group

Module `Nyll.ClassFieldTheory.GlobalClassFieldTheory.IdealClassFieldTheory.PrincipalIdealTower`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

The principal ideal theorem uses a tower K ⊆ L ⊆ M of two finite abelian extensions, with M Galois over K. This file works in the abstract setting of a topological group G, where "fields" are closed subgroups and the order is reversed. It gives the subgroup facts needed to treat such a tower as one finite Galois extension. It also defines the maximal abelian subextension of a finite Galois extension.

## Main definitions and results

- `conjugateClosedSubgroup_eq_self_of_mem`: conjugation by an element of a closed subgroup K maps K to itself.
- `conjugateFiniteAbelianSubextension L s`: conjugating both ends of a finite abelian subextension L of K by s ∈ G gives a finite abelian subextension of the conjugate of K.
- `galoisSubextensionOfConjugateStableAbelianTower L M hstable`: L is finite abelian over K and M is finite abelian over L. Assume, as `hstable`, that the subgroup of M is stable under conjugation by every element of K. Then M is a finite Galois subextension of K.
- `maximalAbelianSubextension P`: for a finite Galois subextension P of K, the fixed field of the commutator subgroup of Gal(P/K), as a finite abelian subextension. Its field is `P.abelianIntermediateField`.
- `finiteAbelianIntermediate_le_maximalAbelianSubextension`, with its subgroup form `abelianIntermediateField_le_of_finiteAbelianIntermediate`: every finite abelian subextension L of K below P lies below the maximal abelian subextension.

## Proof

Normality of M over K comes from the stability hypothesis. Finiteness comes from transitivity in the tower. Maximality holds because restriction Gal(P/K) → Gal(L/K) has abelian target, so it kills the commutator subgroup.

## Points to watch

- M is not shown to be Galois over K on its own. Conjugation stability is a hypothesis, which the user must establish in each application.
- All statements are about subgroups of an abstract G, not about fields. In subgroup order, inclusions of fields are reversed.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/GlobalClassFieldTheory/IdealClassFieldTheory/PrincipalIdealTower.lean`: the Lean file is the source byte for byte (SHA-256 `e5b864b1321753b984ad9b8067ac31fa7326355592e3ca528888c8004c82b39e`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
