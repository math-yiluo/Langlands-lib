# Prime Artin elements, Frobenius, and Hilbert class fields

Module `Nyll.ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.MathlibFrobeniusHilbertComparison`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

The file proves the statements announced in `ClassFieldTheory.Theorems.FrobeniusAndHilbertClassFields`. It compares the library's prime Artin elements in a finite abelian extension `L/K` of number fields with `arithmeticFrobeniusAt`, which unfolds to Mathlib's `arithFrobAt`, and derives the public Hilbert class field statements from the selected big (narrow) and small Hilbert class fields.

## Prime Artin elements and Frobenius

For `L/K` abelian and a finite prime `v` of `K`:

- `arithmeticPrimeArtin_eq_inverse`: the arithmetic-normalized prime Artin element is the inverse of the geometric one, `finitePlacePrimeArtin`.
- `arithmeticPrimeArtin_stabilizes_chosenPrime`, `arithmeticPrimeArtin_stabilizes_prime`: it fixes every prime of `L` above `v`.
- `orderOf_arithmeticPrimeArtin_eq_inertiaDegree` and `arithmeticPrimeArtin_eq_one_iff_splitsCompletely`: if `v` is unramified in `𝓞 L` (`Algebra.IsUnramifiedIn`), its order is the inertia degree, and it is trivial exactly when `v` splits completely.
- `orderOf_arithmeticFrobeniusAt_eq_inertiaDegree`, `arithmeticFrobeniusAt_eq_of_liesOver`: the Frobenius at `w` above `v` has order the inertia degree if `w` is unramified, and does not depend on `w`.
- `arithmeticPrimeArtin_eq_arithmeticFrobeniusAt`: at an unramified `w` above `v`, the arithmetic prime Artin element is `arithmeticFrobeniusAt w`. The proof compares residue actions; inertia is trivial.
- `finitePrimeSplitsCompletely_iff_original` (for `L/K` Galois): splitting with `e = f = 1` at every prime above `v` is equivalent to the library's `FinitePlaceSplitsCompletely`, defined through stabilizers.

## Hilbert class fields

Here `FiniteAbelianExtension K` consists of finite abelian subextensions of `SeparableClosure K`. As used here, `IsBigHilbertClassField E` asks that `E` be unramified at finite places and receive every such extension; `IsSmallHilbertClassField` is the same with "everywhere unramified".

- Degrees of the selected fields: the narrow class number and `classNumber K`. The big one is unramified at finite places and the small one everywhere.
- `exists_bigHilbertClassField`, `exists_smallHilbertClassField`: such fields exist, as images of the selected ones under an embedding into the separable closure.
- `..._degree_eq_narrowClassGroup_card_of_isBig`, `..._degree_eq_classNumber_of_isSmall`: every big, respectively small, Hilbert class field has that degree.
- `nonempty_algHom_to_selectedSmallHilbertClassField`: every everywhere-unramified `F` embeds in the selected small field. `smallHilbertClassFieldEquivOfIsSmall`: every small Hilbert class field is isomorphic over `K` to the selected one.
- `finitePrime_splitsCompletelyInSmallHilbertClassField_iff_principal` (and `_of_isSmall`): a finite prime splits completely if and only if it is principal.
- `ideals_becomePrincipalInSmallHilbertClassField` (and `_of_isSmall`): every ideal of `𝓞 K` becomes principal in the small Hilbert class field.

## Points to watch

- The deep inputs are imported: degree formulas, unramifiedness, the embedding (maximality) theorems, the splitting criterion and principalization. This file transports them along isomorphisms.
- The prime Artin order and splitting results need `v` unramified at every prime above it; the Frobenius order and comparison need it only at `w`.
- For big Hilbert class fields only the degree is transferred; no isomorphism with the selected field is given.
- Public and original library predicates for unramifiedness and complete splitting are distinct and bridged by `..._iff_original` lemmas.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/GlobalClassFieldTheory/GlobalClassFields/MathlibFrobeniusHilbertComparison.lean`: the Lean file is the source byte for byte (SHA-256 `7a6b3e8c515ae59002f136b41f5e7cc820ff5c74a0860b90858659517de0b187`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
