# The idele-class Herbrand quotient and the lower bound for the norm index

Module `Nyll.ClassFieldTheory.AlgebraicNumberTheory.Idele.Cohomology.HerbrandExactSequence`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

For a cyclic Galois extension `L/K` of number fields with group `G`, the file performs the last cardinality step of the idele-class Herbrand calculation: if the Herbrand quotients of the relative ideles and of the principal ideles are `q` and `q / |G|`, then `h(G, C_L) = |G|`, and therefore the index in `C_K` of the image of the class norm is at least `|G| = [L : K]`.

## Main definitions and results

- `RelativeIdeleHerbrandQuotientDefined K L σ` and `PrincipalIdeleHerbrandQuotientDefined K L σ`: propositions saying that the degree 0 and degree −1 groups of the relative idele group, respectively of the subgroup of principal relative ideles, are finite.
- `ideleClass_herbrandQuotient_eq_card_of_relative_principal_values`: assume `σ` generates `G`, both propositions hold, `h(I_L) = q` with `q ≠ 0` a rational number, and `h(principal ideles) = q / |G|`. Then the Herbrand quotient of `C_L` is defined and equals `|G|`.
- `card_le_ideleClassNorm_index_of_relative_principal_values`: under the same hypotheses, `|G|` is at most the index of the image of `ideleClassNorm`.
- `finrank_le_ideleClassNorm_index_of_relative_principal_values`: the same bound with `[L : K]` in place of `|G|`.

## Proofs

Multiplicativity of Herbrand quotients for `1 → Lˣ → I_L → C_L → 1`, from the imported Herbrand file, gives `h(I_L) = h(principal) · h(C_L)`; cancelling the nonzero factor `q / |G|` gives `h(C_L) = |G|`. Since the degree-zero group is the quotient of `C_K` by the class-norm image, a Herbrand quotient equal to a natural number bounds its order from below.

## Points to watch

- The values of the two Herbrand quotients, and the finiteness of their cohomology groups, are hypotheses (`hRelative`, `hPrincipal`, `hRelativeDefined`, `hPrincipalDefined`). According to the file they are supplied by the supported-idele calculation; they are not proved here.
- Cyclicity of `G` enters as the hypothesis `hgen` that every element is a power of `σ`.
- Since `Subgroup.index` is `0` for an infinite index, the bound also shows that the norm subgroup has finite index.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/AlgebraicNumberTheory/Idele/Cohomology/HerbrandExactSequence.lean`: the Lean file is the source byte for byte (SHA-256 `b36d5c72c53369df6effc44bc4023e54dfc99eacf82b1dbbc3999b657134f8e7`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
