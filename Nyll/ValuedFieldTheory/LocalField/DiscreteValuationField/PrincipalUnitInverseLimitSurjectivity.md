# Surjectivity onto the inverse limit of principal-unit quotients

Module `Nyll.ValuedFieldTheory.LocalField.DiscreteValuationField.PrincipalUnitInverseLimitSurjectivity`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

Let `F` be a complete discretely valued field in the library's sense (`CompleteDVF`), with first principal units `U^1` and the inverse limit of the quotients `U^1 / U^(n+1)`. The file proves the compactness step of the equal-characteristic structure theorem for the units of a local field: a continuous map from a compact space to this inverse limit is surjective as soon as each of its finite coordinates is surjective.

- `surjective_principalUnitProdiscreteLimit_of_surjective_coordinates`: for a compact space `A` and a continuous `g : A → PrincipalUnitProdiscreteLimit F`, if for every `n` the composite of `g` with the `n`-th coordinate is surjective, then `g` is surjective.
- `Internal.surjective_principalUnitInverseLimitCarrier_of_surjective_coordinates` and its `Additive` variant: the same statement on the raw inverse-limit carrier, which is how the public version is proved.

Proof: for a target point `y`, the sets of `a` whose `n`-th coordinate agrees with that of `y` are closed by continuity, nonempty by surjectivity of the coordinates and decreasing by compatibility of the coordinates; Cantor's intersection theorem in the compact space `A` gives a common point.

Watch for:

- In the internal versions the discrete topology on each quotient is installed by a local `let` inside the statement, so continuity of `g` refers to that topology. The public version uses `PrincipalUnitProdiscreteLimit`, which carries the prodiscrete topology in its type.
- No finiteness of the residue field is assumed; compactness of the source does the work.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ValuedFieldTheory/LocalField/DiscreteValuationField/PrincipalUnitInverseLimitSurjectivity.lean`: the Lean file is the source byte for byte (SHA-256 `1620648337b5c46528bc76366e053d08de70011a53e810827e8f93090e78c4fa`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
