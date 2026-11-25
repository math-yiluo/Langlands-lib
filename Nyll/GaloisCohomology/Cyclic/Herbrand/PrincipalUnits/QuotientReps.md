# Integer units modulo principal units of level n

Module `Nyll.GaloisCohomology.Cyclic.Herbrand.PrincipalUnits.QuotientReps`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

For a field K with a valuative relation and a natural number n, the file names the quotient of the unit group of the valuation ring `𝒪[K]ˣ` by the principal-unit subgroup `principalUnits K n`, and gives it a small interface.

- `IntegerUnitsModPrincipalUnitsAtLevel K n` is the type `𝒪[K]ˣ ⧸ principalUnits K n`, with its commutative group instance.
- `integerUnitsModPrincipalUnitsAtLevelConcreteEquiv` is the identity isomorphism with the concrete quotient; `integerUnitsModPrincipalUnitsAtLevelMk` is the class map, which is surjective.
- `IntegerUnitsModPrincipalUnitsAtLevel.inductionOn` proves a property of all classes from representatives; `integerUnitsModPrincipalUnitsAtLevelLift` descends a homomorphism whose kernel contains the level-n principal units.
- A class is trivial exactly when its representative lies in `principalUnits K n`, and two units have the same class exactly when their quotient does.

The type is a named wrapper of the concrete quotient, meant to be used through this interface rather than unfolded. `principalUnits K n` is the library's own subgroup, available through the imported file on principal-unit quotients.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/GaloisCohomology/Cyclic/Herbrand/PrincipalUnits/QuotientReps.lean`: the Lean file is the source byte for byte (SHA-256 `b0c2a71caf47ff446e4656f0775e98666c8257a4419dbcb6b480a189a6f21999`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
