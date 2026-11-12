# Compact inclusion for a standard-Levi restriction pair

This derived adapter specializes `leviSpecialCompactSubgroup_le_comap` to the actual standard Levi of a connected reductive group at a maximal split torus and a generic cocharacter. Both supplied valuation apartments have full V6, the Levi apartment has V7, and the supplied point pair satisfies literal restriction. The conclusion uses the original `specialCompactLeviSubgroup`, the preimage of the same ambient norm-one quotient stabilizer.

The published standard-cocharacter theorem expresses the standard Levi as an actual cocharacter centralizer. Its connected reductivity and maximal split torus come from the existing standard-Levi theorems. The ambient centralizer also represents the torus centralizer inside the Levi through `standardLeviCentralizerDatum`. Independence of V6 from the chosen centralizer representative transfers the supplied Levi V6 to this representative. Its group is the ambient centralizer group, so the identity morphism and the published factorization equation provide the commuting square needed by the generic inclusion.

There is no additional centralizer-morphism, building-availability, specialness or maximality premise. This adapter proves only inclusion and does not assert the existence of a restriction pair or compact equality. Its provenance is the stated internal composition of existing Library constructions and the preceding generic inclusion.

The selected construction `standardLeviSpecialCompactInclusion` is the identity on actual Levi rational points, with domain the supplied Levi compact stabilizer and codomain the literal preimage of the ambient compact stabilizer. The proved inclusion supplies its subgroup-membership proof. Thus its unit and multiplication laws are definitional.

The local instances have explicit names specific to this module so that
combined imports retain distinct declarations. Their types, bodies and local
instance scope are unchanged.
