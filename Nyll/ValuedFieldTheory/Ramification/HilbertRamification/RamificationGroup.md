# Normality of the ramification group in the inertia group

Module `Nyll.ValuedFieldTheory.Ramification.HilbertRamification.RamificationGroup`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

For a field extension L/K and a valuation subring A of L, the library defines a decomposition group D, an inertia group I inside D, and a ramification group R inside I, cut out by the principal-unit condition. The file proves that R is normal in I, transports I to a subgroup of the automorphism group L ≃ₐ[K] L and R to a subgroup of that copy, and identifies I/R with the quotient of the transported groups. The file's comment names the purpose: a later character map from I to a group of homomorphisms on value groups.

## Results

- `decompositionGroup_mapEquiv_mem_principalUnitGroup`: every τ in D maps principal units of A to principal units, since it acts on the residue field and fixes 1.
- `ramificationGroup_normal` (instance): R is a normal subgroup of I.
- `inertiaGroupEquivInAut`: I is isomorphic to its image `inertiaGroupInAut K A` in L ≃ₐ[K] L.
- `ramificationGroupInInertiaAut`: the image of R in that copy, with a membership lemma, normal there by `ramificationGroupInInertiaAut_normal`.
- `inertiaGroupQuotientRamificationEquivInertiaAutQuotient`: the induced isomorphism of I/R with the corresponding quotient of the images, with a simp lemma on classes.

## Proof

For x in Lˣ and y = τ⁻¹(x), the quotient (τστ⁻¹)(x)/x equals τ(σ(y)/y). Here σ(y)/y is a principal unit because σ lies in R, and τ preserves principal units.

## Watch for

The groups are taken for an arbitrary valuation subring, with no discreteness or finiteness assumption. R is the group defined by the principal-unit condition, not a member of a numbered filtration.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ValuedFieldTheory/Ramification/HilbertRamification/RamificationGroup.lean`: the Lean file is the source byte for byte (SHA-256 `20920d9f084ce1bfba42489bf76ad8968d3fd8c8560d7f979adbfed5549ab71d`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
