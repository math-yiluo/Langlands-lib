# Displacement of the primitive Lubin–Tate point by units

Module `Nyll.ClassFieldTheory.LubinTate.FiniteLevel.PrimitiveDisplacement`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

Let K be a local field with uniformizer π, residue field of q elements, and standard Lubin–Tate formal group F. The file measures how far a unit a of the valuation ring moves the primitive point λ of the n-th standard finite level, using the normalized additive valuation of that level's valuation ring: if a first differs from 1 in principal-unit depth k ≤ n, then [a](λ) − λ has valuation exactly q^k. The analytic input is proved in the file, not assumed.

## Main results

- `standardLubinTateFormalAdd_sub_left_addVal`: for topologically nilpotent x, z in the level's valuation ring, F(x, z) − x has the same valuation as z.
- `standardLubinTateEndomorphismEvalAt_unit_addVal`: for a unit a, [a](x) has the same valuation as x.
- `standardLubinTateEndomorphismValue_uniformizer_pow`, `standardLubinTatePrimitivePointIterateInteger_hasEval`: [π^k](λ) is the evaluated polynomial iterate, and it is topologically nilpotent.
- `standardLubinTateEndomorphismValue_sub_one_addVal_of_exactDepth` and `standardLubinTatePrimitivePointIntegerAction_sub_self_addVal_of_exactDepth`: if a ∈ U^k, a ∉ U^(k+1) and k ≤ n, then [a − 1](λ) and [a](λ) − λ both have valuation q^k.
- `standardLubinTatePrimitivePointIntegerAction_sub_self_addVal_ge_iff_mem`: for k ≤ n + 1, the valuation of [a](λ) − λ is at least q^k iff a ∈ U^k (the fixed case, of infinite valuation, included).
- `..._ge_iff_mem_of_pow_interval`: for 1 ≤ k ≤ n + 1 and q^(k−1) ≤ r < q^k, the bound r + 1 detects U^k in the same way.
- `standardLubinTateUnitParameterToGal_apply_primitivePointInteger`: the automorphism of the level attached to a finite unit parameter acts on λ (through `valuationSubringAutOfUniqueExtension`) as its chosen representative does. The three statements above are then restated for these automorphisms.
- `standardLubinTateGal_displacement_addVal_le_of_ne`: every σ in the Galois group of the level field over K that moves λ moves it by valuation at most q^n.

## Proofs

[a](X) is X times a power series with constant coefficient a, and F(X, Y) − X is Y times a two-variable series with constant coefficient 1, so after evaluation the cofactors are units. Writing [a](λ) = F(λ, [a − 1](λ)) and a − 1 = c·π^k with c a unit reduces the depth formula to the valuation q^k of [π^k](λ), taken from the level-valuation file. The bound for σ uses surjectivity of the unit-parameter map onto the Galois group.

## Watch for

- U^k is the library's `CompleteDVF.higherPrincipalUnitGroup`, membership meaning a − 1 ∈ m^k.
- Indexing: the module docstring calls the point at index n the primitive point of level n + 1, and a fixes it exactly when a ∈ U^(n+1); that criterion is imported, not proved here.
- The Galois statements concern the chosen representative of a finite unit parameter.
- q is `Nat.card F.residueField`; in Lean, `F` is the local-field structure on K, not the formal group.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/LubinTate/FiniteLevel/PrimitiveDisplacement.lean`: the Lean file is the source byte for byte (SHA-256 `3d6193f3ccc3a70711f4f0bac96672804ab9b525d06cb655fc8431e4992d8fca`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
