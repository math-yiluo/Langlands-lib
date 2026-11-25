# Abstract reciprocity: the Sylow step

Module `Nyll.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Sylow`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

In abstract class field theory over a topological group `G`, let L/K be a finite Galois extension of abstract fields (closed subgroups of `G`) and P a Sylow p-subgroup of G(L/K), with fixed field M = L^P. This file proves the group-theoretic facts about M used to reduce surjectivity of reciprocity to solvable extensions.

## Results

- `abstractReciprocity_sylow_lowerQuotient_isPGroup`: G(L/M) is a p-group, being isomorphic to P.
- `abstractReciprocity_sylow_lowerQuotient_isSolvable`: hence G(L/M) is solvable (a finite p-group is nilpotent).
- `abstractReciprocity_sylow_intermediateDegree_eq_index`: [M : K] equals the index of P in G(L/K).
- `abstractReciprocity_sylow_intermediateDegree_coprime`: [M : K] is prime to p.
- `sylowAddSubgroup_le_nsmul_range_of_coprime`: in any abelian group B, possibly infinite, a Sylow p-subgroup lies in the image of multiplication by n when n is prime to p, because the n-th power map is a bijection on a p-group.
- `abstractReciprocity_sylowAddSubgroup_le_intermediateDegree_nsmul_range`: the special case n = [M : K].

## Points to watch

- M/K need not be normal; no normality of P is assumed.
- The Sylow subgroups of B are taken in the sense of Mathlib's `Sylow` on `Multiplicative B`, and B is not assumed finite. In the reciprocity argument B is the norm quotient, which at this stage is only known to have bounded exponent.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/AbstractClassFieldTheory/Reciprocity/Sylow.lean`: the Lean file is the source byte for byte (SHA-256 `6e1694460607833be012cf232995a11be1501a480a7344723966835153d8c35c`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
