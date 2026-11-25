# An integral lattice from the relative basis, and its bad primes

Module `Nyll.ClassFieldTheory.AlgebraicNumberTheory.Adele.IntegralTensorSupport.Lattice`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

Let L/K be a finite extension of number fields, with the fixed K-basis (b_i) of L given by `relativeExtensionBasis`. The file scales this basis by a common nonzero integer d so that every vector becomes an algebraic integer. The 𝓞 K-span of the scaled vectors is a lattice in 𝓞 L. The quotient of 𝓞 L by this lattice is a finitely generated torsion module, so a nonzero element of 𝓞 K kills it. These two choices define a finite set of bad primes of K. Outside it, the unscaled basis is integral at every place of L above.

## Main definitions and results

- `exists_integral_relativeBasis_scale`: some d ∈ ℤ, d ≠ 0, makes every d·b_i integral over ℤ. `chosenRelativeBasisIntegralScale` is a chosen such d, also given in K, Kˣ and 𝓞 K.
- `scaledRelativeExtensionBasis`: the basis (d·b_i). Its vectors are integral (`..._isIntegral`). `scaledRelativeExtensionBasis_absoluteValue_le_one` says they have absolute value at most 1 for every extension to L of a nonarchimedean absolute value of K.
- `scaledRelativeIntegerLattice`: the 𝓞 K-span of the d·b_i inside 𝓞 L. `scaledRelativeFieldLattice` is the same span inside L, and `scaledRelativeIntegerLattice_map_toField` relates the two.
- `exists_nonZeroDivisor_smul_mem_scaledRelativeIntegerLattice`: every x ∈ 𝓞 L has a multiple by a nonzero element of 𝓞 K in the lattice.
- `ScaledRelativeIntegerLatticeQuotient`: the quotient of 𝓞 L by the lattice. It is a finitely generated 𝓞 K-module (instance) and torsion (`scaledRelativeIntegerLatticeQuotient_isTorsion`).
- `scaledRelativeIntegerLatticeAnnihilator`: a chosen nonzero element a of 𝓞 K that annihilates the quotient. So a·x lies in the lattice for every x ∈ 𝓞 L (`..._smul_mem`).
- `integralTensorControlElement` = d·a, its principal ideal `integralTensorControlIdeal` (nonzero), and `integralTensorBadPlaces`: the finite set of height-one primes dividing this ideal. `mem_integralTensorBadPlaces_iff` gives membership.
- Outside the bad set, d·a, a and d lie outside the prime (`..._not_mem_of_notMem`).
- `relativeExtensionBasis_absoluteValue_le_one_of_notMem`: if w is not a bad place, then every extension of the w-adic absolute value to L takes values at most 1 on every b_i.

## Proofs

The scale d exists because L is algebraic over ℤ. Torsion holds because the scaled vectors span L over K. The last theorem uses |d|_w = 1, which holds because d ∉ w, together with the bound for the scaled basis.

## Points to watch

- The bad set depends on the fixed basis and on two choices made with `Classical.choose`, namely d and a. It is not canonical.
- A comment calls the lattice quotient finite. The file proves only that it is finitely generated and torsion over 𝓞 K.
- The last theorem concerns the basis vectors only, not the coordinates of general elements.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/AlgebraicNumberTheory/Adele/IntegralTensorSupport/Lattice.lean`: the Lean file is the source byte for byte (SHA-256 `bd778493710f78ec2647ae40c3b1098506c204844ae8b031725e547aa865dece`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
