# The logarithmic lattice of S-units and the S-unit theorem

Module `Nyll.ClassFieldTheory.AlgebraicNumberTheory.SUnit.LogLattice`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

Let K be a number field and S a finite set of finite places of K. This file maps the S-unit group `SUnitGroup S` logarithmically onto a complete ℤ-lattice and shows that the kernel is the roots of unity. It then proves the S-unit theorem: the S-units are μ(K) times a free abelian group of rank (number of infinite places) + #S − 1.

## Reduced logarithm

- `ReducedLogSpace S` is Mathlib's Dirichlet logarithmic space, which omits one infinite place w₀, times ℝ^S. `reducedLog` sends x to mult(w)·log w(x) at the infinite places w ≠ w₀. At v ∈ S it gives the exponent of v in the principal ideal of x, as a real number.
- `reducedLog_eq_zero_iff`: the kernel is the torsion, that is, the roots of unity.
- `reducedLogLattice`, the image, is a complete ℤ-lattice (instances) of rank the unit rank plus #S (`finrank_reducedLogLattice`).

## Normalized logarithm at all places

- `LogPlace S` is the set of infinite places together with S. `FullLogSpace S` is ℝ^(LogPlace S), and `LogHyperplane S` is the kernel of `coordinateSum`.
- `fullLogAmbient`: mult(w)·log w(x) at infinite places, and log of the normalized absolute value `adicAbv` at v ∈ S. `sum_log_absoluteValues_eq_zero` is the product formula for S-units, derived from Mathlib's `NumberField.prod_abs_eq_one`. Hence `fullLog` lands in the hyperplane.
- `logHyperplaneEquivReduced`: the linear isomorphism that drops the w₀ coordinate and divides each finite coordinate by −log Nv. `logHyperplaneEquivReduced_fullLog` says that it carries `fullLog` to `reducedLog`.
- `fullLog_eq_zero_iff`: the kernel of `fullLog` is the torsion. `fullLogLattice`, the preimage of the reduced lattice, is a complete lattice in the hyperplane and equals the image of `fullLog` (`fullLogLattice_eq_range`).

## S-unit theorem

- `logRank S` is (number of infinite places) + #S − 1. S-units modulo torsion form a free ℤ-module (local instance `instModuleFree_freeQuotient`), of this rank by `finrank_freeQuotient`.
- `decompositionLinearEquiv`: the additive S-unit group is isomorphic to the roots of unity × (`Fin (logRank S) →₀ ℤ`).
- `decomposition`: `SUnitGroup S ≃* NumberField.Units.torsion K × Multiplicative (Fin (logRank S) →₀ ℤ)`.

## Proof

Discreteness: near 0 the integer finite coordinates vanish, so the element is a global unit, and discreteness of Mathlib's unit lattice applies. The rank comes from the imported `SUnitGroup.finrank`, and a dimension count then gives the spanning. The decomposition splits off the free quotient by the projective lifting property.

## Points to watch

- S contains only finite places. The infinite places are always added, so "#S − 1" in the comments counts them too.
- The decomposition is not canonical. It depends on a chosen basis and a chosen section.
- The finite coordinates of `reducedLog` are integer exponents, not logarithms of absolute values.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/AlgebraicNumberTheory/SUnit/LogLattice.lean`: the Lean file is the source byte for byte (SHA-256 `97ccb5cb9942488e13fb5903d1815e08b6efd7b691edea6b84f470810709a600`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
