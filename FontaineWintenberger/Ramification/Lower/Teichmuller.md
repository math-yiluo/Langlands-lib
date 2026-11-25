# Multiplicative representatives for a perfect residue field

Module `FontaineWintenberger.Ramification.Lower.Teichmuller`, copied from the Lean library FontaineWintenberger. The origin of the file and the changes made in the copy are given at the end of this page.

Let `R` be a local ring, complete for the topology of its maximal ideal, whose residue field is perfect of characteristic `p`. The file constructs the multiplicative section of the reduction map (the Teichmüller representatives), proves that it is unique and natural, and specializes it to the ring of integers of a finite separable extension of a local field with perfect residue field.

## Main definitions and results

For `R` local with `IsAdicComplete (maximalIdeal R) R` and residue characteristic `p`:

- `residue_comp_monoidHom_injective`: for a commutative monoid `A` on which the `p`-th power map is bijective (`PerfectRing A p`), two multiplicative maps `A →* R` with the same reduction are equal.

With the residue field perfect in addition:

- `residueTeichmuller R p`: a homomorphism of monoids with zero from the residue field to `R`.
- `residue_residueTeichmuller`: it is a section of the reduction map.
- `residueTeichmuller_unique`: any multiplicative, zero-preserving section of the reduction equals it.
- `residueTeichmuller_pow`, `residueTeichmuller_frobenius`, `residueTeichmuller_zero`, `residueTeichmuller_one`: compatibility with powers, Frobenius, 0 and 1.
- `residueTeichmuller_sModEq`: if `y` lifts the `n`-th coordinate of `x` in the perfection (that is, the `p^n`-th root of `x`), then `residueTeichmuller R p x ≡ y ^ p ^ n` modulo the `(n+1)`-st power of the maximal ideal.
- `residueTeichmuller_naturality`: a local ring homomorphism `f : R → S` between two such rings carries the representative of `x` to the representative of the image of `x`.

For `K` with `IsPerfectResidueLocalField K` and `E/K` finite separable:

- instances: `spectralIntegerRing K E` is complete for its maximal ideal; its residue field is perfect and has characteristic `residueChar K`.
- `spectralTeichmuller K E`: the representatives in `spectralIntegerRing K E`, with `residue_spectralTeichmuller` and `spectralTeichmuller_unique`.
- `spectralTeichmuller_naturality`, `coe_spectralTeichmuller_naturality`: for a `K`-embedding `i : E →ₐ[K] F` of finite separable extensions, `i` carries representatives to representatives, along `spectralResidueInclusion K i`.

## Proofs

The section is Mathlib's `Perfection.teichmuller₀` for the ideal `maximalIdeal R`, composed with the identification of the perfect residue field with its own perfection. Uniqueness follows from Mathlib's `Perfection.liftMonoidHom` and `Perfection.quotientMulEquiv`; naturality is deduced from uniqueness, so no continuity of `f` is asked. Completeness of the spectral integer ring comes from the adic completeness of the unit ball of a complete discretely valued field.

## Points to watch

- The residue field need not be finite, and `p = 2` is allowed.
- `R` is only assumed local and adically complete, not a discrete valuation ring.
- `IsPerfectResidueLocalField` and `spectralIntegerRing` are the library's own notions.
- The spectral part assumes `E/K` finite and separable.

## References

Serre, *Local Fields*, Chapter IV.

## Origin of the file

Copied from the Lean library FontaineWintenberger (https://github.com/YijunYuan/FontaineWintenberger), commit `e835d58871d8d564901c0f13b685034cd202659e`, file `FontaineWintenberger/Ramification/Lower/Teichmuller.lean` (SHA-256 of the source file `1e8ded0cdf8fe91fe34b08e2c95d167cb1c5cb4e8c40256feec3fc3f93e2d127`). That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the copy:

- The two Lean options that the library's lakefile sets and that differ from Lean's defaults are set after the imports (`relaxedAutoImplicit false`, `maxSynthPendingDepth 3`).
