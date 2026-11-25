# Finitely many ramified primes in a Dedekind extension

Module `Nyll.ClassFieldTheory.AlgebraicNumberTheory.Ramification.FiniteRamifiedPrimes`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

Let `B/A` be a finite, torsion-free extension of Dedekind domains whose fraction fields form a separable extension. This file shows that only finitely many height-one primes ramify, counted either in `B` or in `A`.

## Main definitions and results

- `AlgebraicNumberTheory.Ramification.heightOnePrimeBelow w`: the height-one prime of `A` below a height-one prime `w` of `B`.
- `finite_ramified_heightOne_primes`: the set of height-one primes `w` of `B` at which `B` is not unramified over `A` (Mathlib's `Algebra.IsUnramifiedAt`) is finite.
- `finite_ramified_base_heightOne_primes`: the set of height-one primes of `A` lying under some ramified height-one prime of `B` is finite.

## Proof

A ramified prime of `B` divides the different ideal (Mathlib's `dvd_differentIdeal_iff`); the different is nonzero, so it has finitely many prime factors. The statement for `A` is the image of that finite set under `heightOnePrimeBelow`.

## Points to watch

- Separability of the fraction-field extension is assumed; in characteristic zero it is automatic, but in general it is a real hypothesis.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/AlgebraicNumberTheory/Ramification/FiniteRamifiedPrimes.lean`: the Lean file is the source byte for byte (SHA-256 `2abbde95975e820df4bc8396e572c81ee5d9d1de086984494b9aebb894c5cf21`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
