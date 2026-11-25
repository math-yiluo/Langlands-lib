# Extensions unramified at all finite primes, in towers

Module `Nyll.ClassFieldTheory.AlgebraicNumberTheory.NumberField.FiniteUnramifiedTower`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

This file defines when an extension of number fields is unramified at every finite prime and proves the usual tower properties.

## Main definitions and results

- `IsUnramifiedAtFinitePlaces K L`: for every height-one prime `P` of `𝓞 L`, Mathlib's `Algebra.IsUnramifiedAt (𝓞 K) P` holds, that is, the localization of `𝓞 L` at `P` is formally unramified over `𝓞 K`.
- `IsUnramifiedAtFinitePlaces.refl`: `K/K` has this property.
- For a tower `k ⊆ K ⊆ F` of number fields:
  - `trans`: if `K/k` and `F/K` are unramified at finite primes, so is `F/k`;
  - `top`: if `F/k` is, so is `F/K`;
  - `bot`: if `F/k` is, so is `K/k`.

## Proof

For `trans` and `bot`, the hypotheses give ramification index `1` (Mathlib's `Ideal.ramificationIdx_eq_one`), ramification indices multiply in towers (`Ideal.ramificationIdx_tower`), and Mathlib's criterion `Ideal.ramificationIdx_eq_one_iff` turns index `1` back into unramifiedness; that criterion needs the residue field of the base prime to be perfect, which holds because it is finite. For `bot`, a prime of `𝓞 F` above the given prime of `𝓞 K` is chosen. `top` is Mathlib's `Algebra.IsUnramifiedAt.of_restrictScalars`. Finiteness of rings of integers as modules and the prime below a given prime come from the library.

## Points to watch

- The definition is phrased with primes of the top field: it asks each prime of `𝓞 L` to be unramified over `𝓞 K`. Infinite places are not involved; the combined notion with infinite places is a separate definition, `IsEverywhereUnramified`.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/AlgebraicNumberTheory/NumberField/FiniteUnramifiedTower.lean`: the Lean file is the source byte for byte (SHA-256 `badf2f9f2158efa5a691b3cfc0989746ba140c4ccf2d39eac87d7645276897b9`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
