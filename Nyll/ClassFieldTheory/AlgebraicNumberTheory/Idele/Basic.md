# The idele group of a number field

Module `Nyll.ClassFieldTheory.AlgebraicNumberTheory.Idele.Basic`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

This file defines the idele group I_K of a number field K as the product of an infinite and a finite part, with component maps, and compares it algebraically with the units of the adele ring.

## Definitions

- `FiniteIdeleGroupOf R F`: for a Dedekind domain R with fraction field F, the restricted product over the height-one primes v of the groups (F_v)ˣ of the adic completions, with respect to the unit groups of their valuation rings. `FiniteIdeleGroup K` is the case R = 𝓞 K.
- `InfiniteIdeleGroup K`: the unit group of Mathlib's infinite adele ring, the product of the archimedean completions.
- `IdeleGroup K`: `InfiniteIdeleGroup K × FiniteIdeleGroup K`.
- Components: `FiniteIdeleGroup.component v`, `InfiniteIdeleGroup.component v`, `IdeleGroup.infiniteComponent v`, `IdeleGroup.finiteComponent v`, each a monoid homomorphism to the units of the completion at v, with simp lemmas.

## Results

- `FiniteIdeleGroup.eventually_mem_localUnits`: a finite idele lies in the local integral units at all but finitely many places.
- `IdeleGroup.finiteEquivFiniteAdeleUnitsOf`, `IdeleGroup.finiteEquivFiniteAdeleUnits`: the finite ideles are isomorphic, as a group, to the units of the finite adele ring.
- `IdeleGroup.equivAdeleRingUnits`: I_K is isomorphic, as a group, to the units of Mathlib's adele ring, with simp lemmas `equivAdeleRingUnits_fst` and `_snd` for its two components.

## Points to watch

- `IdeleGroup` and its finite part are the library's definitions. The finite part is a restricted product of unit groups, so it carries the restricted-product topology, not the topology induced from the finite adele ring.
- The comparisons with adele units are stated as isomorphisms of groups only; the file proves nothing about their continuity. Its comments give the reason: the idele topology is finer than the topology induced from the adele ring.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/AlgebraicNumberTheory/Idele/Basic.lean`: the Lean file is the source byte for byte (SHA-256 `b2a5d714376d896817965523124ca5996eabae11d0e58cf8031695edb008d3fc`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
