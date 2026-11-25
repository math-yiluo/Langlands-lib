# Finite normalization for monogenic subalgebras

Module `StacksFrontier.RingTheory.Nagata.MonogenicN1`, an extract of the file of the same path of the Lean library AxiomMath/Stacks. The origin of the file and what the extract leaves out are given at the end of this page.

A subalgebra of the fraction field of a normal Nagata domain has finite normalization if it is generated over the domain by one element. The file proves this through the maximal localizations of the monogenic algebra.

`MonogenicN1.module_finite_integralClosure` takes a normal Nagata domain `A`, a fraction field `K`, and an `A`-algebra domain `C` with a compatible injective map into `K`. If `Algebra.adjoin A {y} = ⊤` for some `y` in `C`, it proves `Module.Finite C (integralClosure C K)`. The helper `MonogenicN1.isN1_of_forall_isN1_atPrime` applies the local-to-global criterion to a Noetherian localization of `C` at nonzerodivisors, using the denominator of `y` to obtain a normal principal open. Other helpers transport N-1 along ring isomorphisms and between models of a localization at a prime, and show that the Nagata property passes to quotients.

At a maximal ideal of `C`, localize `A` at the contracted prime to obtain a monic polynomial vanishing on the residue of `y`. The argument in `MonogenicN1.isN1_atPrime_of_exists_monic` splits this polynomial in a finite extension of `K`, replaces the base by its finite integral closure there, and shifts the generator by a root at each maximal ideal over the original one. Finiteness then descends from the resulting finite extension.

The local step `MonogenicN1.isN1_atPrime_of_mem` handles a nonzero generator in the prime with every base element outside that prime already a unit. Quotienting by the generator gives the base modulo the contraction of the fractional ideal `yA`. The associated primes of this quotient are minimal, with regular height-one localizations and analytically unramified prime quotients. The criterion for analytic unramifiedness then gives N-1 for the local ring. The version `MonogenicN1.isN1_atPrime_of_mem'` uses the reduction to a local base and includes the zero generator.

This is the monogenic N-1 step of Tag 0334, with the generator in the base fraction field and `A`, `C`, and `K` in one universe. `C` can be any presentation of the subalgebra with the stated scalar tower and injection. The implementation notes of the module docstring write the N-1 predicate `StacksIsN1` without the prefix `Stacks` and still name a lemma passing from finiteness in `K` to N-1, which is not in the file.

References include Tag 0333 for the local-to-global criterion, Tag 032K and Tag 032T for the finite extension, and Tag 031T, Tag 0330, Tag 0331, and Tag 032Y for the local step. EGA IV 7.9.1 is cited for the height-one regularity lemma.

## References to EGA and SGA

| Source | Place | Declaration | Note |
| --- | --- | --- | --- |
| EGA | IV 7.9.1 | `isRegularLocalRing_of_height_eq_one` | partial |

## Origin of the file

Extracted from the Lean library AxiomMath/Stacks (https://github.com/AxiomMath/Stacks), commit `c496df0d9beea9deaeabcea8492605f9a0a2313b`, file `StacksFrontier/RingTheory/Nagata/MonogenicN1.lean`. That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the extract:

- Of the 30 declarations of the source file 29 are kept. The 1 left out are not needed by the results for which the extract is made: `MonogenicN1.isN1_of_module_finite`.
- The import lines are those that the kept text needs.
- The library's Lean options that differ from Lean's defaults are set at the top of the file (`autoImplicit false`, `maxSynthPendingDepth 3`).
- The import of the library's own attribute modules is replaced by `Mathlib.Tactic.CrossRefAttribute`.
- One reference to EGA or SGA, written in the source as an attribute of that library, is taken out of the Lean text and listed above.
