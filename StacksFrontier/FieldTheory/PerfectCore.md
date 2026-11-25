# The largest perfect subfield

Module `StacksFrontier.FieldTheory.PerfectCore`, an extract of the file of the same path of the Lean library AxiomMath/Stacks. The origin of the file and what the extract leaves out are given at the end of this page.

For a field F of exponential characteristic p, the perfect core consists of the elements admitting pⁿ-th roots in F for every n. The file constructs this subfield and transports the residue-field hypothesis of Epp's theorem along a square of fields whose upper map is surjective.

## The perfect core

`perfectCore F p` is the intersection of the images of the iterated Frobenius. The membership tests `mem_perfectCore_iff` and `mem_perfectCore_iff_forall_one_le` quantify over all n and positive n, respectively. The instances `perfectCore.perfectRing` and `perfectCore.perfectField` follow because injectivity of Frobenius puts the p-th root of a core element back in the core. The lemma `mem_perfectCore_of_perfectRing` puts the image of any perfect field of the same exponential characteristic in the core, so the core is the largest perfect subfield. By `mem_perfectCore_ringEquiv_iff`, core membership is invariant under ring isomorphisms. An element outside the core has a last stage admitting a root, as witnessed by `exists_pow_eq_and_not_pow_of_notMem_perfectCore`.

## A square of fields

In a commutative square k ⟶ l ⟶ L and k ⟶ K ⟶ L with l ⟶ L surjective, `isSeparable_of_mem_perfectCore_of_surjective` deduces from the condition that every element of the core of l is separable over k that every element of the core of L is separable over K. The surjective map is an isomorphism, so a core element of L comes from a core element of l, and separability over k passes to K along the tower.

The core is a subfield of F itself. In characteristic zero the parameter is p = 1 and the core is all of F.

The module docstring also announces results that the file does not contain: algebraic closedness of the core of a separably closed field, with its criterion by roots of separable polynomials, and the behaviour of the core under separable extensions.

The references are Epp's *Elimination of wild ramification* and Tag 09F9.

## Origin of the file

Extracted from the Lean library AxiomMath/Stacks (https://github.com/AxiomMath/Stacks), commit `c496df0d9beea9deaeabcea8492605f9a0a2313b`, file `StacksFrontier/FieldTheory/PerfectCore.lean`. That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the extract:

- Of the 26 declarations of the source file 10 are kept. The 16 left out are not needed by the results for which the extract is made; `licenses/Stacks/STX-MANIFEST.tsv.md` lists them.
- The import lines are those that the kept text needs.
- The library's Lean options that differ from Lean's defaults are set at the top of the file (`autoImplicit false`, `maxSynthPendingDepth 3`).
