# Abstract reciprocity: the totally ramified calculation

Module `Nyll.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.TotallyRamified`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

In abstract class field theory over a group `G` with module `A` (written additively, so a "power" π^k is `k • π`) and valuation `v`, this file carries out the computation behind injectivity of reciprocity for a cyclic totally ramified extension. From an equality of norms it produces, via the class field axiom, an element of the base whose image in the extension has normalized valuation a prescribed k; the step from there to k = 0 is not in this file.

## Results

- `primeNormClass_eq_zero_exists_unit_norm_eq`: let K, L, Σ be finite abstract fields (`FiniteAbstractField G`), L/K finite and totally ramified and Σ/K finite of residue degree 1, with prime elements π_Σ and π_L. If the class of the norm to K of k π_Σ in A_K modulo the norms from A_L is zero, there is a unit w of L such that k π_L + w and k π_Σ have the same norm to K. The proof compares valuations along both towers.
- `valuationAt_extensionFixedRepresentation_action`: for a finite normal extension L/K (`E : FiniteAbstractFieldExtension G` with `hnormal`), the valuation on A_L is invariant under the action of G(L/K).
- `abstractReciprocity_exists_hMinusOne_primitive`: under `hcf : SatisfiesClassFieldAxiom A`, for a cyclic extension with generator σ and elements u, w of A_L with equal norms to K, there is a with σa − a = w − u. It uses the vanishing of Tate H⁻¹ supplied by the axiom.
- `abstractReciprocity_totallyRamified_fixedSource`: given in addition that w is a unit of L and π_L a prime element of L, and t ∈ G(L/K) with k π_Σ = u + k π_L, t fixing π_Σ, and σ and t acting equally on b = k π_L + w, there are a and x ∈ A_K such that x, viewed in A_L, equals b + a − t(a), and its normalized valuation in L is k. The fixedness of b + a − t(a) under σ is the private lemma `abstractReciprocity_fixedCombination`, which uses commutativity of the cyclic group.

## Points to watch

- The two action conditions (t fixes π_Σ; σ and t agree on b) and the relation k π_Σ = u + k π_L are hypotheses of `abstractReciprocity_totallyRamified_fixedSource`, to be supplied by the caller.
- The identification of a reciprocity value with the class of a prime norm is not made here; the file starts from the vanishing of that class.
- The fields, prime elements, unit subgroups and valuations are the library's own notions for abstract class formations.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/AbstractClassFieldTheory/Reciprocity/TotallyRamified.lean`: the Lean file is the source byte for byte (SHA-256 `658db1aa41fe1a0a6392882f580a2ab29b86bca317635e0a37faaf394527d029`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
