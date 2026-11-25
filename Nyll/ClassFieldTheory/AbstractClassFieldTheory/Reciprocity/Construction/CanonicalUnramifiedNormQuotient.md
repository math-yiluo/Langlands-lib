# The valuation isomorphism for unramified norm quotients

Module `Nyll.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Construction.CanonicalUnramifiedNormQuotient`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

Let `v` be a henselian valuation on a `ℤ`-representation `A` of `G` with value group `Z ⊆ ℤ̂`, and `L | K` a finite unramified Galois extension of degree `n` of abstract fields finite over the base. The file shows that the normalized valuation `v_K` reduced mod `n` induces an isomorphism `A_K / N(L/K)(A_L) ≃ ℤ/n`. The reduction used is the canonical one inherited from `Z ⊆ ℤ̂`, not an arbitrary isomorphism `Z/nZ ≃ ℤ/n`.

## Main definitions and results

- `canonicalValueReduction`, `canonicalValueQuotientHom` and `canonicalValueQuotientEquiv`: reduction mod `n` on `Z` and on `Z/nZ`; the first sends `1` to `1` and both are surjective.
- `canonicalUnramifiedValuationHom`: `a ↦ v_K(a) mod n` on `A_K`.
- `finiteNormSubgroup_le_canonicalUnramifiedValuationHom_ker`: if `L | K` is unramified, norms have valuation `0` mod `n`.
- `canonicalUnramifiedNormQuotientValuation`: the induced map `A_K / N(L/K)(A_L) → ℤ/n`, surjective by `canonicalUnramifiedNormQuotientValuation_surjective`.
- `canonicalUnramifiedNormQuotientValuation_injective`: for normal `G_L` and unramified `L | K`, the map is injective, given the hypothesis `hAxiom`.
- `canonicalUnramifiedNormQuotientEquiv`: the resulting isomorphism `A_K / N(L/K)(A_L) ≃ ℤ/n`.

## Proofs

Norms have valuation divisible by `n` by the norm–valuation formula with `f(L/K) = n`. For injectivity: if `v_K(a) = n z`, pick `b` with `v_L(b) = z`; then `a − N(b)` is a unit. The extension is cyclic, since an unramified extension has a generator, and vanishing of degree-zero Tate cohomology of the units makes this unit a norm of a unit. So `a` is a norm.

## Points to watch

- Injectivity, hence the isomorphism, takes as a hypothesis `hAxiom : SatisfiesUnramifiedUnitCohomology D v` from an imported file. It is used as the statement that, for every finite unramified cyclic extension, the Tate groups of the units vanish in degrees `0` and `−1`. The file does not prove it.
- Surjectivity and the containment of norms in the kernel need only unramifiedness; normality is used only for injectivity.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/AbstractClassFieldTheory/Reciprocity/Construction/CanonicalUnramifiedNormQuotient.lean`: the Lean file is the source byte for byte (SHA-256 `76ebc40ae9a83ca69177cf3d300ebdede3800c476c86a9ea0c0b9f0d05a45a44`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
