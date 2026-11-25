# The maximal-unramified norm-residue symbol

Module `Nyll.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.MaximalUnramifiedSymbol`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

In abstract class field theory over a group `G` with a topology, with degree map `D` and valuation `v`, the maximal unramified Galois group of K is the quotient of K by its inertia, `K ⧸ D.fieldInertiaWithin K`, identified with ℤ̂ by the normalized degree. This file builds the restriction maps from it to finite unramified quotients and defines the symbol a ↦ φ_K to the power v_K(a).

## Definitions and results

- `maximalUnramifiedExtensionRestriction`, `finiteUnramifiedRestriction`: restriction to G(L/K) for an unramified Galois extension L/K (the first does not need L/K finite). They send the Frobenius `D.frobenius K` to the arithmetic Frobenius `unramifiedFrobenius` (`maximalUnramifiedRestriction_frobenius`, `finiteUnramifiedRestriction_frobenius`).
- `finiteUnramifiedDegreeEquiv`: for finite unramified L/K, the normalized degree modulo [L : K] gives G(L/K) ≃ ℤ/[L : K]; it is compatible with restriction (`finiteUnramifiedDegreeEquiv_restriction`) and sends Frobenius to 1.
- `maximalUnramifiedFrobeniusPower D K z`: the profinite power φ_K^z for z ∈ ℤ̂, through the degree isomorphism.
- `maximalUnramifiedNormResidueSymbol v K`: the additive map a ↦ φ_K to the power v_K(a) on the fixed elements A_K; `maximalUnramifiedNormResidue_eq_frobeniusPower` states this by definition, and `maximalUnramifiedNormResidue_degree` recovers the valuation.
- `maximalUnramifiedNormResidueSymbol_finiteReciprocity_of_generator`: if an additive map r from G(L/K) to A_K modulo the norms from A_L sends Frobenius to the class of the chosen prime element, then r of the restricted symbol of a is the class of a. `maximalUnramifiedNormResidueSymbol_finiteRestriction_of_generator` restates this as: the restricted symbol is the inverse of the equivalence `unramifiedReciprocity_equiv_of_generator` built from r.

## Proofs

`canonicalUnramifiedReciprocity_degree_of_generator` checks on the Frobenius generator that such an r intertwines the valuation modulo [L : K] with the degree isomorphism; injectivity of the valuation on the unramified norm quotient then gives the compatibility.

## Points to watch

- The last two results take `hAxiom : v.SatisfiesUnramifiedUnitCohomology D` and keep the reciprocity map r as an explicit argument with its Frobenius value as hypothesis, rather than using the finite reciprocity map itself.
- The restriction and degree constructions take `K : FiniteResidueAbstractField D`; the symbol and the results about it take `K : FiniteAbstractField G`. `canonicalUnramifiedReciprocity_degree_of_generator` and the last two results also assume `G` a compact Hausdorff topological group.
- `maximalUnramifiedNormResidueSymbol` is the library's own definition by the valuation; the file comment calls it a candidate until its compatibility with finite norm-residue symbols is proved.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/AbstractClassFieldTheory/Reciprocity/MaximalUnramifiedSymbol.lean`: the Lean file is the source byte for byte (SHA-256 `a28ff799183fe20c3579e3e681672a4892feaee7d70de2b095a1c80328495893`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
