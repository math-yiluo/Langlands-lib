# Continuity of the idele norm

Module `Nyll.ClassFieldTheory.AlgebraicNumberTheory.Idele.NormTopology.Continuity`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

Let L/K be a finite extension of number fields. This file proves that the norm map `IdeleGroup.norm K L` from the ideles of L to the ideles of K is continuous for the restricted-product topologies, and bundles it as a continuous homomorphism.

## Main results

- `IdeleGroup.finitePlace_normUnits_mem_integerUnits`: for a finite place W of L over v of K, the local norm from L_W to K_v maps integral units to integral units. The order at v of the norm of x is a multiple of the order of x at W.
- `IdeleGroup.norm_continuous`: `norm K L` is continuous.
- `IdeleGroup.ideleNormContinuousMonoidHom`: the norm as a continuous monoid homomorphism I_L → I_K, with the simp lemma `ideleNormContinuousMonoidHom_apply`.

## Proof

The proof works on an open chart of I_L: arbitrary infinite components together with finite components that are integral units at every place. The chart has the product topology, and the structure map of the restricted product makes it an open subspace.

On the chart, each component of the norm is a finite product of local norms over the places of L above the given place of K (`finiteComponent_norm_eq_prod` and `infiniteComponent_norm_eq_prod`). The finite components stay integral units, by the first result.

Each local norm is continuous. At finite places this comes from `normUnits_continuous_of_finiteDimensional`, once K_v is made a nontrivially normed field. At infinite places the local norm is transported to ℝ or ℂ. When the identification of L_W with ℂ does not fit the one of K_v, it is composed with complex conjugation.

So the norm is continuous on the chart, hence continuous at 1, and therefore continuous everywhere, since it is a homomorphism of topological groups.

## Points to watch

- No Galois hypothesis is needed. The extension must be finite and both fields must be number fields.
- `IdeleGroup.norm` is the library's idele norm, defined in imported files through the norm of the relative idele group. That its component at each place of K is the product of the local norms over the places above it is a theorem, the imported `finiteComponent_norm_eq_prod` and `infiniteComponent_norm_eq_prod`.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/AlgebraicNumberTheory/Idele/NormTopology/Continuity.lean`: the Lean file is the source byte for byte (SHA-256 `3bc3cc53f1cc696a5dd5ca4f11bb1398949f1fd487ef190f3b202aaee2a97437`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
