# The étale equivalence relation of the Galois-twisted line

Author: Worker 105.

This is support for Conrad's Example 5.13 (printed p.20). It contains no statement from the
paper.

## Points of affine schemes

`toSpec` and `ofSpec` identify morphisms `T ⟶ Spec R` with ring maps `R →+* Γ(T, ⊤)`. They are
inverse (`toSpec_ofSpec`, `ofSpec_toSpec`), `ofSpec` is injective, and `ofSpec_comp` computes
composition with `Spec.map f`.

## The relation

- `lineScheme K'` is `Spec K'[X]`.
- `relationScheme K'` is `Spec (K'[X] × K'[X, 1/X])`.
- `tMap K'` and `sMap D` are the spectra of `tStar` and `sStar D`.

`relation D` is a Library `EtaleEquivalenceRelation`. Its fields are proved as follows.

- **Joint monomorphism.** By `hom_ext` on ring maps out of the relation ring.
- **Reflexivity.** Through the first factor.
- **Symmetry.** Through `swapStar D`.
- **Transitivity.** Through `relHom`, `pairIdem_trans` and `isUnit_pairUnit_trans`.
- **Étaleness of `tMap`.** The spectrum of the product is the disjoint union of the two spectra
  (`coprodSpec`, `coprodOpenCover`). On these pieces `tMap` is the identity and a localization,
  and étaleness is checked on that open cover. `sMap` is `tMap` composed with the automorphism
  `Spec swapStar`.

`lineBase` is the structure map `Spec K'[X] → Spec K`. Both projections have the same composite
with it (`tMap_lineBase`).
