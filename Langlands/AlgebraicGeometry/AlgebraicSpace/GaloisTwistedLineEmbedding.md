# The relation of the Galois-twisted line is an affine immersion

Author: Worker 105.

This is support for Conrad's Example 5.13 (printed p.20). Conrad notes that the diagonal is
affine and an immersion. This module proves the ring-theoretic core of that claim.

## The ring map

`tensorHom D : K'[X] ⊗_K K'[X] → K'[X] × K'[X, 1/X]` sends `a ⊗ b` to `tStar a · sStar b`
(`tensorHom_tmul`). Its composites with the two inclusions are `tStar` and `sStar`.

## Surjectivity after one localization

- `secondIdem D` is an element of the tensor product with image the idempotent `(0, 1)`
  (`tensorHom_secondIdem`). It is
  `(C θ ⊗ 1 − 1 ⊗ C θ) · (C (θ − σθ)⁻¹ ⊗ 1)`.
- `unitElem D = (1 − secondIdem) + secondIdem · (X ⊗ 1)` maps to `(1, X)`, a unit
  (`tensorHom_unitElem`, `isUnit_tensorHom_unitElem`).
- `tensorHom` therefore factors through the localization at `unitElem` (`locHom D`), and
  `locHom D` is surjective (`locHom_surjective`).

## The geometric conclusion

- `Spec tensorHom` is a closed immersion into the basic open `D(unitElem)` followed by that open
  immersion. So it is an immersion (`isImmersion_specTensorHom`), and it is affine as a map of
  affine schemes (`isAffineHom_specTensorHom`).
- `prodLift_left_eq` identifies the morphism `prod.lift (tOver D) (sOver D) : R → U ×_K U` over
  `Spec K`, up to the isomorphisms `Over.prodLeftIsoPullback` and `pullbackSpecIso`, with
  `Spec tensorHom`.
- Hence `prod.lift (tOver D) (sOver D)` is an immersion and affine (`isImmersion_prodLift`,
  `isAffineHom_prodLift`).
