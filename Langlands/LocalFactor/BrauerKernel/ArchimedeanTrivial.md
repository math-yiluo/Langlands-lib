# Archimedean components of reciprocity characters trivial on `C_E`

Author: Worker 5093. This is a supporting unit for task
`92a3d086-a5ad-476f-9fd9-aa9d4eaa3778`, which must prove
`Langlands.LocalFactor.NonabelianBrauer.KernelCompatibilityStatement`. In Deligne's global argument
(1973, proof of Lemma 4.12) the global field `K'` is totally real, and the characters attached to
the generators are inflated from a finite Galois group. Their archimedean components must be
known in order to compare the archimedean factors of the global functional equations. This unit
shows that a Hecke character whose reciprocity character on the relative Weil group is trivial
on the idele classes of the top field has trivial archimedean components below every unramified
infinite place. The argument is elementary given the published transfer formula; it has no
separate literature source.

Everything is in `Langlands.LocalFactor.NonabelianBrauer`; the topology of `Gal(E/F)` is the
discrete one, as in the published relative Weil modules.

## Results

- `exists_localUnitNorm_eq`: if the infinite place `w` of `E` lies over `v` of `F` and is
  unramified, every unit of `F_v` is the local norm of a unit of `E_w`: the local degree is `1`,
  so the norm of the image of `y` is `y` (`InfiniteExtension.localNorm_algebraMap`).
- `isUnramified_of_isReal`: a real infinite place is unramified (Mathlib's
  `not_isUnramified_iff`).
- `infiniteComponent_eq_one_of_reciprocity_inclusion`: let `Θ` be a Hecke character of `F` with
  `continuousReciprocityCharacter c F E Θ` trivial on the image of `C_E` in `W_{E/F}`. If an
  infinite place `w` of `E` above `v` is unramified, then the archimedean component of `Θ` at
  `v` is trivial. Proof: a unit `y` of `F_v` is the local norm of some `y'` (first item); the
  reciprocity character at the image of the idele class of `y'` is `Θ(transfer)⁻¹`, and the transfer
  of an element of `C_E` is its idele-class norm (`transfer_inclusion`), which is the class of `y`
  (`ideleClassNorm_ofCompletion`).
- `infiniteComponent_eq_one_of_isTotallyReal`: if `E` is totally real, the conclusion holds at every
  infinite place of `F` (every place has a place above it, `exists_infinitePlace_above`, and it is
  real).
