# The rank of relative differentials at a point of a fibre of relative dimension `n`

Author: Worker 50.

Helper module for the proof of
`Langlands.GroupScheme.ReducedBaseConnectedFibreSmoothStatement` (SGA 3, Exposé VI_B,
Corollaire 4.4). It computes the dimension of the fibre of the module of Kähler
differentials at a point whose fibre over the base is smooth of relative dimension `n`.

## Declarations

- `Langlands.GroupScheme.ReducedBaseSmooth.finrank_tensor_kaehler_of_locally`: let `k`, `F`
  be commutative rings and `K` a field (all in one universe), with `k → F` and `F → K`. If
  `algebraMap k F` satisfies `RingHom.Locally (RingHom.IsStandardSmoothOfRelativeDimension n)`,
  then `Module.finrank K (K ⊗[F] Ω[F⁄k]) = n`.
- `Langlands.GroupScheme.ReducedBaseSmooth.finrank_residueField_tensor_kaehler_eq`: let `B` be
  an `R`-algebra, `p` a prime ideal of `R` and `Q` a prime ideal of `B` lying over `p`. If
  `Spec (κ(p) ⊗[R] B) → Spec κ(p)` (the map `Spec.map` of `algebraMap p.ResidueField
  (p.Fiber B)`) is `SmoothOfRelativeDimension n`, then
  `Module.finrank κ(Q) (κ(Q) ⊗[B] Ω[B⁄R]) = n`.

In words: if the fibre of `Spec B → Spec R` over `p` is smooth of relative dimension `n` over
`κ(p)`, then `Ω_{B/R} ⊗_B κ(Q)` is an `n`-dimensional `κ(Q)`-vector space. This is a standard
consequence of the base-change property of differentials and of the rank of differentials of
a standard smooth algebra; the precise formulation is internal to this proof.

## Proofs

`finrank_tensor_kaehler_of_locally`. The locality hypothesis gives a finite family `s ⊆ F`
generating the unit ideal such that `k → F[1/t]` is standard smooth of relative dimension `n`
for every `t ∈ s`. Some `t ∈ s` has nonzero image in `K`; otherwise the unit ideal would lie
in the kernel of `F → K`. Then `F → K` factors through `F_t = Localization.Away t`
(`IsLocalization.Away.lift`). Mathlib's
`Algebra.IsStandardSmoothOfRelativeDimension.rank_kaehlerDifferential` gives
`finrank F_t Ω[F_t⁄k] = n`. Since `F → F_t` is a localization, it is formally étale, and
`KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale` identifies `F_t ⊗[F] Ω[F⁄k]` with
`Ω[F_t⁄k]`. Combining with `AlgebraTensorModule.cancelBaseChange` gives
`K ⊗[F] Ω[F⁄k] ≃ K ⊗[F_t] Ω[F_t⁄k]`, and `Module.finrank_baseChange` gives dimension `n`.

`finrank_residueField_tensor_kaehler_eq`. Write `F = κ(p) ⊗[R] B`. Mathlib's
`HasRingHomProperty.Spec_iff` for `SmoothOfRelativeDimension n` turns the hypothesis into
`RingHom.Locally (RingHom.IsStandardSmoothOfRelativeDimension n) (algebraMap κ(p) F)`. The
map `F → κ(Q)` is `Algebra.TensorProduct.lift` of `Ideal.ResidueField.mapₐ p Q` (well
defined since `Q` lies over `p`) and of `B → κ(Q)`; it is compatible with `B → F`,
`b ↦ 1 ⊗ b`. The first lemma gives `finrank κ(Q) (κ(Q) ⊗[F] Ω[F⁄κ(p)]) = n`. Finally
`κ(Q) ⊗[B] Ω[B⁄R] ≃ κ(Q) ⊗[F] (F ⊗[B] Ω[B⁄R]) ≃ κ(Q) ⊗[F] Ω[F⁄κ(p)]`, by
`AlgebraTensorModule.cancelBaseChange` and by Mathlib's
`KaehlerDifferential.tensorKaehlerEquiv` for the pushout square `R → κ(p)`, `R → B`,
`F = κ(p) ⊗[R] B` (`TensorProduct.isPushout`).
