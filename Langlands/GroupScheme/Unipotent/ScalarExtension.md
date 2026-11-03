# Unipotent coordinate bialgebras under extension of scalars

Worker 1395 wrote this module. It proves that the internal predicate `OneMemStable` from
`Langlands.GroupScheme.Unipotent.HopfFixed` survives extension of scalars along any field
extension `k → K`. This is the algebraic core of Milne, *Algebraic Groups* (2017), Corollary 14.9
(forward direction), which Milne proves via coconnected Hopf algebras. This module uses a
different, fixed-vector route.

## Contents

* `tensor_ext_left`: let `t ∈ M ⊗[k] N` over a field `k`. If `lid (g.rTensor N t) = 0` for every
  functional `g` on `M`, then `t = 0`. Proof: expand `t` in a basis of `M` with
  `TensorProduct.equivFinsuppOfBasisLeft`, whose coefficients are the contractions with the
  coordinate functionals.
* `rightAct_baseChange`: the `K`-bialgebra `K ⊗[k] B` carries Mathlib's tensor-product bialgebra
  structure. On it, right translation by the scalar extension `g.baseChange K` of a `k`-functional
  `g` is `(rightAct g).lTensor K`. Checked on pure tensors.
* `OneMemStable.baseChange`: `OneMemStable k B` implies `OneMemStable K (K ⊗[k] B)`. Let `V` be a
  nonzero finite-dimensional `K`-subspace stable under all `K`-linear right translations. Regard
  `K ⊗[k] B` as a `k`-module with:
  * operators `T g = (rightAct g).lTensor K` for `k`-functionals `g` on `B`; they preserve `V` by
    `rightAct_baseChange`;
  * `k`-linear projections `π l = lid ∘ l.rTensor B` for `k`-functionals `l` on `K`; they satisfy
    `π l ∘ T g = rightAct g ∘ π l` and are jointly injective by `tensor_ext_left`.

  `V` need not be finite-dimensional over `k`, so pick `v₀ ≠ 0` in `V` and write it as a finite
  sum of pure tensors. Let `L ⊆ K` be the `k`-span of the first factors, and let
  `U = regularSpan` of the second factors, which is finite-dimensional and stable. Then
  `W = image (L ⊗ U → K ⊗ B) ∩ V` is a nonzero finite-dimensional `T`-stable `k`-subspace.
  `exists_invariant` gives a nonzero `w ∈ W` with `T g w = g 1 • w`. Each `π l w` is then
  right-translation invariant, so `π l w = l c • 1` with `c = (id ⊗ ε) w ∈ K`, by
  `eq_counit_smul_one_of_invariant`. Joint injectivity gives `w = c ⊗ 1` with `c ≠ 0`, so
  `1 = c⁻¹ • w ∈ V`.
