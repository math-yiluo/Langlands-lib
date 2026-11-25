# Rigidity of group-scheme homomorphisms out of diagonalizable groups

Module `Langlands.GroupScheme.Torus.CompleteLocalDeformation.HomRigidity`, namespace
`Langlands.GroupScheme.CompleteLocalDeformation`. This module translates the bialgebra
rigidity of `Rigidity.lean` and `FiniteRigidity.lean` into a statement about actual group
schemes.

## Statements

Let `R` be a commutative ring and `I` an ideal of `R`. Let `H` and `G` be group schemes over
`Spec R`, with `G.X.left` affine. Write `bc_{R/I}` for the actual base change
`GroupScheme.baseChange (Spec.algebraMap R (R ⧸ I))`.

- `eq_of_baseChange_eq_of_isDiagonalizable I hsep hH hG f g h`. Hypotheses: `R` is
  `I`-adically separated (`hsep : ∀ x, (∀ k, x ∈ I ^ k) → x = 0`), `H` is diagonalizable,
  `bc_{R/I} G` is diagonalizable, and `f g : H ⟶ G` satisfy `bc_{R/I}.map f = bc_{R/I}.map g`.
  Conclusion: `f = g`.
- `eq_of_baseChange_eq_of_le_jacobson`: the same conclusion when `R` is noetherian and
  `I ≤ jacobson ⊥`.
- `eq_of_baseChange_eq_of_finite`: the same conclusion when `R` is an algebra over a
  noetherian local ring `A`, `R` is finite as an `A`-module, and `I` is the extension of the
  maximal ideal of `A` to `R`. Neither `A` nor `R` needs to be complete, and `R` need not be
  local. This is the form used for `B ⊗[A] B` in `CoverDescent.lean`.

Auxiliary results:

- `tensorMap_eq_of_baseChange_eq`: if two `R`-algebra maps `f g : A → B` give equal
  pullbacks of `algSpec` maps along `Spec S → Spec R`, then
  `Algebra.TensorProduct.map (AlgHom.id S S) f = Algebra.TensorProduct.map (AlgHom.id S S) g`.
- `tensorMap_diagonalSourceCoordinateMap_eq`: the same for the coordinate maps
  `diagonalSourceCoordinateMap f` (module `Torus.DiagonalizableSourceCoordinates`) of two
  homomorphisms from the standard diagonalizable group with equal base change along
  `R → S`.
- `diagonalSourceCoordinateMap_sub_mem`: if such homomorphisms have equal base change to
  `R ⧸ I`, then their coordinate maps agree modulo `I • ⊤`.
- `diagonalSource_eq_of_baseChange_eq`: rigidity for the standard diagonalizable source. Here
  cocommutativity of the coordinate bialgebra of `G` modulo `I` is a hypothesis.
- `comul_sub_comm_mem_of_reduction_isDiagonalizable`: the coordinate bialgebra of `G` is
  cocommutative modulo `J` when `bc_{R/J} G` is diagonalizable.

## Proof

Let `π_f` be the coordinate map of `f` from the standard diagonalizable source. By
`diagonalSourceCoordinateMap_spec`, `hopfSpec π_f` is `f` conjugated by the canonical
coordinate isomorphisms. So equal base changes of `f` and `g` give equal base changes of
`hopfSpec π_f` and `hopfSpec π_g`. Their underlying scheme maps are the pullbacks of the
`algSpec` maps. The published `HopfMorphismBaseChange.tensorSpecIso_naturality` identifies
those pullbacks with `Spec` of the tensor maps. Since `Spec.map` is injective, the tensor maps
are equal. Evaluate at `1 ⊗ a` in `(R ⧸ I) ⊗[R] R[M]` and apply `one_tmul_eq_zero_iff`
(from `Lifting.lean`). This gives `π_f a - π_g a ∈ I • ⊤`.

Next, `comul_sub_comm_mem_of_bialgEquiv` (from `FiniteRigidity.lean`) applies to the
presentation `diagonalizableReductionPresentation G I hG` (module `Torus.DiagonalizableReductionCoordinates`). It shows that the coordinate
bialgebra of `G` is cocommutative modulo `I`. Then `eq_of_sub_mem_smul_top` gives
`π_f = π_g`, and `eq_of_diagonalSourceCoordinates_eq` gives `f = g`.

For a general diagonalizable `H`, choose an isomorphism of `H` with a standard diagonalizable
group (through `Diagonalizable.relativeModelIso`). Precompose both maps with it, and cancel
the isomorphism at the end. The noetherian and finite-algebra variants obtain `hsep` from
`eq_zero_of_mem_pow_of_le_jacobson` and `eq_zero_of_mem_map_maximalIdeal_pow`
(`FiniteRigidity.lean`), which rest on Krull's intersection theorem.

## Provenance

This is internal content derived for the descent step of Conrad, *Reductive group schemes*
(2014), Theorem B.3.2(2). Compare SGA 3, Exposé IX, 7.1, where uniqueness on the double
overlap of a finite étale cover is used. The route through coordinate bialgebras and
convolution rigidity is our own.
