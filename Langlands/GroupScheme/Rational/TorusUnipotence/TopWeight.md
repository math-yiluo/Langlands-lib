# Fixed vectors of matrix corepresentations of a graded coalgebra

Module `Langlands.GroupScheme.Rational.TorusUnipotence.TopWeight`, namespace
`Langlands.GroupScheme.TorusUnipotence`.

This module is the pure-algebra part of the proof of
`Langlands.GroupScheme.RelativeRoot.TorusActionUnipotenceStatement`. It does not mention group
schemes. It works with a coalgebra `B` over a field `K` that is graded by a linearly ordered
abelian group `Γ`. In the application, `B` is the coordinate ring of `H` graded by the
characters of the split torus `S`, `Γ` is `ℤ` (or `X(S)` with a compatible order), and `e = 1`.

## Main results

`exists_fixed_vector_of_graded`. Let `K` be a field and `B` a `K`-coalgebra. Let
`𝒜 : Γ → Submodule K B` be an internal direct sum decomposition (`DirectSum.IsInternal 𝒜`) indexed
by a linearly ordered abelian group `Γ`. Assume:

* `hΔ`: the comultiplication is graded, i.e. `comul (𝒜 χ) ⊆ ∑_α 𝒜 α ⊗ 𝒜 (χ - α)`;
* `e ∈ 𝒜 0` is grouplike: `comul e = e ⊗ e` and `counit e = 1`;
* `hrigid` (top-weight rigidity): if `a ∈ 𝒜 0` and `rightAct m a = 0` for every functional `m`
  that vanishes on `𝒜 χ` for all `χ ≥ 0`, then `a ∈ K • e`.

Here `rightAct m b = ∑ m (b₂) • b₁` for `comul b = ∑ b₁ ⊗ b₂`. This is
`Langlands.GroupScheme.AffineLinearEmbedding.rightAct`, i.e. `(id ⊗ m) ∘ comul`.

Then every matrix corepresentation `M : Matrix n n B` with `n` finite and nonempty, i.e.
`comul (M i j) = ∑ l, M i l ⊗ M l j` and `counit (M i j) = δ i j`, has a nonzero fixed vector
`v : n → K`: `∑ j, v j • M i j = v i • e` for every `i`.

`exists_fixed_vector_of_graded'` is the same statement for a module `B` without a `Coalgebra`
instance. Here the comultiplication `Δ` and counit `ε` are explicit linear maps satisfying the
three coalgebra axioms, stated in the form of Mathlib's `Coalgebra` fields (`coassoc`,
`rTensor_counit_comp_comul`, `lTensor_counit_comp_comul`). Right translation is written out as
`TensorProduct.rid K B (m.lTensor B (Δ a))`. The proof installs the corresponding `Coalgebra`
instance and applies `exists_fixed_vector_of_graded`.

## Auxiliary declarations

* `gradedProj 𝒜 χ`: the projection `B → 𝒜 χ ⊆ B`. Its lemmas cover membership, idempotence,
  vanishing on other degrees, finite support (`exists_gradedProj_eq_zero`) and the reconstruction
  `sum_gradedProj`.
* `gradedProjPi`, `rightActPi`: the coordinatewise projection and right translation on `n → B`.
  `IsGradedPi 𝒜 W` means `W` is closed under every `gradedProjPi 𝒜 n χ`. `IsStablePi W` means `W`
  is closed under every `rightActPi n m`, i.e. `W` is a subcomodule of the comodule `n → B`.
* `map_comul_eq_of_mem`: two linear maps on `B ⊗ B` that agree on `𝒜 α ⊗ 𝒜 (χ - α)` for every
  `α` agree on `comul a` for every `a ∈ 𝒜 χ`.
* `gradedProj_rightAct` (G2): for `a ∈ 𝒜 N`,
  `gradedProj χ (rightAct m a) = rightAct (m ∘ gradedProj (N - χ)) a`.
* `leftAct_mem_zero` (G1): for `a ∈ 𝒜 N` and `φ` vanishing on every `𝒜 χ` with `χ ≠ N`,
  `leftAct φ a ∈ 𝒜 0`.
* `gradedProjPi_mem_of_top` (core top-weight lemma). Let `W` be stable and `W'` graded and
  stable, and suppose every degree `> N` component of `W` lies in `W'`. Then for `x ∈ W`
  homogeneous of degree `N`, the degree `N` part of `rightActPi l x - l e • x` lies in `W'`.
* `exists_relative_coinvariant`. If `W' < W` are graded stable subspaces of `n → B` with `W`
  finite-dimensional, then some homogeneous `x ∈ W \ W'` has `rightActPi l x - l e • x ∈ W'` for
  every `l`.
* `exists_coinvariant`. A nonzero stable subspace `V` of a finite-dimensional graded stable `W₀`
  contains a nonzero `v` with `rightActPi l v = l e • v` for every `l`.
* `rightAct_matrix_coeff`: `rightAct m (M i j) = ∑ l, m (M l j) • M i l`.
* `eq_counit_smul_of_rightAct`: if `rightAct l b = l e • b` for all `l`, then
  `b = counit b • e`.

## Proof

*Core lemma.* Let `z` be the degree `N` part of `rightActPi l x - l e • x`, and suppose
`z ∉ W'`. Then `z` lies outside `U = gradedProjPi N ⁻¹ W'`, so there is a functional `φ` on
`n → B` that vanishes on `U` with `φ z ≠ 0`. `U` contains `W'` and every vector with zero degree
`N` part, so each coordinate functional `φ_i` vanishes on `𝒜 χ` for `χ ≠ N`. Put
`a = ∑ i, leftAct φ_i (x i)`. By G1, `a ∈ 𝒜 0`, and `g a = φ (rightActPi g x)` for every `g`
(`apply_leftAct`). Let `m` kill `𝒜 χ` for all `χ ≥ 0`. By G2, the degree `χ ≤ N` parts of
`rightActPi m x` vanish, and its degree `χ > N` parts lie in `W'` by hypothesis. So
`rightActPi m x ∈ W'`, and since `W'` is stable, `g (rightAct m a) = φ (rightActPi g (rightActPi m x)) = 0`
for all `g`. Hence `rightAct m a = 0`, and `hrigid` gives `a = c • e`. Applying this with
`g = counit` gives `φ x = c`. Then
`φ z = φ (rightActPi l x) - l e * φ x = l (c • e) - l e * c = 0`, a contradiction.

*Relative lemma*, by strong induction on `finrank W`. Let `N` be the largest degree in which
some component of `W` is not in `W'`. Then the core lemma applies. Let `G` be the span of
`rightActPi l x - l e • x` over homogeneous `x ∈ W` of degree `N` and all `l`. By G2, `G` is
graded. It is stable by coassociativity (`rightAct_rightAct`), and `G ≤ W`. By the core lemma,
degree `N` parts of `G` lie in `W'`. If `G ≤ W'`, the degree `N` component of a witness `y ∈ W`
works. Otherwise `C = W' ⊔ G` satisfies `W' < C < W`, because the degree `N` component of the
witness lies in `W` but not in `C`. Apply the induction hypothesis to `(C, W')`.

*Coinvariants.* Choose `W' ≤ W₀` graded and stable with `V ⊓ W' = ⊥` and of maximal dimension
(`Nat.findGreatest`). Then `W' < W₀`, and the relative lemma gives a homogeneous `x`.
`W'' = W' ⊔ K x` is graded and stable, so by maximality `V ⊓ W''` contains some `v ≠ 0`. For every
`l`, `rightActPi l v - l e • v ∈ V ⊓ W' = ⊥`.

*Main theorem.* `𝒰 ⊆ B` is the span of all `rightAct g (gradedProj χ (M i j))`. It is graded
(G2), stable (`rightAct_rightAct`) and contains every `M i j` (`sum_gradedProj`,
`rightAct_counit`). It is finite-dimensional: only finitely many `χ` occur, and each homogeneous
component has a finitely generated space of right translates (`exists_fg_rightAct`). Take
`W₀ = 𝒰ⁿ ⊆ n → B` (the range of `𝒰.subtype.compLeft n`) and `V` the span of the columns of `M`.
`V` is stable by `rightAct_matrix_coeff`, and `V ≠ ⊥` because `counit (M i i) = 1`.
`exists_coinvariant` gives `v = ∑ j, c j • col j ≠ 0` with `rightAct l (v i) = l e • v i`. By
`eq_counit_smul_of_rightAct`, `v i = counit (v i) • e`, and
`counit (v i) = ∑ j, c j * δ i j = c i`. So `c` is the required fixed vector.

## Provenance

The statements are internal interfaces for the proof of `TorusActionUnipotenceStatement`, so
none is quoted from a source. The target is the claim made in the proof of Conrad–Gabber–Prasad,
*Pseudo-reductive groups* (2nd ed.), Prop. 2.3.11, p. 82. The claim is that a smooth connected
affine group with a torus action whose Lie algebra has only nontrivial weights is unipotent. CGP
argue with maximal tori of the semidirect product. This module supports a different route that
uses no maximal tori: a graded, coalgebraic top-weight induction on comodules. The relative
top-weight induction and the `hrigid` interface are this module's own formulation. `hrigid` is
where the geometric input enters (smoothness and connectedness of `H`, and no zero weight on the
Lie algebra). It is proved separately for the coordinate ring.
