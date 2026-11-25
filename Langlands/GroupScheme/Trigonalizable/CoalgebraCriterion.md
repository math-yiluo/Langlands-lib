# A coalgebra criterion for stable lines

This internal module proves a purely algebraic fact used for
[`SubgroupQuotientProof`](SubgroupQuotientProof.md). Let `B` be a bialgebra over a field. If
every nonzero finite matrix corepresentation of `B` has a stable line, then the same holds for
every quotient of `B` by a surjective bialgebra map. Geometrically, such a surjection is the
coordinate map of a closed subgroup (see Background). Everything lives in the namespace
`Langlands.GroupScheme.CoalgebraTrigonalizable`. The ambient data are a field `k`, a ring `B`
with `[Bialgebra k B]`, and a second ring `C` with `[Bialgebra k C]`. No commutativity is
assumed, and the universes are arbitrary.

The module reuses these published declarations:
- `CoalgebraUnipotence.IsCoefficientMatrix`, which says
  `Δ(aᵢⱼ) = ∑ₗ aᵢₗ ⊗ aₗⱼ` and `ε(aᵢⱼ) = δᵢⱼ`.
- `CoalgebraUnipotence.coefficientVector a v i = ∑ j, v j • a i j`, together with its lemmas
  `counit_coefficientVector` and `rightAct_coefficientVector`.
- From `AffineLinearEmbedding`: the right translation
  `rightAct f b = (id ⊗ f)(Δ b)` and the left translation `leftAct`, their composition
  lemmas, `apply_leftAct`, `tensor_ext`, and `exists_matrix_coefficients`. The last one says
  that every finite subset of `B` lies in the span of the entries of some coefficient matrix.
- From Mathlib: `IsGroupLikeElem`, its image under bialgebra maps, and the linear independence
  of group-like elements (`linearIndepOn_isGroupLikeElem`).

## Definitions

- `IsMatrixTrigonalizable k B` holds when, for every `n > 0` and every coefficient matrix
  `a : Matrix (Fin n) (Fin n) B`, there are `v : Fin n → k` with `v ≠ 0` and `c : B` such that
  `∑ j, v j • a i j = v i • c` for every row `i`. It has the same shape as the published
  `CoalgebraUnipotence.IsMatrixUnipotent`, except that the right-hand side `v i • 1` is
  replaced by `v i • c` for an unknown `c`.
- `groupLikeLevel k B : ℕ → Submodule k B` starts at level `0 = ⊥`. Level `n + 1` is the common
  preimage of level `n` under every `rightAct f` whose functional `f : Module.Dual k B`
  vanishes on all group-like elements. This adapts the published
  `CoalgebraUnipotence.reducedLevel`, which uses the functionals with `f 1 = 0`.
- `IsGroupLikeExhausted k B` says that every element of `B` lies in some level.

These are derived definitions with no literature counterpart. Their only role is the proof in
this module.

## Results

- `mem_groupLikeLevel_zero` and `mem_groupLikeLevel_succ` unfold the levels.
  `groupLikeLevel_le_succ` and `groupLikeLevel_mono` show that the levels increase.
- `rightAct_of_isGroupLikeElem`: `rightAct f g = f g • g` for every group-like `g`.
- `rightAct_mem_groupLikeLevel`: every right translation preserves every level. By
  `rightAct_rightAct`, `rightAct f (rightAct g b) = rightAct (f ∘ₗ rightAct g) b`, and
  `f ∘ₗ rightAct g` vanishes on group-like elements whenever `f` does, by the previous item.
- `map_mem_groupLikeLevel` and `isGroupLikeExhausted_of_surjective`: a bialgebra map
  `q : B →ₐc[k] C` sends level `n` into level `n`. The reason is that `f ∘ q` vanishes on the
  group-likes of `B` whenever `f` vanishes on those of `C`, and `q` commutes with right
  translations. So exhaustion passes to the target of a surjective bialgebra map.
- `isGroupLikeElem_of_stableLine`: the multiplier `c` of a stable line of a coefficient matrix
  is group-like. Apply the counit and the comultiplication to `∑ j, v j • a i j = v i • c` at
  a row with `v i ≠ 0`.
- `exists_stableLine_of_forall_dual`: suppose `v ≠ 0` and every functional vanishing on all
  group-likes kills every coefficient `xⱼ = ∑ l, v l • a j l`. Then the matrix has a stable
  line. By duality for vector spaces (`Submodule.exists_dual_map_eq_bot_of_notMem`), every `xⱼ` lies
  in the span `U` of the group-like elements. These form a basis of `U`. Extending a
  coordinate functional `φ_g` of this basis to `B` by a linear retraction onto `U` gives
  `rightAct φ_g u = φ_g u • g` for all `u ∈ U`. Some `φ_g` is nonzero on `x_{i₀}`, because
  `ε(x_{i₀}) = v i₀ ≠ 0`. The vector `w j = φ_g (xⱼ)` together with `c = g` is then a stable
  line, by `rightAct_coefficientVector`.
- `isMatrixTrigonalizable_of_isGroupLikeExhausted`: under exhaustion, take the least level `m`
  that contains all coefficients `xⱼ` of some nonzero `v`. Then `m = m' + 1`, since level `0`
  would force `v = 0` via the counit. A functional vanishing on the group-likes that is nonzero
  on some `xⱼ` would give a new vector `j ↦ f (xⱼ)`, and its coefficients would lie in level
  `m'`. This contradicts minimality, so the previous item applies.
- `exists_stable_mod_of_isMatrixTrigonalizable`: let `W ⊆ B` be stable under right
  translations, and let `q : W → V` be a surjection onto a nonzero finite-dimensional space
  whose kernel is translation-stable. Choose a basis of `V`, a section of `q` and a retraction
  of `W`. Left translations by the resulting coordinate functionals form a coefficient matrix
  `M`. A stable line of `M`, whose multiplier is group-like, yields `w ∈ W` with `q w ≠ 0` such
  that `q (rightAct f w) = 0` for every `f` vanishing on the group-likes.
- `exists_groupLikeLevel_containing_finite_stable`: a finite-dimensional translation-stable
  subspace `W` lies in a single level. The increasing chain of levels intersected with `W`
  stabilizes, at `n` say. If it stopped below `W`, the previous item applied to `W` modulo
  level `n` would produce an element of level `n + 1` that is not in level `n`.
- `isGroupLikeExhausted_of_isMatrixTrigonalizable`: every `b` lies in the span `W` of the
  entries of a coefficient matrix (`exists_matrix_coefficients`). This span is finite
  dimensional and translation-stable, so the previous item applies.
- `IsMatrixTrigonalizable.of_surjective`: for a surjective bialgebra map `q : B →ₐc[k] C`,
  `IsMatrixTrigonalizable k B` implies `IsMatrixTrigonalizable k C`. Pass to exhaustion,
  transport it along `q`, and return.

## Background

The conclusion is the coalgebraic content of the closed-subgroup clause of Milne, *Algebraic
Groups* (2017), Corollary 16.3, p.325 (source ID `milne-2017-algebraic-groups`): closed
subgroups of trigonalizable groups are trigonalizable. A closed immersion `H → G` of affine
group schemes induces a surjective bialgebra map `O(G) → O(H)` on coordinate rings, and
[`SubgroupQuotientProof`](SubgroupQuotientProof.md) applies
`IsMatrixTrigonalizable.of_surjective` to that map. The group-quotient clause of
the corollary goes the other way: a faithfully flat quotient `G → Q` induces an injective map
`O(Q) → O(G)`. It is not proved in this module, but by descending the stable-line equation
along that injection in [`MatrixCriterion`](MatrixCriterion.md)
(`MatrixRepresentation.isStableLine_restrict_iff` and `IsTrigonalizable.of_flat_surjective`).
Milne's proof uses faithful representations. The route here does not. It generalizes the
Library's proof for unipotent groups (`CoalgebraUnipotence`) by replacing the functionals with
`f 1 = 0` by the functionals vanishing on all group-like elements.
