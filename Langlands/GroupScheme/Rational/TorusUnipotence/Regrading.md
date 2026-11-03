# Coarsening a weight grading to a `ℤ`-grading

Module `Langlands.GroupScheme.Rational.TorusUnipotence.Regrading`, namespace
`Langlands.GroupScheme.TorusUnipotence`.

The coordinate algebra of `H` is graded by the character lattice `X` of the torus.
`BigCell` and `Rigidity` work with `ℤ`-gradings. This module coarsens an `X`-grading along a
homomorphism `w : X →+ ℤ`; in the application `w` is the pairing with a generic cocharacter. It
then combines `gradedBigCellInjectivity` with `eq_algebraMap_of_lTensor_eq_zero` to obtain the
rigidity hypothesis of `TopWeight` for the coarsened grading.

## Definition

`regrade W w d = ⨆ (χ : X) (_ : w χ = d), W χ`, for a family `W : X → Submodule k M` of
subspaces and `w : X →+ ℤ`. Degree `d` is the sum of the `W χ` with `w χ = d`.

## Statements

*Linear algebra.* Let `M` be a vector space over a field `k` and `X` an additive abelian group.

* `le_regrade`: `W χ ≤ regrade W w d` when `w χ = d`.
* `regrade_le_iff`: `regrade W w d ≤ P` iff `W χ ≤ P` for every `χ` with `w χ = d`.
* `regrade_neg`: `regrade W (-w) d = regrade W w (-d)`.
* `iSupIndep_regrade`, `iSup_regrade`, `isInternal_regrade`: coarsening preserves independence
  and the total sum. So if `W` is independent with `⨆ χ, W χ = ⊤`, the coarsened family is an
  internal direct sum decomposition.
* `regrade_comul`. Let a linear map `Δ : M → M ⊗ M` satisfy
  `Δ (W χ) ⊆ ⨆ α, W α ⊗ W (χ - α)` (as `Submodule.map₂ (TensorProduct.mk k M M)`). Then
  `Δ (regrade W w d) ⊆ ⨆ e, regrade W w e ⊗ regrade W w (d - e)`.

*Algebras.* Let `A` be a commutative `k`-algebra, and let `W` satisfy `W χ * W ψ ≤ W (χ + ψ)`
(`hmul`) and `1 ∈ W 0` (`h1`). Let `ε : A →ₐ[k] k` vanish on `W χ` for `χ ≠ 0` (`hε`).

* `regrade_mul_le`, `gradedMonoid_regrade`: the coarsened family is multiplicative and contains
  `1` in degree `0`.
* `gradedAlgebraRegrade hind htop h1 hmul`: the resulting `GradedAlgebra` structure. Its
  decomposition is chosen from `isInternal_regrade`.
* `regrade_augmentation`: `ε` vanishes in nonzero coarse degrees.
* `regrade_zero_mem_sq`. Suppose every `a ∈ W χ` with `w χ = 0` and `ε a = 0` lies in
  `(ker ε) ^ 2` (`hsq`). Then every `a` of coarse degree `0` with `ε a = 0` lies in `(ker ε) ^ 2`.

*Rigidity.* `exists_eq_smul_one_of_regrade hind htop h1 hmul ε hε Δ hl hr w hsq ha hm`. Let `A`
be a formally smooth Noetherian domain over `k`. Let `W` be independent with sum `⊤`, with `h1`,
`hmul` and `hε` as above. Let `Δ : A →ₐ[k] A ⊗ A` satisfy both counit laws (`hl`, `hr`), and let
`w` satisfy `hsq`. Let `a` have coarse degree `0` and satisfy `rid (m.lTensor A (Δ a)) = 0` for
every functional `m` vanishing in all coarse degrees `≥ 0` (`hm`). Then `a = c • 1` for some
`c : k`.

## Proof

*Linear algebra.* For independence, the sum of the coarse degrees `e ≠ d` is the sum of the
`W χ` with `w χ ≠ d`. That sum is disjoint from the sum of the `W χ` with `w χ = d` by
`iSupIndep.disjoint_biSup_biSup`. The total sum is unchanged because each `W χ` sits in degree
`w χ`. For `regrade_comul`, `regrade_le_iff` reduces to a single `W χ` with `w χ = d`. There
`W α ⊗ W (χ - α)` lies in coarse degrees `w α` and `d - w α`.

*Algebras.* Multiplicativity follows from `Submodule.iSup_mul`, `Submodule.mul_iSup` and `hmul`.
`regrade_augmentation` follows from `regrade_le_iff`: if `w χ = d ≠ 0`, then `χ ≠ 0`. For
`regrade_zero_mem_sq`, show that coarse degree `0` lies in `k · 1 + (ker ε) ^ 2`. For `f ∈ W χ`
with `w χ = 0`, the element `f - ε f` lies in `W χ`: if `χ = 0` because `1 ∈ W 0`, and otherwise
because `ε f = 0`. So `f - ε f` lies in `(ker ε) ^ 2` by `hsq`. Writing `a = c · 1 + z` with
`z ∈ (ker ε) ^ 2`, `ε a = 0` forces `c = 0`.

*Rigidity.* The orientation conventions differ: `TopWeight` uses functionals vanishing in degrees
`≥ 0`, while `Rigidity` uses degrees `≤ 0`. So the proof works with the negated grading
`regrade W (-w)`, made a graded algebra by `gradedAlgebraRegrade`. Its augmentation and
degree-zero hypotheses follow from `regrade_augmentation` and `regrade_zero_mem_sq`, using
`(-w) χ = 0 ↔ w χ = 0`. `gradedBigCellInjectivity` then makes its `bigCellMap` injective. By
`regrade_neg`, `a` has degree `0` for `-w`, and a functional vanishing in `(-w)`-degrees `≤ 0`
vanishes in `w`-degrees `≥ 0`. So `eq_algebraMap_of_lTensor_eq_zero` gives `a = ε a · 1`.

## Provenance

The coarsening of a character grading along a cocharacter is standard: it is the grading by the
weights of a one-parameter subgroup, chosen generic for the finitely many cotangent weights. The
statements here are internal lemmas for the
proof of `Langlands.GroupScheme.RelativeRoot.TorusActionUnipotenceStatement`. No source states
them in this form.
