# Proof of the linear system morphism statement

The theorem `Langlands.AlgebraicGeometry.linearSystemMorphism` proves
`Langlands.AlgebraicGeometry.LinearSystemMorphismStatement.{u}`, for every universe `u`.

Statement. Let `K` be a field, `X` a scheme, `p : X ⟶ Spec K`, `L` a line bundle on `X`, and
`s 0, …, s n` global sections of `L` with no common zero. Then there is
`φ : X ⟶ ProjectiveSpace K n` over `Spec K` such that, with
`σ c = ∑ i, scalarsFromBase p (c i) • s i`:

1. for rational points `x, y`, `x ≫ φ = y ≫ φ` if and only if every `σ c` vanishing at `x`
   vanishes at `y`;
2. for a rational point `x` and a tangent vector `t` at `x`,
   `t ≫ φ = (dualNumberProjection K ≫ x) ≫ φ` if and only if every `σ c` vanishing at `x`
   vanishes along `t`.

This is the morphism to projective space defined by a base-point-free linear system, as used
by Milne in the proof of Theorem 7.1 (pp.10–11 of `milne-abelian-varieties-1986-author-2022`,
recalling Hartshorne, which is cited only through Milne; compare Stacks Project, Constructions of Schemes, Section 27.14 "Invertible sheaves and morphisms into Proj", Lemma 27.14.1, tag 01NJ, in the registered source `stacks-very-ampleness-support-2026-10-29`). The proof below is the implemented
Lean route. It follows the outline of the proof sketch in the statement's Markdown (chart
maps on the loci where `s j` does not vanish, glued; then testing with `s i - α i • s j`),
but compares pulled-back ratios along `T`-points directly instead of writing them as
`α_i + β_i ε`.

## The morphism

`φ` is `LinearSystem.linearSystemMap p hs` (module `LinearSystem.Morphism`), glued from the
point maps of the nonvanishing loci `U_j` of the sections. On `U_j` it sends `X_i / X_j` to
the ratio `s i / s j`. It lies over `Spec K` (`linearSystemMap_toSpec`).

## Auxiliary lemmas in this module

These are in the namespace `Langlands.AlgebraicGeometry.LinearSystem`. The lemmas
`forall_mem_of_mem` and `forall_mem_of_augmentation_comp` used below come from the helper
module `LinearSystem.DualNumberPoints`.

- `exists_vanishesAlong_basisDiff`: for a rational point `x` landing in `U_j`, there are
  `α i ∈ K` such that `s i - α i • s j` vanishes at `x` for every `i`. The ratio
  `s i / s j` at `x` is a function on `Spec K`, hence a scalar `α i`
  (`exists_scalarsFromBase_eq`). Apply `vanishesAlong_linComb_basisDiff_iff`.
- `mem_of_vanishesAlong_basisDiff`: if `y` is a point with values in a field `K'` and every
  `s k - α k • s j` vanishes along `y`, then the image point of `y` lies in `U_j`. Otherwise
  choose `k` with `y` landing in `U_k`. Along `y`, `ratio(s j, s k) = 0` because `s j`
  vanishes at `y` (`vanishesAlong_iff_not_mem`). Then the vanishing of `s k - α k • s j` gives
  `1 - α k · 0 = 0` in `Γ(Spec K', ⊤) ≅ K'`, which is impossible.

## Clause 1 (rational points)

Choose `j` with `x` in `U_j`.

(⇒) Suppose `x ≫ φ = y ≫ φ`. The image of `x` lies in the chart `D₊(X_j)`
(`comp_mem_coordinateOpen`). Hence the image of `y` does too, and `y` lands in `U_j`
(`mem_trivializationOpen_of_comp_mem`). Two points of `U_j` with the same image are cut out
by the same linear combinations (`vanishesAlong_linComb_iff_of_comp_eq`).

(⇐) Take the `α` of `exists_vanishesAlong_basisDiff` for `x`. By hypothesis every
`s k - α k • s j` also vanishes at `y`, so `y` lands in `U_j`
(`mem_of_vanishesAlong_basisDiff`). By `vanishesAlong_linComb_basisDiff_iff`, the ratios
`s i / s j` at `x` and at `y` are both the scalar `α i`. Both points lie over the identity of
`Spec K`, so `comp_eq_of_sectionRatio_eq` gives `x ≫ φ = y ≫ φ`.

## Clause 2 (tangent vectors)

Choose `j` with `x` in `U_j`. Then `t` and the constant tangent vector
`x' = dualNumberProjection K ≫ x` land in `U_j`. Both lie over `dualNumberProjection K`.

(⇒) If `t ≫ φ = x' ≫ φ`, then `σ c` vanishes along `t` if and only if it vanishes along
`x'` (`vanishesAlong_linComb_iff_of_comp_eq`). If `σ c` vanishes at `x`, it vanishes along
the composite `x'` (`vanishesAlong_comp`), hence along `t`.

(⇐) Take `α` for `x` as before. By hypothesis every `s i - α i • s j` vanishes along `t`.
By `vanishesAlong_comp` it also vanishes along `x'`. So the ratios along `t` and along `x'`
are both the image of `α i` (`vanishesAlong_linComb_basisDiff_iff`), and
`comp_eq_of_sectionRatio_eq` gives `t ≫ φ = x' ≫ φ`.

## Remarks on the statement

The clauses are stated with one-directional implications on the right. In clause 2 this is
equivalent to the bi-implication, because vanishing along `t` implies vanishing at
`x = dualNumberAugmentation K ≫ t`. In clause 1 the left side is symmetric in `x` and `y`.
Neither equivalence is used in the proof. The theorem
uses no hypothesis on `X` beyond the absence of common zeros; `n = 0` and the empty scheme are
included.
