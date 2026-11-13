# Convergence of the hyperext spectral sequence in Cartan–Eilenberg's Case 1: proof

Author: Worker 22.

This module proves the published proposition
`Langlands.Cohomology.HyperextConvergence.HyperextHalfBoundedConvergenceStatements` of
`Langlands.Cohomology.HyperextConvergence.HalfBoundedStatement`:

```
theorem hyperextHalfBoundedConvergenceStatements_proof :
    HyperextHalfBoundedConvergenceStatements.{v, u} C
```

Here `C` is any category with the instances of the statement module: preadditive, with a zero
object, a shift by `ℤ` through additive functors, pretriangulated and `IsTriangulated`. The
universes `v` and `u` are independent. The theorem keeps every quantifier and bound of the
statement: a t-structure `t`, objects `K` and `B` with `t.IsLE K b` and `t.IsGE B c`, a page
`r` with `2 ≤ r`, and a position `(p, q)` with `p - c + 1 ≤ r` and `q + b + 2 ≤ r`. Nothing else
is assumed; in particular `K` need not be bounded below, and `B` need not lie in the heart.
The theorem is the pair `⟨hyperextHalfBoundedDifferential, hyperextHalfBoundedStablePage⟩` of the
two conjuncts. Only the standard axioms `propext`, `Classical.choice` and `Quot.sound` are used.

## Reused results

The module imports the published proof module `Langlands.Cohomology.HyperextConvergence.Proof`
(Worker 199's proof of the companion `HyperextConvergenceStatements`, for `K` bounded on both
sides) and reuses from it, unchanged:

* `eAddEquiv`: for any spectral object in abelian groups, `E^{n}(i ⟶ j ⟶ k ⟶ l)` is the
  quotient of the image of `H^n(i ⟶ k) ⟶ H^n(i ⟶ l)` by the image of
  `H^n(i ⟶ j) ⟶ H^n(i ⟶ l)`;
* `isZero_H_bot`: if `K` lies in degrees `≤ b`, then `H^n(⊥ ⟶ i)` vanishes for `i ≤ -b`;
* `isZero_page_X_of_lt`: if `K` lies in degrees `≤ b`, then every page vanishes in the rows
  `q < -b`;
* `mem_filtration_iff_exists` and `H_map_twoδ₂Toδ₁_apply`: when `p - n = 1 - m`, the subgroup
  `F^p` of `Hom(K, B⟦n⟧)` is the image of `H^n(⊥ ⟶ m) ⟶ H^n(⊥ ⟶ ⊤)`.

None of these uses a lower bound on `K`.

## Notation

Write `t'` for `opTStructure t` and `X` for `hyperextSpectralObject t K B`. By definition
`X.H n = t'.ω₁ ⋙ (preadditiveYoneda.obj B).shift n`, and the shifted functor is
`preadditiveYoneda.obj (B⟦n⟧)`. So `H^n(i ⟶ j)` is the group of morphisms from
`(τ_{≥ i} τ_{< j} (op K)).unop` to `B⟦n⟧`, the truncations being those of `t'`
(`eTruncGE`, `eTruncLT`).

## The new vanishing lemma (`isZero_H_of_isGE`)

Let `B` lie in degrees `≥ c`, let `D = (i ⟶ j)` be an arrow of `EInt`, and let `m` be an integer
with `m ≤ i` and `n - c < m`. Then `H^n(D)` is zero.

Proof. The object `τ_{≥ i} τ_{< j} (op K)` lies in `t'`-degrees `≥ m`
(`isGE_eTruncGE_obj_obj`), so its `unop` lies in `t`-degrees `≤ -m`
(`opTStructure_isGE_iff`). The object `B⟦n⟧` lies in degrees `≥ c - n`
(`TStructure.isGE_shift`), and `-m < c - n`. By `TStructure.zero` every morphism between them is
zero, so the group is a subsingleton and `AddCommGrpCat.isZero_of_subsingleton` applies.

`isZero_page_X_of_lt_left`: if `p < c`, the object in position `(p, q)` of every page `r ≥ 2`
is zero. Mathlib's `isZero_spectralSequence_page_X_of_isZero_H'` for `coreE₂Cohomological`
reduces this to the vanishing of `H^{p+q}(q ⟶ q + 1)`, which is `isZero_H_of_isGE` with
`m = q`, since `p + q - c < q`.

## Differentials (`hyperextHalfBoundedDifferential`)

Let `r ≥ 2`, `p - c + 1 ≤ r` and `q + b + 2 ≤ r`. If two positions are not related by the shape
`ComplexShape.up' (r, 1 - r)`, the differential between them is zero
(`HomologicalComplex.shape`). Otherwise:

* the differential leaving `(p, q)` ends at `(p', q')` with `q' = q + 1 - r ≤ -b - 1 < -b`, so
  its target is zero (`isZero_page_X_of_lt`);
* the differential entering `(p, q)` starts at `(p', q')` with `p' + r = p`, so
  `p' = p - r ≤ c - 1 < c`, and its source is zero (`isZero_page_X_of_lt_left`).

## Stable pages (`halfBoundedStablePageIso`, `hyperextHalfBoundedStablePage`)

Under the same bounds put `n = p + q`. The isomorphism `halfBoundedStablePageIso` is a composite
of four isomorphisms, as `stablePageIsoOfMem` in the bounded case; only step 3 uses a different
vanishing argument, and no case distinction on `q` is needed.

1. `spectralSequencePageXIso` for `coreE₂Cohomological` identifies the object in position
   `(p, q)` of page `r` with `E^n(q - r + 2 ⟶ q ⟶ q + 1 ⟶ q + r - 1)`.
2. Since `q - r + 2 ≤ -b`, the group `H^{n+1}(⊥ ⟶ q - r + 2)` vanishes (`isZero_H_bot`).
   Mathlib's `isoMapFourδ₁Toδ₀'` (inverted) replaces the first index by `⊥`, giving
   `E^n(⊥ ⟶ q ⟶ q + 1 ⟶ q + r - 1)`.
3. The group `H^{n-1}(q + r - 1 ⟶ ⊤)` vanishes by `isZero_H_of_isGE` with `m = q + r - 1`:
   the condition `n - 1 - c < q + r - 1` is `p - c < r`, that is `p - c + 1 ≤ r`. Mathlib's
   `isoMapFourδ₄Toδ₃'` replaces the last index by `⊤`, giving `E^n(⊥ ⟶ q ⟶ q + 1 ⟶ ⊤)`.
4. `eAddEquiv` with `i = ⊥`, `j = q`, `k = q + 1`, `l = ⊤`, through
   `AddEquiv.toAddCommGrpIso`, identifies this term with `A ⧸ B` for the subgroups `A = F^p`
   and `B = F^{p+1}` of `H^n(⊥ ⟶ ⊤) = Hom(K, B⟦n⟧)`. The image hypotheses come from
   `mem_filtration_iff_exists` with `m = q + 1` for `F^p` (`p - n = -q`) and `m = q` for
   `F^{p+1}` (`p + 1 - n = 1 - q`), together with `H_map_twoδ₂Toδ₁_apply`. The quotient is
   `HyperextAbutment.graded t K B (p + q) p`.

`hyperextHalfBoundedStablePage` packages this isomorphism in `Nonempty`. Positions with
`q < -b` or `p < c` need no separate treatment: all four steps use only the bounds
`2 ≤ r`, `p - c + 1 ≤ r` and `q + b + 2 ≤ r`, so the same composite applies there (both sides
are then zero, but the proof does not use this).

## Relation to the route in the statement Markdown

The proof follows the route of the sections "The stable range" and "Why the statements are
true" of the statement Markdown. Two differences:

* The vanishing in the columns `p < c` is obtained directly from `H^{p+q}(q ⟶ q + 1)`, the
  group that Mathlib's `isZero_spectralSequence_page_X_of_isZero_H'` tests, rather than from the
  subquotient description of `E_r^{p,q}`.
* Step 3 there argues by surjectivity of `H^{n-1}(q + 1 ⟶ l) → H^{n-1}(q + 1 ⟶ ⊤)`; the Lean
  proof instead uses Mathlib's `isoMapFourδ₄Toδ₃'`, whose hypothesis is exactly the vanishing of
  `H^{n-1}(l ⟶ ⊤)` established there. Step 4 uses the abstract quotient description
  `eAddEquiv` of the bounded-case proof instead of the image of
  `Hom(τ_{≥ -q} K, B⟦n⟧) → Hom(τ_{≤ -q} K, B⟦n⟧)`.

## Source

The statement is Cartan–Eilenberg, *Homological Algebra* (1956), Chapter XVII §2 (4) and §3
Case 1, pp. 368–370, in the derived reformulation of the statement module; see its Markdown for
the source comparison. This module adds no mathematical content beyond the proof.
