# Direct-sum decompositions from finitely supported coefficient maps

This module proves a general linear-algebra criterion for internal direct sums,
needed to show that a torus weight decomposition of a Lie algebra is direct. It
depends only on Mathlib.

Fix a semiring `R`, an `R`-module `V`, a type `ι` with decidable equality, a
family of submodules `W : ι → Submodule R V`, and an `R`-linear map
`p : V →ₗ[R] (ι →₀ V)`. Read `p v i` as the "`i`-th coefficient" of `v`. All
three results use some of the following hypotheses:

- `hmem : ∀ v i, p v i ∈ W i`: every coefficient lies in its summand;
- `hdiag : ∀ i (v : W i), p v = Finsupp.single i v`: on `W i`, `p` returns the
  element itself in slot `i` and zero in every other slot;
- `hsum : ∀ v, (p v).sum (fun _ x => x) = v`: the finitely many nonzero
  coefficients add up to `v`.

## Declarations

- `finsuppCoeff_coeAddMonoidHom W p hdiag x i`: for `x : ⨁ i, W i`, the `i`-th
  coefficient of the sum `DirectSum.coeAddMonoidHom W x` is `x i`. It needs only
  `hdiag`. The proof is by `DirectSum.induction_on`: zero is trivial; for
  `of j w`, `hdiag` gives `Finsupp.single j w`, whose `i`-th entry agrees with
  `(of j w) i`; additivity follows from linearity of `p`.
- `finsuppDecomposition W p hmem hdiag hsum : DirectSum.Decomposition W` (a
  `def`, marked `@[instance_reducible]` and not declared an instance). It sends
  `v` to `∑ i ∈ (p v).support, DirectSum.of _ i ⟨p v i, hmem v i⟩`. Applying
  `coeAddMonoidHom` to this family returns `(p v).sum (fun _ x => x)`, which is
  `v` by `hsum`. This is `left_inv`. For `right_inv`, take `x : ⨁ i, W i`. The
  family built from `coeAddMonoidHom W x` has entry
  `p (coeAddMonoidHom W x) i` in slot `i`, and that entry equals `x i` by
  `finsuppCoeff_coeAddMonoidHom`. The two families are compared slot by slot
  with `DirectSum.ext`.
- `coe_finsuppDecomposition_decompose'_apply`: the `i`-th component of `v` under
  this decomposition, viewed in `V`, is `p v i`.
- `isInternal_of_finsupp W p hmem hdiag hsum : DirectSum.IsInternal W`: if a
  coefficient map satisfies the three hypotheses, then `V` is the internal
  direct sum of the `W i`. It is Mathlib's `DirectSum.Decomposition.isInternal`
  applied to `finsuppDecomposition`.

## Provenance

This is internal infrastructure. Its content is the standard fact that a
compatible family of projections with finite support splits a module into a
direct sum. Equivalently, the canonical map `⨁ i, W i → V` is bijective because
the coefficient map is a two-sided inverse. Mathlib's `DirectSum.Decomposition`
API is phrased with a map `V → ⨁ i, W i`. This module supplies the form in which
coefficients are produced as a finitely supported function. Worker 339 asked for
this interface for the weight-decomposition proof in task 425af515. There, `p`
is given by the coefficients of the coaction of the coordinate ring of a split
torus, written in the character basis (compare Milne, *Algebraic Groups*,
Theorem 12.12, Example 12.15 and Definition 12.16). This module does not depend on that
application.
