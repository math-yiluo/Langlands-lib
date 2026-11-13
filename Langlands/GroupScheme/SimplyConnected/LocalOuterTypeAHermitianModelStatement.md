# Local outer forms of type A are Hermitian models with a hyperbolic plane

This module states the proposition
`Langlands.GroupScheme.LocalOuterTypeAHermitianModelStatement` and supplies no
proof of it.

## Statement

Fix a universe `u`. For every field `K : Type u` with
`[ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]` (Mathlib's
nonarchimedean local field), every group scheme
`G : GroupScheme (Spec (CommRingCat.of K))` with `[IsAffineHom G.X.hom]` and
`[LocallyOfFiniteType G.X.hom]`, every actual index datum `d : TitsIndexData G`
and every `n : ℕ`, assume

1. `IsSimplyConnected G` and `IsAbsolutelyAlmostSimple G`;
2. the index has type `A_n`: there is `e : d.Vertex ≃ Fin n` with
   `d.cartan a b = CartanMatrix.A n (e a) (e b)` for all simple vertices `a b`;
3. the actual star action is nontrivial: some
   `σ : SeparableClosure K ≃ₐ[K] SeparableClosure K` and some vertex `a` have
   `d.star σ a ≠ a`.

Then there exist a field `L : Type u` with `Algebra K L`,
`Algebra.IsQuadraticExtension K L` and `Algebra.IsSeparable K L` (a quadratic
Galois extension of `K`), a diagonal Hermitian form
`H : HermitianRoot.DiagonalForm (SU3Root.fieldInvolution K L) (Fin (n - 1))`,
units `w : Fin (n - 1) → Lˣ` with `(w i : L) = H.weight i` for every `i`, and a
group-scheme isomorphism

`G ≅ HermitianRoot.SchemeModel.groupScheme K L H w hw`.

The model `HermitianRoot.SchemeModel.groupScheme K L H w hw` is the published
affine group scheme over `K` whose points on every test scheme `T` over `Spec K`
are exactly the determinant-one invertible matrices, indexed by
`Unit ⊕ (Fin (n - 1) ⊕ Unit)`, over `L ⊗[K] Γ(T, O_T)` that preserve the
Hermitian form (for the conjugation of `L/K` on the first tensor factor) with
Gram matrix `HermitianRoot.gram H`: the first and last coordinates form a
hyperbolic pair with pairing `1`, and the middle `n - 1` coordinates are
orthogonal to them with diagonal entries `-H.weight i`. The weights are
fixed by the conjugation (they lie in `K`) and are units, so the form is a
nondegenerate Hermitian form on `L^(n + 1)` that contains a hyperbolic plane.

No anisotropy of `G` and no anisotropy of `H` is assumed or asserted, and there
is no restriction on the characteristic of `K` or of its residue field.

## Remarks on the hypotheses

- Hypothesis 3 is how "outer type" is expressed on actual index data: the group
  is an outer form exactly when the star action of the absolute Galois group on
  the simple roots is nontrivial.
- For `n ≤ 1` the hypotheses are contradictory (a set with at most one element
  has no map moving a point), so the statement has content only for `n ≥ 2`.
  Hence `Fin (n - 1)` has `n - 1 ≥ 1` elements whenever the statement applies,
  and the model has `n + 1` coordinates, matching type `A_n`.

## Provenance

Derived. T. Kaletha and G. Prasad, *Bruhat–Tits Theory: A New Approach*,
Cambridge University Press, 2023 (source
`kaletha-prasad-2023-bruhat-tits-new-approach`), §10.3, the paragraph after
Remark 10.3.2, printed pp. 392–393 / PDF pp. 423–424, states: if `k` is a
nonarchimedean local field and `G` is a simply connected absolutely almost
simple `k`-group of outer type `A_n`, then "there is a quadratic Galois
extension `ℓ` of `k` and a non-degenerate hermitian form `h` on `ℓ^(n+1)` such
that `G = SU(h)`" (using that no noncommutative finite-dimensional division
algebra with center `ℓ` has an involution of the second kind with fixed field
`k`, [Sch85, Chapter 10, Theorem 2.2(ii)]), and that for `n ≥ 2` the
`(2n + 2)`-dimensional quadratic form `x ↦ h(x, x)` over `k` is isotropic, so
`h` represents zero nontrivially.

The present statement records this conclusion in the form of a Library model.
The passage from the book's `SU(h)` to the model uses two standard facts about
Hermitian forms for a separable quadratic extension `L/K`, valid in every
characteristic: a nondegenerate isotropic Hermitian form splits off a
hyperbolic plane (an isotropic vector `x` and a vector `y` with `h(x, y) = 1`
can be modified to a hyperbolic pair), and a nondegenerate Hermitian form has
an orthogonal basis (if `h(x, x) = 0` for all `x`, then the trace of
`h(x, y)` vanishes for all `x, y`, so `h = 0` because the trace form of
`L/K` is nondegenerate). The diagonal entries of such a basis are nonzero
elements of `K`; the model's middle weights are their negatives. The rank
`n - 1` of the middle part is `(n + 1) - 2`.

## Use

`Langlands.GroupScheme.localAnisotropicTypeAInner_of_hermitianModel`, in
`Langlands.GroupScheme.SimplyConnected.LocalAnisotropicTypeAInnerReduction`,
derives `Langlands.GroupScheme.LocalAnisotropicTypeAInnerStatement` from this
proposition.
