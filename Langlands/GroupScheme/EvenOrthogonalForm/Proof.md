# Tits's realization of the forms of `SO_{2n}` as `O(q)⁰`

## Statement

`Langlands.GroupScheme.Quaternionic.evenSpecialOrthogonalForm` proves the
Library proposition `EvenSpecialOrthogonalFormStatement` at every universe
`u`, with no extra hypothesis:

```
theorem evenSpecialOrthogonalForm : EvenSpecialOrthogonalFormStatement.{u}
```

Let `K` be a field, `n ≥ 4`, and `H` an affine group scheme of locally
finite type over `K` whose base change to the separable closure `K^s` is
isomorphic to the split `SO_{2n}` (the identity component of
`OrthogonalMatrix.groupScheme (Fin n) K^s`). Then there are a central
division `K`-algebra `D` of degree `d`, `m` with `m d = 2n`, an orthogonal
involution `σ` of the first kind on `D` (`dim Sym(σ) = d(d+1)/2`) and a
nondegenerate `σ`-quadratic form `q` on `D^m`. Its isometry group `O(q)` is
smooth and `H ≅ O(q)⁰` over `K`. There is no restriction on the
characteristic (2 and finite fields included), `n = 4` is included, and
outer forms are covered.

## Proof

The theorem is the composite of two results proved in this development:

1. `EvenOrthogonalForm.evenSpecialOrthogonalForm_of_specialOrthogonalAutomorphism`
   (`EvenOrthogonalForm/Reduction`) derives the statement from
   `SpecialOrthogonalAutomorphismStatement`. In outline: the isomorphism
   over `K^s` descends to a finite Galois extension `N / K`. The automorphism
   statement turns its Galois twists into conjugations by similitudes `g_σ`.
   These define a twisted Galois action on `M_{2n}(N)`. Its fixed algebra
   `A` is a finite-dimensional central simple `K`-algebra with an
   involution `τ` (descended from `x ↦ J xᵀ J`) and a base point `a₀` with
   `a₀ + τ a₀ = 1` (a trace average of `p = diag(1, 0)`).
   `orthogonalInvolutionHermitian` gives `D`, `σ` and a hermitian matrix
   `H_m` with `(A, τ)` isomorphic to `M_m(D)` with the adjoint involution of
   `H_m`. Then `q = [φ_A(a₀) H_m]`, and the isometry cut of `(A, τ, a₀)` is
   isomorphic to `O(q)`. Comparing with the split group over `N` and
   descending gives smoothness of `O(q)` and `H ≅ O(q)⁰`. The Markdown files
   of `EvenOrthogonalForm/*` and `OrthogonalInnerForm/*` give each step.
2. `OrthogonalMatrix.specialOrthogonalAutomorphism`
   (`OrthogonalMatrix/Automorphism/Proof`) proves
   `SpecialOrthogonalAutomorphismStatement`: every automorphism of the split
   `SO_{2n}`, `n ≥ 2`, is conjugation by a similitude.

No other statement is assumed: the theorem has no hypotheses. In
particular it does not use the type-`D` spin or Kneser–Tits statements
that the task excludes.

## Provenance

Derived; see `EvenOrthogonalForm/Reduction.md` (KMRT §29.D, §29.F, §5.B;
Tits 1968, §2.2) and `OrthogonalMatrix/Automorphism/Proof.md` (KMRT
(26.15), §26.B).
