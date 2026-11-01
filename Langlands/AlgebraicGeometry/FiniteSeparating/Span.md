# `K`-linear spans of finite sets of sections

This helper module is used in the proof of
`Langlands.AlgebraicGeometry.FiniteSeparatingSectionsStatement`. It is internal: it is not a
Library statement and has no literature source of its own. It provides the bookkeeping for
the linear system spanned by a finite set of global sections, as in Milne's condition that a
linear system separates points and tangent vectors (proof of Theorem 7.1, pp.10–11 of
`milne-abelian-varieties-1986-author-2022`). Everything is in the namespace
`Langlands.AlgebraicGeometry.FiniteSeparating`.

Throughout, `K` is a field, `p : X ⟶ Spec K`, `L` is a line bundle on `X`, and `S` is a
finite set (`Finset`) of global sections of `L`. A scalar `a ∈ K` acts on sections through
Library's `Scheme.Modules.scalarsFromBase p a ∈ Γ(X, ⊤)`.

## The span of a finite set

- `InSpan p L S σ`: there is `c : GlobalSections L.obj → K` with
  `σ = ∑ s ∈ S, scalarsFromBase p (c s) • s`. The coefficient function is defined on all
  sections, but only its values on `S` matter.
- `InSpan.mono`: the span grows with `S`. Extend the coefficients by `0` outside the smaller
  set (`Finset.sum_subset`).
- `inSpan_of_mem`: every element of `S` is in its span (coefficient `1` at `σ`, `0`
  elsewhere, `Finset.sum_eq_single`).

## Enumerating a finite set

The target statement asks for a family `s : Fin (n + 1) → GlobalSections L.obj`. The set `S`
can be empty, so the family puts the zero section first.

- `enum S : Fin (S.card + 1) → GlobalSections L.obj` is `Fin.cons 0 e`, where `e` lists the
  elements of `S` through `S.equivFin`. `enum_zero` and `enum_succ` compute it.
- `exists_enum_eq`: every element of `S` occurs in `enum S`.
- `sum_eq_sum_equivFin`: a sum over `S` is the sum over `Fin S.card` through
  `S.equivFin.symm`.
- `sum_enum`: in a linear combination of `enum S`, the zero section contributes nothing, so
  only the coefficients at `i.succ` remain.
- `inSpan_iff`: `InSpan p L S σ` holds exactly when
  `σ = ∑ i, scalarsFromBase p (a i) • enum S i` for some `a : Fin (S.card + 1) → K`. This is
  how the span of `S` is compared with the combinations of a family indexed by `Fin (n + 1)`
  in the Library statements. From `c`, take `a = Fin.cons 0 (c ∘ e)`. From `a`, take
  `c s = a (S.equivFin s).succ` for `s ∈ S` and `0` otherwise.

## Separation at a point

- `SeparatesAt p L S x`, for a rational point `x : Spec K ⟶ X`, states two conditions:
  1. for every rational point `y ≠ x` there is `σ` in the span of `S` that vanishes at `x`
     but not at `y`;
  2. for every nonzero tangent vector `t` at `x` (Library's `IsNonzeroTangentVectorAt p x t`)
     there is `σ` in the span of `S` that vanishes at `x` but not along `t`.

  Vanishing is Library's `VanishesAlong` (the pulled-back section is zero).
- `SeparatesAt.mono`: separation is preserved when `S` grows, by `InSpan.mono`.
