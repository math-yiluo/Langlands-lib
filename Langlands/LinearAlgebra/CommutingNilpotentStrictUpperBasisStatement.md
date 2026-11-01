# A common strictly upper triangular basis for commuting nilpotent endomorphisms

This pair states a generic linear-algebra fact. Every family of pairwise
commuting nilpotent endomorphisms of a finite-dimensional vector space over an
arbitrary field has one basis in which all of their matrices are strictly upper
triangular at once. The declaration
`Langlands.CommutingNilpotentStrictUpperBasisStatement.{uK,uV,uI}` is a
proposition (a `Prop`-valued `def`). The pair does not prove it.

## The statement

The universes `uK`, `uV` and `uI` are independent: the field, the carrier and
the index type may live in different universes. The proposition quantifies over

- a field `K : Type uK`;
- a `K`-vector space `V : Type uV` (an additive commutative group with a
  `Module K V` structure) that is finite-dimensional, `[FiniteDimensional K V]`;
- an index type `I : Type uI`;
- a family `N : I → Module.End K V` of `K`-linear endomorphisms of `V`.

It has exactly two hypotheses:

- `∀ s t, Commute (N s) (N t)`: the supplied endomorphisms commute pairwise, that
  is, `N s ∘ N t = N t ∘ N s` in the ring `Module.End K V`, whose multiplication
  is composition;
- `∀ t, IsNilpotent (N t)`: each `N t` has some power equal to `0`. The exponent
  may depend on `t`; no uniform bound is supplied.

The conclusion is that there exists a basis
`b : Module.Basis (Fin (Module.finrank K V)) K V` such that

`∀ (t : I) (i j : Fin (Module.finrank K V)), j ≤ i → b.repr (N t (b j)) i = 0`.

The basis is indexed by `0, 1, …, n - 1`, where `n = Module.finrank K V` is the
dimension of `V`, ordered as natural numbers. `b.repr w i` is the `i`-th
coordinate of a vector `w` in the basis `b`.

### Matrix convention

The vector `b.repr (N t (b j))` is the `j`-th column of the matrix of `N t` in
`b`, so `b.repr (N t (b j)) i` is the entry in row `i` and column `j`. Mathlib's
`LinearMap.toMatrix_apply` gives exactly
`LinearMap.toMatrix b b (N t) i j = b.repr (N t (b j)) i`. The conclusion
therefore says that, for every `t`, the entries of `LinearMap.toMatrix b b (N t)`
on the diagonal (`i = j`) and below it (`j < i`) vanish. Only entries with
`i < j`, strictly above the diagonal, may be nonzero. Equivalently, `N t (b j)`
lies in the span of the `b i` with `i < j`. Thus `N t (b 0) = 0`, and each `N t`
maps the span of `b 0, …, b j` into the span of `b 0, …, b (j - 1)`.

One basis serves every member of the family simultaneously. The basis is part of
the existential conclusion. The statement assumes no common flag, triangular
basis or triangularizability predicate, and it supplies no chosen basis.

## Boundary cases and absent hypotheses

- **Empty index type.** If `I` is empty, both hypotheses and the conclusion's
  condition on `t` are vacuous, and any basis indexed by
  `Fin (Module.finrank K V)` works. The case is retained.
- **Infinite index type.** `I` may be infinite, of any cardinality and in any
  universe. Nothing restricts the family to a finite or finitely generated one.
- **Zero vector space.** If `V = 0`, then `Module.finrank K V = 0`, the basis is
  the empty family indexed by `Fin 0`, and the condition on `i` and `j` is
  vacuous. The case is retained; the statement assumes neither `Nontrivial V` nor
  positive dimension.
- **Fields.** `K` is an arbitrary field. There is no algebraic-closedness,
  characteristic or infinitude assumption. Nilpotent endomorphisms have only the
  eigenvalue `0`, so no extension of scalars is needed.

There is no hypothesis on the nilpotence exponents and no condition beyond the
pairwise commutation of the actual endomorphisms `N s` and `N t` and the
nilpotence of each one.

## Provenance and role in Renard C.III

This statement is an internal, derived algebraic tool. It is not a quotation of
a theorem stated at this generality in the literature it serves.

The governing source is David Renard, *Représentations des groupes réductifs
p-adiques*, French version dated 9 July 2026, registered as
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`. Appendix C.III,
"Représentations de Z^d", is on printed pages 279–280 (PDF pages 285–286). It
considers pairwise commuting invertible endomorphisms `u_1, …, u_d` of a
finite-dimensional complex vector space and proves that matrix coefficients of
the resulting representation of `Z^d` are finite sums of characters times
polynomials. On printed page 280 the proof says "Choisissons une base de
triangularisation commune des `u_1, …, u_d`" so that the matrices of the `U(n)`
are block diagonal, with upper triangular blocks `A_j(n)` whose diagonal entries
are `χ_j(n)`. It then writes `A_j(e_k) = z_k^(j) (Id + N_k^(j))`, where the
`N_k^(j)` are "des matrices triangulaires supérieures strictes (donc
nilpotentes), commutant deux à deux".

The source does not prove that such a common basis exists. On a block where each
`u_k` acts with the single eigenvalue `z_k^(j)`, the operators
`z_k^(j)⁻¹ u_k - Id` are pairwise commuting and nilpotent. Applied to these
operators on that block, the present statement yields a common basis in which
each `N_k^(j)` is strictly upper triangular, hence each block is upper triangular
with diagonal entries `z_k^(j)`. The statement is formulated over an arbitrary
field and for an arbitrary index type because the argument uses neither the
complex numbers nor the finiteness of the family. This generality is internal;
it claims no stronger source theorem.

The supplementary errata for the 2010 edition, registered as
`renard-2010-corrections-complements`, SHA256
`fdf3c88716c294c451c1f6fad67f6b99c95dae670aae0b8ad191ab0a96e69863`, PDF pages
18–19, were checked. Their only C.III entry (old printed page 322, line −4)
adds parentheses to the product `A_j(n) = ∏_i (z_i^(j) (Id + N_i^(j)))^(n_i)`;
the governing 2026 text already has them. No erratum concerns the common
triangular basis.

## Scope

This pair supplies only the proposition. It does not prove it. It also does not
state any of the following:

- the decomposition of `V` into common generalized-weight blocks;
- the source-facing common block basis for the actual commuting invertible
  tuple;
- the normalized nilpotent parts `N_k^(j)` on actual blocks;
- the binomial expansion or the multivariable matrix-coefficient factorization.

These remain obligations of the parent Renard program and of its separate tasks.

A possible proof route, not implemented here, is as follows. The published
theorem `Langlands.DualEigenfunctional.exists_ne_zero_forall_apply_eq_zero`
provides a common nonzero kernel vector for a commuting nilpotent family over any
field. Applying it to the dual maps gives a nonzero functional killed by every
transpose. Its kernel is a common invariant hyperplane containing every range of
`N t`. Induct on the dimension and append a vector outside this hyperplane with
Mathlib's `Module.Basis.mkFinSnoc`.
