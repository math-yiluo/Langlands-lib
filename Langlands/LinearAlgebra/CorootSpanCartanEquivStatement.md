# Based root data with spanning coroots are determined by their Cartan matrix: statement

This module defines the proposition
`Langlands.LinearAlgebra.CorootSpanCartanEquivStatement` (universe parameter `u`). It
is a statement only. The module supplies no proof. It is a prerequisite of Task 5703
(simply connected groups of inner type `A_n` as reduced-norm-one groups), where it
compares the root datum of a simply connected group of type `A_n` with that of
`SL_{n+1}`.

## Statement

Let `ι`, `M`, `N`, `ι'`, `M'`, `N'` be types in `Type u` with `ι` and `ι'` finite and
`M`, `N`, `M'`, `N'` additive commutative groups. Let `P : RootDatum ι M N` and
`Q : RootDatum ι' M' N'` be reduced root data (Mathlib's `RootDatum`: a root pairing
over `ℤ` with weight lattice `M` and coweight lattice `N`). Let `b : P.Base` and
`c : Q.Base` be bases. Assume:

- the coroots of `P` span `N` over `ℤ` (`P.corootSpan ℤ = ⊤`), and the coroots of `Q`
  span `N'` (`Q.corootSpan ℤ = ⊤`);
- `e : b.support ≃ c.support` is a bijection of simple roots that preserves all simple
  pairings: `Q.pairing (e i) (e j) = P.pairing i j` for all simple `i`, `j`.

Then there is an isomorphism of root data `f : RootPairing.Equiv P Q` (bijective maps
of weight and coweight lattices and of root indices, compatible with roots, coroots and
the pairing) whose index bijection extends `e`: `f.indexEquiv i = e i` for every simple
`i` in `b.support`.

## Provenance

This is the classical fact that a reduced root system is determined up to isomorphism
by its Cartan matrix, extended to root data whose coroots span the coweight lattice.

- Milne, *Algebraic groups* (2017), Appendix C, Proposition C.52, printed p.623 (PDF
  p.639): "The Cartan matrix of (V, R) is independent of S, and determines (V, R) up to
  isomorphism." The proof given there sends the base `S` to the base `S'` along the
  bijection that matches the Cartan matrices.

The Lean formulation is derived. For a root datum whose coroots span the coweight
lattice, the simple coroots form a `ℤ`-basis of that lattice (Mathlib's base axioms).
The coweight lattice is then the coroot lattice and the weight lattice is its dual.
These are the lattices of the simply connected root datum of the root system, so the
root datum is determined by its root system. The statement also records the extra
information, present in the source's proof, that the isomorphism extends the given
bijection of simple roots.
