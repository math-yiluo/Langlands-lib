# Neutral Brauer classes and actual splitting

For every field `K : Type u` and actual central simple algebra
`A : CSA.{u,u} K`, `Langlands.Brauer.IsSplit A` means

`∃ n : ℕ, 0 < n ∧ Nonempty (A ≃ₐ[K] Matrix (Fin n) (Fin n) K)`.

The theorem `classOf_eq_zero_iff` proves
`classOf A = 0 ↔ IsSplit A` for Mathlib's actual matrix-stable Brauer
quotient. `neutralMatrixSize A h` chooses a positive size from a proof
`h : classOf A = 0`, `neutralMatrixSize_pos` proves positivity, and
`neutralMatrixChart A h` constructs an actual algebra equivalence from
`A` to matrices of that size. Thus the result gives an actual splitting
chart, rather than only a statement about stable equivalence.

There are no restrictions on characteristic, perfection or separability.
The field and the CSA carrier can share any universe. The corner
construction below is more general: its field, coefficient ring, vector
space and matrix index type have independent universes.

## Cancelling a stabilization by an actual corner

`isSplit_of_equivalent_groundField` starts from Mathlib's witness
`Matrix (Fin n) (Fin n) A ≃ₐ[K] Matrix (Fin m) (Fin m) K`, with both
sizes nonzero. It identifies the target with the full endomorphism algebra
of the finite vector space `V = Fin m → K` and chooses the diagonal index
`0 : Fin n`. The main construction is then `matrixCornerEquiv`.

For any algebra equivalence
`e : Matrix ι ι A ≃ₐ[K] Module.End K V` and index `i : ι`, put
`p = e (Matrix.single i i 1)` and `W = LinearMap.range p`.
The abbreviation `matrixCornerSpace e i` is this actual image submodule.
The identity `p*p = p` implies that `p` acts as the identity on `W`,
as proved in `matrixCorner_fixed`.

For `a : A`, the operator `e (Matrix.single i i a)` maps `V` into `W`.
Its restriction defines `matrixCornerLinear`, and the identities

- `single i i a * single i i b = single i i (a*b)`;
- `p|W = id`;

make this a unital algebra homomorphism `matrixCornerHom : A →ₐ[K] End_K(W)`.
The range is nontrivial when `A` is nontrivial: injectivity of `e` ensures
that `p` is a nonzero operator, so its image contains a nonzero vector.
When `A` is simple, the homomorphism into this nontrivial endomorphism
ring is injective.

For surjectivity, extend any `g : End_K(W)` to the operator
`f = W.subtype ∘ g ∘ p.rangeRestrict` on `V`, and let `x = e.symm f`.
The matrix corner identity
`single i i 1 * x * single i i 1 = single i i (x i i)` gives
`e (single i i (x i i)) = p*f*p`. Since `p` fixes `W` and the values
of `g`, the restriction of this operator to `W` is exactly `g`.
This proves `matrixCornerHom_surjective` and hence the actual
equivalence `matrixCornerEquiv`.

In the stabilization application, `W` is a submodule of a finite vector
space, and its nontriviality makes `Module.finrank K W` positive.
A finite basis identifies `End_K(W)` with square matrices of that size,
giving the asserted splitting chart. The reverse implication of
`classOf_eq_zero_iff` uses `classOf_eq_of_algEquiv`, `classOf_matrix`
and the ground-field class computation.

## Source and provenance

The original source is Knus–Merkurjev–Rost–Tignol, *The Book of Involutions*
(1998), §1, printed pp.3–4 / PDF pp.26–27, registered as
`knus-merkurjev-rost-tignol-1998-book-of-involutions`, content SHA256
`e21641aeb1425b63bec70032352f0cb33275f7bd1ddf682c3bea62b798654fe0`.
Page 3 gives the Wedderburn structure theorem, and page 4 gives
matrix-stable Brauer equivalence in Definition (1.3), the neutral class
represented by the ground field, and its matrix-algebra representatives.
These original pages and the relevant retained author errata were read;
no correction to these passages was present.

The image-idempotent construction is an internal proof of cancellation
against the ground field. It establishes the source's neutral-class
characterization directly from the actual matrix-stable relation,
without assuming uniqueness of a Wedderburn division algebra or a
Brauer-group splitting theorem. The proof uses only actual algebra
equivalences, linear-map ranges, simplicity and finite bases.
