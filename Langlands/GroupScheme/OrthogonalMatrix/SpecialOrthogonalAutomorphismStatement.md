# Automorphisms of the split even special orthogonal group

Author: Worker 74.

`Langlands.GroupScheme.OrthogonalMatrix.SpecialOrthogonalAutomorphismStatement.{u}` is an
**unproved** statement: over every field, every automorphism of the split group `SO_{2n}`
(`n ≥ 2`) is conjugation by a similitude of the hyperbolic quadratic form. In other words
`Aut(SO_{2n})(L) = PGO_{2n}(L) = GO_{2n}(L)/Lˣ`. There is no characteristic hypothesis.
This is the point where forms of `SO_{2n}` are tied to algebras with orthogonal
involution: a Galois cocycle with values in `Aut(SO_{2n})` becomes, through this
statement, a cocycle of similitudes up to scalars.

## Hypotheses

- `L : Type u` is a field and `n : ℕ` with `2 ≤ n`.
- `α` is an automorphism (an isomorphism to itself, as group schemes over `Spec L`) of
  `identityComponent (OrthogonalMatrix.groupScheme (Fin n) (CommRingCat.of L))`, the identity
  component `SO_{2n}` of the Library's split orthogonal group `O_{2n}`. That group is the
  orthogonal group of the hyperbolic form `q(x) = ∑ a, x (inl a) * x (inr a)` on
  `L^(Fin n ⊕ Fin n)`, with Gram matrix `Q = formMatrix (Fin n) L = [[0, 1], [0, 0]]`. A matrix
  `x` over a commutative `L`-algebra `R` lies in `O_{2n}(R)` when its defect `x Q xᵀ - Q` is
  alternating (`OrthogonalMatrix.IsAlt`: of the form `U - Uᵀ`). This is the row-vector
  convention `q(v x) = q(v)` of `OrthogonalMatrix.Basic`.

## Conclusion

There are an invertible matrix `g ∈ GL_{2n}(L)` and a unit `μ ∈ Lˣ` such that

- `g Q gᵀ - μ Q` is alternating, i.e. `q(v g) = μ q(v)` for all row vectors `v`: `g` is a
  similitude of `q` with multiplier `μ`;
- for every scheme `T` over `Spec L` and every point `x : T ⟶ SO_{2n}`, the matrix of the
  point `α(x)` of `O_{2n}` is `g X g⁻¹`. Here `X` is the matrix of `x` in `O_{2n}`, read
  through `OrthogonalMatrix.pointsEquiv` after composing with the inclusion
  `identityComponentι` of `SO_{2n}` into `O_{2n}`. The entries of `g` and `g⁻¹` are mapped into
  the global sections `Γ(T, ⊤)` by the structure map `scalarMap T : L →+* Γ(T, ⊤)`.

The point formula determines `α`, since points of `SO_{2n}` are determined by their matrices
in `O_{2n}`. Conversely, conjugation by a similitude preserves `O_{2n}`:
`(g X g⁻¹) Q (g X g⁻¹)ᵀ ≡ g X (μ⁻¹ Q) Xᵀ gᵀ ≡ Q` modulo alternating matrices. So the statement
says exactly that `GO_{2n}(L) → Aut(SO_{2n})` is surjective. No uniqueness is claimed; `g` is
unique up to `Lˣ`.

## Source and derivation

The statement is derived from the theory of automorphisms of split semisimple groups in
M.-A. Knus, A. Merkurjev, M. Rost, J.-P. Tignol, *The Book of Involutions* (1998), registered
source `knus-merkurjev-rost-tignol-1998-book-of-involutions` (PDF SHA-256
`e21641aeb1425b63bec70032352f0cb33275f7bd1ddf682c3bea62b798654fe0`; printed page `p` is PDF
page `p + 23` in Chapter VI).

- §25.B, Theorem (25.16), printed p.360 / PDF p.383: for a split semisimple group `G` over an
  arbitrary field `F` with adjoint group `Ḡ`, there is an exact sequence
  `1 → Ḡ(F) → Aut(G) → Aut(Dyn(Φ))`. The paragraph before it records that `Aut(G) → Aut(Ḡ)` is
  injective with image containing `Int(Ḡ(F))`.
- §26.A, proof of Theorem (26.15), statement (26.16), printed p.371 / PDF p.394: for type
  `D_n` with `n ≠ 4`, `PGO(A, σ, f) → Aut(PGO⁺(A, σ, f))` is an isomorphism. The index-2
  subgroup `PGO⁺` gives the inner automorphisms and every element of `PGO⁻` gives an outer
  one.

Derivation for `G = SO_{2n} = O⁺_{2n}`, which is split over every field:

- The adjoint group is `PGO⁺_{2n} = GO⁺_{2n}/𝔾ₘ`. By Hilbert's Theorem 90 for `𝔾ₘ`, its
  `L`-points are `GO⁺_{2n}(L)/Lˣ`, so inner automorphisms are conjugations by similitudes.
- The image of `Aut(SO_{2n})` in `Aut(Dyn(D_n))` consists of diagram automorphisms that
  preserve the character lattice `ℤⁿ` of the diagonal torus of `SO_{2n}`. For `n ≠ 4` this
  is all of `Aut(Dyn(D_n)) = ℤ/2` (for `n = 2`, `D_2 = A_1 + A_1`, the swap of the two
  nodes). For `n = 4` it is the stabilizer `ℤ/2` of the vector node in `S_3`, since triality
  moves `ℤ⁴` to the character lattice of a half-spin group. Equivalently, an automorphism of
  `SO_8` lifts to `Spin_8` and must preserve the kernel of `Spin_8 → SO_8`.
- The nontrivial element of `ℤ/2` is realized by the reflection exchanging `inl a` and
  `inr a` for one index `a`. This is an element of `O_{2n}(L)`, a similitude with `μ = 1`.

KMRT state (26.16) for adjoint groups over a separably closed field. The Lean statement is
for `SO_{2n}` over an arbitrary field and includes `n = 4`. These are the consequences of
(25.16) explained above. The task that published this statement uses it for `n ≥ 4`; it is
stated for all `n ≥ 2`, where the same argument applies.
