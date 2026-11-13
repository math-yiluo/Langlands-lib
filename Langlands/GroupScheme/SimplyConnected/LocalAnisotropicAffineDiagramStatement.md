# A vertex-transitive affine extension of the Cartan matrix of an anisotropic local group

Authors: Worker 158, Worker 5662.

This module states one proposition, `Langlands.GroupScheme.LocalAnisotropicAffineDiagramStatement`.
It supplies no proof. It is the building-theoretic input of Kaletha–Prasad's proof of
Theorem 10.3.1, specialized to nonarchimedean local fields and written on the published
actual Tits-index data `TitsIndexData G`. It also contains the splitting over the maximal
unramified extension that the same proof establishes (see "What the statement bundles"
below). The companion module `LocalAnisotropicTypeAReduction` proves
`LocalAnisotropicTypeAStatement` from it.

## The statement

The hypotheses are those of `LocalAnisotropicTypeAStatement` in
`Langlands/GroupScheme/SimplyConnected/LocalAnisotropicInnerTypeAStatement.lean`:

- `K : Type u` with `[Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]`, a nonarchimedean local field of any characteristic;
- a group scheme `G` over `Spec K` with `[IsAffineHom G.X.hom]` and
  `[LocallyOfFiniteType G.X.hom]`;
- an arbitrary actual index datum `d : TitsIndexData G`;
- `IsAbsolutelyAlmostSimple G` and `IsAnisotropic G`.

The conclusion: there is an integer matrix `A : Matrix (Option d.Vertex) (Option d.Vertex) ℤ`
(the simple vertices of `d` together with one extra index `none`) such that

1. `A (some a) (some b) = d.cartan a b` for all simple vertices `a b`. Here
   `d.cartan a b = ⟨α_a, α_b^∨⟩` is the actual integral Cartan pairing of the simple root
   `α_a` with the simple coroot `α_b^∨`;
2. `A i i = 2` for every index `i`;
3. `A i j ≤ 0` whenever `i ≠ j`;
4. `A i j = 0 ↔ A j i = 0` for all `i j`;
5. some `m : Option d.Vertex → ℤ` with `0 < m i` for every `i` satisfies `m ᵥ* A = 0`,
   that is `∑ i, m i * A i j = 0` for every `j` (a positive left kernel vector);
6. for all indices `i j` there is a permutation `σ` of `Option d.Vertex` with
   `A (σ k) (σ l) = A k l` for all `k l` and `σ i = j`. So the symmetries of `A` act
   transitively on the indices.

Conditions 2–4 say that `A` is a generalized Cartan matrix, and condition 1 says that
deleting the index `none` leaves the actual Cartan matrix of `G`.

## Where the matrix comes from in the source

T. Kaletha and G. Prasad, *Bruhat–Tits Theory: A New Approach*, Cambridge University
Press, 2023, registered as `kaletha-prasad-2023-bruhat-tits-new-approach`. Printed page
numbers are followed by PDF page numbers.

Theorem 10.3.1 (printed pp. 391–392 / PDF pp. 422–423). Chapter 10 assumes that the
residue field has dimension at most 1. A nonarchimedean local field has a finite residue
field, so it satisfies this. The theorem says that an absolutely almost simple anisotropic
`k`-group splits over the maximal unramified extension `K'` of `k` and is of type `A_n`.
Its proof runs as follows, with `Γ = Gal(K'/k)`:

- `B(G) = B(G_{K'})^Γ` is a single point `x` (Proposition 9.3.9, printed p. 335 /
  PDF p. 366).
- A special `k`-apartment `A` of `B(G_{K'})` contains a `Γ`-chamber `C`
  (Proposition 9.3.6, printed p. 333 / PDF p. 364). `C` is a `K'`-chamber by
  Proposition 9.10.4 (printed p. 382 / PDF p. 413).
- Let `Δ` be the basis, determined by the Iwahori subgroup of `C`, of the affine root
  system of `G_{K'}` with respect to the torus `T_{K'}` of `A`. Then `Δ` is `Γ`-stable, and
  its elements correspond `Γ`-equivariantly to the vertices of `C`
  (Proposition 1.3.22(6), printed p. 23 / PDF p. 54).
- Since `B(G)` contains no facet of positive dimension, the discussion in 9.2.4
  (printed p. 327 / PDF p. 358) shows that `Γ` acts transitively on the vertices of `C`,
  hence on `Δ`.
- By the description of irreducible affine root systems in Proposition 6.4.8
  (printed pp. 225–226 / PDF pp. 256–257, with Table 6.4.1 on printed p. 227), the affine
  root system is of type `A_n`, since otherwise the automorphisms of its affine Dynkin
  diagram could not act transitively on `Δ`. This implies that `G_{K'}` is `K'`-split.

The matrix `A` of the statement is the matrix of Cartan integers of `Δ`: its entry at
`(ψ, η)` is `ψ̇(η̇^∨)`, where `ψ̇` is the gradient of the affine root `ψ`. These are the
integers from which Construction 1.3.64 (printed pp. 39–40 / PDF pp. 70–71) builds the
affine Dynkin diagram. The conditions match as follows:

- Choose an extra special vertex of `C` and let `none` be the element of `Δ`
  corresponding to it. The other elements of `Δ` vanish at that vertex
  (Proposition 1.3.22(6)). As in the proof of Proposition 1.3.47(1) (printed p. 31 /
  PDF p. 62), their gradients form a basis of the finite root system
  `Φ(T_{K'}, G_{K'})`. Because `G_{K'}` is split, this is the absolute root
  system of `G`. Any two bases of the absolute root datum of `G`, for any maximal tori,
  are carried to each other by an isomorphism of root data. So, after the elements of `Δ`
  other than `none` are matched with the simple vertices of `d`, their Cartan integers
  are `d.cartan`. This gives condition 1 for every datum `d`.
- Distinct elements of a basis have nonpositive Cartan integers, and a Cartan integer
  vanishes exactly when the transposed one does. Together with `ψ̇(ψ̇^∨) = 2`, this gives
  conditions 2–4.
- Proposition 1.3.47(1),(2) gives positive integers `n_ψ` such that `∑_{ψ∈Δ} n_ψ ψ` is a
  constant functional. Taking gradients, `∑ n_ψ ψ̇ = 0`, so pairing with each `η̇^∨` gives
  `∑_ψ n_ψ ψ̇(η̇^∨) = 0`. This is condition 5 with `m ψ = n_ψ`.
- `Γ` acts on the affine root system by automorphisms and preserves `Δ`, so it preserves the
  Cartan integers of `Δ`. Its transitivity on `Δ` gives condition 6.

The authors' corrections (version of 1 November 2024, registered as
`kaletha-prasad-2024-corrections`) have no entry for §10.3, Proposition 6.4.8,
Proposition 1.3.22(5),(6), Construction 1.3.64, 9.2.4, or Propositions 9.3.6, 9.3.9 and
9.10.4. They do correct Proposition 1.3.47. In (1), "constant functional" becomes
"non-zero constant functional" and "common denominator" becomes "common factor". The
proof of (2) is replaced, and statements (3′) and (3′′) on special vertices are added.
The corrected (2) still says that all `n_ψ` are positive, which is what condition 5 uses.
The book attributes Theorem 10.3.1 to Bruhat–Tits [BT87a, 4.4–4.5].

## What the statement bundles

The statement is written on the absolute Cartan matrix `d.cartan`. In the source, the
affine root system in the proof is that of the quasi-split group `G_{K'}` relative to
`K'`. Its gradients form the `K'`-relative root system, which need not be the absolute
one before the splitting is known. Kaletha–Prasad obtain the splitting of `G_{K'}` only at
the end of the proof, from Proposition 6.4.8 and the transitivity. So a proof of this
statement from the building has to establish all of the following:

- the building facts above (Propositions 9.3.9, 9.3.6, 9.10.4, the transitivity argument
  of 9.2.4, and the correspondence of Proposition 1.3.22(6));
- the marks of Proposition 1.3.47;
- the splitting of `G` over `K'`, either through Proposition 6.4.8 as in the source or by
  a separate argument, so that the Cartan integers of `Δ` can be compared with
  `d.cartan`.

The statement is therefore not plain building transitivity.

It is also no weaker than `LocalAnisotropicTypeAStatement`, given the proved combinatorics
in `AffineCartanTransitive`. If the actual index has type `A_n`, the affine Cartan matrix
of type `A_n` satisfies conditions 1–6: for `n = 1`, the matrix with rows `(2, -2)` and
`(-2, 2)`; for `n ≥ 2`, the cyclic matrix with `-1` between cyclically adjacent indices.
In both cases `m` is constant `1` and the symmetries include the rotations. Conversely,
`LocalAnisotropicTypeAReduction` derives `LocalAnisotropicTypeAStatement` from this
statement. The point of the split is that the combinatorial step of the proof, which the
source does with the classification in Proposition 6.4.8, is now proved, and what remains
to prove is exactly the building input described above.

## Scope

- The field `K` is a nonarchimedean local field, as in `LocalAnisotropicTypeAStatement`.
  Theorem 10.3.1 itself allows any field in the standing setting of Chapter 10 whose residue
  field has dimension at most 1.
- Simple connectedness is not assumed, as in Theorem 10.3.1.
- The splitting over `K'` is not stated as a separate conclusion. It enters only through
  condition 1.
