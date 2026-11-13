# Weights of a maximal split torus of `O(q)⁰` on `D^n`

Author: Worker 73.

Module `Langlands.GroupScheme.Quaternionic.MaximalSplitTorusWeightsStatement`, namespace
`Langlands.GroupScheme.Quaternionic`. It contains one `Prop`-valued definition,
`IsometryMaximalSplitTorusWeightsStatement`, with universe parameter `u`, and proves
nothing. Its proof is a separate task. The weight spaces are those of
[`cocharacterWeightSpace`](CocharacterWeightSpace.md).

## The statement

```lean
def IsometryMaximalSplitTorusWeightsStatement : Prop :=
  ∀ (K D : Type u) [Field K] [DivisionRing D] [Algebra K D] [Algebra.IsCentral K D]
    [FiniteDimensional K D] (degree : ℕ), Module.finrank K D = degree ^ 2 →
    ∀ (σ : FirstKindInvolution K D),
    Module.finrank K σ.symmetricSubspace = degree * (degree + 1) / 2 →
    ∀ (n : Type) [Fintype n] [DecidableEq n] (q : σ.QuadraticForms n)
    [Smooth (σ.isometryGroup q).X.hom],
    σ.IsNondegenerateQuadratic q →
    ∀ (S : CommGroupScheme (Spec (CommRingCat.of K)))
      (i : S.toGrp ⟶ σ.connectedIsometryGroup q),
      IsMaximalSplitTorus i →
      ∃ χ : Fin (σ.quadraticWittIndex q) → characterLattice S,
        LinearIndependent ℤ χ ∧
        (∀ ν : cocharacterLattice S, (∀ k, latticePairing S (χ k) ν = 0) → ν = 0) ∧
        ∀ (ν : cocharacterLattice S) (c : ℤ),
          Module.finrank D (σ.cocharacterWeightSpace q
              (CommGroupScheme.groupHom ν ≫ i ≫ identityComponentι (σ.isometryGroup q)) c) =
            Nat.card {p : Fin (σ.quadraticWittIndex q) × ℤˣ //
                (p.2 : ℤ) * latticePairing S (χ p.1) ν = c} +
              if c = 0 then Fintype.card n - 2 * σ.quadraticWittIndex q else 0
```

### Hypotheses

* `K` is an arbitrary field, with no restriction on the characteristic and no
  infiniteness hypothesis.
* `D` is a finite-dimensional central division `K`-algebra of degree `degree`, that is,
  `finrank K D = degree ^ 2`.
* `σ` is an involution of the first kind of `D` whose symmetric subspace has
  `K`-dimension `degree * (degree + 1) / 2`. In characteristic different from 2 this means
  that `σ` is orthogonal (Tits type `1`). In characteristic 2 every involution of the
  first kind satisfies it. With this hypothesis the published fixed-sign quotient
  `σ.QuadraticForms n = M_n(D) ⧸ {x - ᵗx^σ}` is Tits's space of `σ`-quadratic forms
  (sign `ε = 1`). The hypothesis and the reason for it are the same as in
  [`ConnectedIsometrySplitRankStatement`](ConnectedIsometrySplitRankStatement.md) and in
  the published `AlignedSpinCoverTitsIndexStatement`.
* `n` is a finite coordinate type.
* `q` is a nondegenerate `σ`-quadratic form on `D^n`: its polar Gram matrix `Q + ᵗQ^σ` is
  invertible. This is the nondefective case of Tits's nondegeneracy.
* The isometry group `O(q)` is smooth. This hypothesis is needed for the published
  `connectedIsometryGroup` to be defined.
* `S` is a commutative group scheme over `Spec K` and `i : S ⟶ O(q)⁰` exhibits it as a
  maximal split torus (`IsMaximalSplitTorus`, module `Rational.SplitTorus`). In
  particular `i` is a closed subgroup embedding of a split torus, and no larger split
  subtorus of `O(q)⁰` contains it.

### Conclusion

Write `r = σ.quadraticWittIndex q` for the Witt index of `q`. There are characters
`χ_0, …, χ_{r-1}` of `S` (elements of the published `characterLattice S`) with the
following three properties.

1. They are linearly independent over `ℤ`.
2. They detect cocharacters: if a cocharacter `ν` of `S` pairs to zero with every `χ_k`
   under the published `latticePairing`, then `ν = 0`. Together with 1, this says that
   the `χ_k` form a basis of `X^*(S) ⊗ ℚ`, so `S` has rank `r`.
3. Take a cocharacter `ν` of `S` and an integer `c`. Let `ν` act on `D^n` through
   `S ⟶ O(q)⁰ ⟶ O(q)`; the second map is the published inclusion `identityComponentι`.
   Then the weight space of weight `c`, `σ.cocharacterWeightSpace q (ν ≫ i ≫ ι) c`, has
   left `D`-dimension equal to the number of pairs `(k, s)` with `k < r` and `s ∈ ℤˣ`
   (that is, `s = ±1`) such that `s · ⟨χ_k, ν⟩ = c`. When `c = 0` one adds
   `card n - 2r`. The truncated natural subtraction is harmless, since `2r ≤ card n` for
   a nondegenerate form.

Equivalently: the weights of the maximal split torus `S` on `D^n` are `±χ_1, …, ±χ_r`,
each with `D`-multiplicity one, together with the weight `0` of multiplicity `n − 2r`. The
statement uses only cocharacters of `S`, so no torus weight-space notion is needed beyond
the published one-parameter definition.

## Mathematical content and provenance

The statement is derived. It restates the classical description of a maximal split torus
of an orthogonal group through a Witt decomposition. Choose a maximal family of mutually
orthogonal hyperbolic pairs `(x_k, y_k)`, `k = 1, …, r`. Then
`D^n = ⊕_k (D x_k ⊕ D y_k) ⊕ V_0`, and the anisotropic complement `V_0` has dimension
`n − 2r`. The torus scaling `x_k` by `t_k` and `y_k` by `t_k^{-1}`, and acting trivially
on `V_0`, is a maximal split torus. Its weights on `x_k` and `y_k` are `±χ_k`, where `χ_k`
is the `k`-th coordinate character, and its weight on `V_0` is `0`. All maximal split
tori arise this way. With the row action `v ↦ v u⁻¹` of the Library the signs are
exchanged, but the statement is symmetric under `s ↦ −s`.

Sources:

* Borel–Tits 1965, 4.24 (source `borel-tits-1965-groupes-reductifs`, printed p. 99, PDF
  p. 40) works in the ordinary case `D = K`. It diagonalizes a split torus of `O(Q)⁰`
  and finds isotropic weight vectors. It also notes that for nondegenerate `Q` the
  `k`-rank equals the index of `Q`.
* Tits 1966, Table II, the type `D_n` entries (source
  `tits-1966-classification-algebraic-semisimple`, printed pp. 56–57, PDF pp. 61–62),
  describe the groups `SO(D, h)` over a central division algebra of degree `d` with a
  form of index `r`. In characteristic different from 2 this is a hermitian form for an
  involution with `dim D^σ = d(d+1)/2`. In characteristic 2 it is a nondefective
  generalized quadratic form. Their index has relative rank `r`. Tits numbers the
  vertices `1, …, n`, with fork vertices `n − 1` and `n`.
  * For inner type `¹D_n` (conditions `rd ≤ n` and `n ≠ rd + 1`) the distinguished
    vertices are `d, 2d, …, rd`.
  * For outer type `²D_n` (condition `rd ≤ n − 1`) the star action of the Galois group
    exchanges the two fork vertices, and the table lists distinguished orbits. They are
    `d, 2d, …, rd`, except that when `n = rd + 1` (which forces `d = 1` or `2`) the last
    one is replaced by the orbit `(n − 1, n)` of the two fork vertices. For example, for
    `d = 1` and `r = n − 1` every vertex is distinguished.

  In both types the distinguished vertices among the nonfork vertices `1, …, n − 2` are
  exactly the multiples `jd` with `1 ≤ j ≤ r` and `jd ≤ n − 2`. This is the pattern that
  the vector weights give. Over a separable closure the weights of `D^n` are
  `±ε_1, …, ±ε_n`. For a suitable numbering and choice of signs, their restrictions to a
  maximal split torus are as follows: `ε_1, …, ε_{rd}` become
  `χ_1, …, χ_r`, each repeated `d` times, and the remaining `ε_i` become `0`. So the
  nonfork simple root `ε_i − ε_{i+1}` restricts nontrivially exactly when `i = jd` with
  `j ≤ r`. The statement records only the weights `±χ_k` and their multiplicities. It
  asserts nothing about distinguished vertices, and in particular nothing about the fork
  vertices.
* Tits 1968 (source `tits-1968-formes-quadratiques-clifford`, §2.1, printed p. 20, PDF
  p. 3, and §§2.2–2.3, printed pp. 21–23, PDF pp. 4–6) introduces the `σ`-quadratic
  forms, their polar forms and the Witt index, in every characteristic, with a sign `ε`
  equal to the type of the involution. The published `Quaternionic.Forms` uses the fixed
  sign `ε = 1`. Under the degree and symmetric-dimension hypotheses of this statement
  this is Tits's construction.

The formulation through the Library's `IsMaximalSplitTorus`, `characterLattice`,
`latticePairing` and the cocharacter weight spaces is new.
