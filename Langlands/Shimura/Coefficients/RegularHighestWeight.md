# Regular highest weight of a coefficient system

This module defines when an algebraic representation of the similitude group of an
algebra with involution has regular highest weight. It is the hypothesis of Kottwitz
1992, printed p. 658: "The statement of the theorem becomes simpler and more useful
when the highest weight of `ξ` is regular."

## Definitions

Namespace `Langlands.Shimura.AlgebraInvolution`; `σ : AlgebraInvolution R A` over a
field `R`, and `ρ : σ.AlgebraicRepresentation W` (the published functor-of-points
representations of `Langlands/Shimura/Coefficients/Algebraic`).

- `SplitChart σ K' J n`, for a field `K'` with `Algebra R K'` and an index type `J`:
  an isomorphism of `K'`-algebras `equiv : K' ⊗_R A ≃ (J → M_n(K'))` and a map
  `conj : J → J` with `equiv (σ_{K'} x) j k l = equiv x (conj j) (n-1-l) (n-1-k)`. The
  extended involution is the reversed transpose of the conjugate factor. This is the
  form of the published unramified charts of `Langlands/Shimura/Unitary/KottwitzChart`
  (`UnramifiedChart.involution_eq`), now over an arbitrary splitting field. In such
  coordinates `g ↦ σ(g)⁻¹` preserves the diagonal and the upper triangular matrices of
  every factor. So the similitudes with diagonal coordinates form a maximal torus,
  those with upper triangular coordinates a Borel subgroup, and those of multiplier
  `1` with upper unitriangular coordinates its unipotent radical.
- `IsRegularHighestWeight n ρ`: there are a field `K'` of characteristic zero (in the
  universe of `R`, as required by `AlgebraicRepresentation.act`), a finite type `J`, a
  splitting chart `χ` whose map `conj` has no fixed point (`χ.conj j ≠ j` for all `j`),
  a nonzero `x ∈ K' ⊗_R W` and a weight `μ : J → Fin n → ℤ`, `m : ℤ` such that
  1. every similitude point `g` over `K'` with coordinates
     `χ.equiv g = (diag(t_{j,0}, …, t_{j,n-1}))_j` acts on `x` by the scalar
     `ν(g)^m ∏_{j,k} t_{j,k}^{μ_{j,k}}`, `ν` the published multiplier
     `Points.multiplier`;
  2. every point of multiplier `1` with upper unitriangular coordinates
     (`Matrix.BlockTriangular … id` and diagonal entries `1`) fixes `x`;
  3. for every `j`, `k ↦ μ_{j,k} − μ_{conj j, n-1-k}` is strictly decreasing
     (`StrictAnti`).

## Meaning

Conditions 1 and 2 say that `x` is a highest weight vector for the Borel subgroup of
the chart, with weight `(μ, m)`. The factors of the chart are exchanged in pairs
`{j, conj j}` by the involution, as for an involution of the second kind. On the points
of multiplier `1` the similitude condition gives `t_{conj j, n-1-k} = t_{j,k}⁻¹`, so this
torus is the product over the pairs of one diagonal torus of `GL_n` each, with
coordinates `t_{j,k}` for one chosen `j` in each pair, and the points of multiplier `1`
form the product of one `GL_n` per pair. The character of condition 1 restricted to the
factor `GL_n` of `j` is `t ↦ ∏_k t_k^{λ_{j,k}}` with `λ_{j,k} = μ_{j,k} − μ_{conj j, n-1-k}`.
These exponents do not depend on the choice of `μ` representing the character, and in
characteristic zero the character determines them, since `K'ˣ` has elements of
infinite order. For the paired factor, `λ_{conj j, k} = −λ_{j, n-1-k}`, so condition 3 at
`j` and at `conj j` are the same condition. Condition 3 says that the highest weight
`λ_j` of each `GL_n` factor is strictly dominant, which is regularity of the highest
weight. After the shift by `ρ = ((n − 1)/2, (n − 3)/2, …, −(n − 1)/2)` the entries
`λ_{j,k} + (n − 1)/2 − k` are then at distance at least `2` from one another.

For an irreducible `ρ` (the hypothesis of Kottwitz's theorem) the highest weight vector
is unique up to a scalar. Another splitting chart changes the highest weight by a Weyl
group element and keeps it regular. Neither fact is proved here. The definition asks
for one chart and one highest weight vector.

Both restrictions of the domain are needed. Over a finite field the torus character
does not determine the exponents: over `𝔽₂` every diagonal unit is `1`, and condition 1
holds for every `μ`, so a trivial representation would satisfy the definition. A factor
with `conj j = j` would carry the reversed transpose as its involution, whose similitude
group on that factor is an orthogonal similitude group, not `GL_n`.

In the Harris CM setting `R = K` is the coefficient field, a number field, `A` is
`K ⊗_ℚ A₀` for the division algebra `A₀` with involution of the second kind, and `J` is
the set of embeddings `φ` of its CM centre into `K'`, one matrix factor for each, with
`conj φ = φ ∘ c` for the complex conjugation `c` of the centre. Since `c ≠ id`, `conj` has
no fixed point.

## Source

R. E. Kottwitz, *On the λ-adic representations associated to some simple Shimura
varieties*, Invent. Math. 108 (1992), printed p. 658 (PDF p. 6): the highest weight of
`ξ` regular, with the consequences drawn from Vogan–Zuckerman. Registered
`kottwitz-1992-lambda-adic-simple-shimura`, SHA256
`749af5541a59187e6f9d1089dec9a0e591a2059173da739c7384ff3a7d0dd799`.

The definition of highest weight vectors through a maximal torus and the unipotent
radical of a Borel subgroup is the standard one. The chart form is taken from the
published `UnramifiedChart` of `Langlands/Shimura/Unitary/KottwitzChart`.
