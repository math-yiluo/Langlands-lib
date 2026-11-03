# The opposite open cell of a closed subgroup of `GL_n` with diagonal cocharacter

This internal unit carries out the scheme-theoretic part of the opposite-cell proof. Throughout,
`k : Type u` is a field and `n` a finite index type. `G` is a group scheme over `Spec k`, and
`ρ : G ⟶ GL_n` is a homomorphism whose underlying morphism of schemes is a closed immersion.
Test objects `T` are arbitrary schemes over `Spec k`. The global sections `Γ(T, ⊤)` are a
`k`-algebra through the structure morphism (the local instance `sectionsAlgebra`).

## Main theorem

`Dynamic.isOpenImmersion_mul_of_diagonal` has the following hypotheses:

* `ρ.hom.hom.left` is a closed immersion;
* `χ : 𝔾_m ⟶ G` is a cocharacter with `χ ≫ ρ = diagonalCocharacter n k e` for some
  `e : n → ℤ`;
* `iU : U ⟶ G` represents `U(χ⁻¹)`, the dynamic unipotent subgroup functor of `χ` precomposed
  with inversion on `𝔾_m`;
* `iP : P ⟶ G` represents `P(χ)`;
* the multiplication `m = (fst ≫ iU) * (snd ≫ iP) : U ×_k P ⟶ G` is a monomorphism.

Under these hypotheses, the underlying morphism of schemes of `m` is an open immersion. The
monomorphism hypothesis is discharged later, in `Absolute.OppositeCellProof`, by
`Dynamic.mono_oppositeCellMul`.

## Auxiliary results

* `isUnit_of_basicOpen_eq_top`: a global section whose basic open is the whole scheme is a unit.
* `GeneralLinear.aeval_values_pointsEquiv`: let `y` be a point of `GL_n` over `T`. Evaluating a
  polynomial in the coordinates at the matrix of `y` equals pulling back along `y` the
  corresponding global function on `GL_n`. It comes from the description of `pointsEquiv` by
  the classifying map of the coordinate ring.
* `GeneralLinear.inv_comp_diagonalCocharacter`: precomposing the diagonal cocharacter of `e`
  with inversion on `𝔾_m` gives the diagonal cocharacter of `-e`. It is checked on points.
* `embeddingIdeal ρ` is the kernel of evaluation at the matrix of the universal point `ρ` of
  `GL_n` over `G`. It is the ideal of polynomials in the coordinates that vanish on `G`.

### Points of `G` as zeros of the embedding ideal

* `pointsEquiv_comp_mem_zeroLocus`: for every point `x` of `G` over `T`, the matrix of `x ≫ ρ`
  is a zero of `embeddingIdeal ρ` over `Γ(T, ⊤)`. This is `aeval_values_pointsEquiv` and
  pullback along `x`.
* `exists_comp_eq_of_mem_zeroLocus`: conversely, let `y` be a point of `GL_n` over `T` whose
  matrix is a zero of `embeddingIdeal ρ`. Then `y` factors through `ρ`. Both schemes are
  affine, so `Scheme.ker_of_isAffine` describes the kernels of `ρ` and `y` by global sections.
  Each section of `GL_n` is the class of a polynomial, and this gives
  `ker ρ ≤ ker y`. `IsClosedImmersion.lift` then produces the factorization.
* For a `k`-algebra `S`, `affineTest k S` is `Spec S` as an object over `Spec k`, and
  `affineTestEquiv k S : S ≃ₐ[k] Γ(Spec S, ⊤)`. By `mem_zeroLocus_iff`, a matrix `g : GL n S`
  is a zero of `embeddingIdeal ρ` if and only if its image over `Γ(Spec S, ⊤)` is the matrix
  of `x ≫ ρ` for a point `x` of `G` over `Spec S`.

### The hypotheses of the stabilizer argument

The next four results check, for `J = embeddingIdeal ρ`, the hypotheses of
`GeneralLinear.mem_zeroLocus_of_mul_mem` from `GeneralLinearStabilizer`.

* `ideal_le_embeddingIdeal`: the ideal of `GL_n` lies in `J`. Its polynomials vanish in the
  coordinate ring of `GL_n`.
* `zeroLocusMulClosed_embeddingIdeal`: zeros of `J` are closed under multiplication, because
  `ρ` is a homomorphism. By `mem_zeroLocus_iff`, zeros come from points `x, y` of `G`, and
  `(x * y) ≫ ρ = (x ≫ ρ) * (y ≫ ρ)`.
* `one_mem_zeroLocus_embeddingIdeal`: the identity matrix over `k` is a zero of `J`, coming
  from the identity point.
* `diagonalUnits_mem_zeroLocus_embeddingIdeal`: if `χ ≫ ρ` is the diagonal cocharacter of
  `e`, then `diag(T ^ e i)` over `k[T, T⁻¹]` is a zero of `J`. It comes from the point `χ(T)`
  of `G` over `Spec k[T, T⁻¹]`.

### Matrix descriptions of `U(χ⁻¹)` and `P(χ)`

Assume `χ ≫ ρ` is the diagonal cocharacter of `e`.

* `mem_unipotent_iff_of_diagonal`: a point `x` of `G` lies in `U(χ⁻¹)` if and only if the
  matrix of `x ≫ ρ` lies in `blockUnipotentSubgroup (-e)`.
* `mem_parabolic_iff_of_diagonal`: `x` lies in `P(χ)` if and only if the matrix of `x ≫ ρ`
  lies in `blockParabolicSubgroup e`.

The proofs rewrite the dynamic subgroup functors of `G` as preimages of those of `GL_n` along
the closed subgroup `ρ` (`unipotent_eq_comap_of_isClosedSubgroup`,
`parabolic_eq_comap_of_isClosedSubgroup`). For `U(χ⁻¹)` they also use
`inv_comp_diagonalCocharacter`. Then the published matrix descriptions
`unipotent_diagonalCocharacter` and `parabolic_diagonalCocharacter` for `GL_n` apply.

* `appTop_cellMinor`: pulling back the cell minor `δ_e` of the universal matrix of `G` along a
  point `z` gives the cell minor of the matrix of `z ≫ ρ`. This uses the naturality of
  `pointsEquiv` and `map_cellMinor`.

## Proof of the main theorem

Let `c` be the cell minor `δ_e` of the universal matrix of `G`, a global function on `G`, and
let `Ω = D(c)` be its basic open.

1. **The image lies in `Ω`.** For every point `(u, p)`, the matrix of `(u p) ≫ ρ` is a product
   of a block unipotent matrix for `-e` and a block parabolic matrix for `e`. So its cell minor
   is a unit by `isUnit_cellMinor_mul`. Applied to the universal point of `U ×_k P`, together
   with `preimage_basicOpen_top` and `appTop_cellMinor`, this gives `m⁻¹(Ω) = ⊤`. The
   morphism `m` therefore lifts through the open immersion `Ω.ι`
   (`IsOpenImmersion.lift`), giving `l` with `l ≫ Ω.ι = m`.
2. **A section over `Ω`.** View `Ω` as a scheme over `Spec k`, with the point `xΩ` of `G`
   given by its inclusion. The pullback of `c` to `Ω` has basic open all of `Ω`, so the cell
   minor of the matrix of `xΩ ≫ ρ` is a unit. `exists_cell_decomposition` writes this matrix
   as `u' p'`, with `u'` block unipotent for `-e` and `p'` block parabolic for `e`, over
   `Γ(Ω, ⊤)`.
3. The matrix `u' p'` is a zero of `J` by `pointsEquiv_comp_mem_zeroLocus`. The stabilizer
   theorem `mem_zeroLocus_of_mul_mem`, with the four hypotheses above, then shows that `p'` is
   a zero of `J`. By `exists_comp_eq_of_mem_zeroLocus`, `p'` is the matrix of `p₀ ≫ ρ` for a
   point `p₀` of `G` over `Ω`. Then `p₀ ∈ P(χ)`, and `xΩ * p₀⁻¹ ∈ U(χ⁻¹)` because its matrix
   is `u'`. By representability these points factor as `p₁ ≫ iP` and `u₁ ≫ iU`.
4. Let `ψ = lift u₁ p₁ : Ω ⟶ U ×_k P`. Then `ψ ≫ m = (xΩ * p₀⁻¹) * p₀ = xΩ`.
5. **`l` is an isomorphism with inverse `ψ`.** First, `ψ ≫ l = 𝟙` after composing with the
   monomorphism `Ω.ι`. Second, `l ≫ ψ = 𝟙` after composing with `m`, which is a monomorphism
   on underlying schemes by the hypothesis and `Over.mono_left_of_mono`.
6. Hence `m = l ≫ Ω.ι` is an isomorphism followed by an open immersion, so it is an open
   immersion.

## Provenance

This is the scheme-theoretic part of Step 3 of the proof of Proposition 2.1.8(3) in
Conrad–Gabber–Prasad, *Pseudo-reductive groups* (2nd edition). They identify
`G ∩ (U_{GL}(-λ) × P_{GL}(λ))` with `U_G(-λ) × P_G(λ)` by showing that the factors of a point
of `G` in the open cell of the ambient group lie in `G`. The book obtains this by the stabilizer
argument. Here, the open cell of `GL_n` is cut out by the cell minor, the factorization is
explicit (`GeneralLinearCell`), and the factors are shown to lie in `G` by the ideal-theoretic
stabilizer argument of `GeneralLinearStabilizer`. The open-immersion property is deduced from
an explicit inverse over the basic open `Ω`. The formulation is internal to this development.
