# Cyclic linear forms on `I⁺` and proper unipotent radicals

Lean module: `Langlands.Representation.AffineGeneric.Genericity`, namespace
`Langlands.AffineGeneric`.

Let `F` be a nonarchimedean local field with residue field `k`, and let
`I⁺ = iwahoriRadical m` be the pro-unipotent radical of the standard Iwahori subgroup of
`GL_{m+1}(F)`. For `ϖ : Fˣ` write `aᵢ(Y) = coord ϖ Y i` and `groupCoord ϖ g i = aᵢ(g - 1)`.
These coordinates use `resOf`, which returns `0` for nonintegral arguments.

## Declarations

- `exists_blockIndex_lt_finRotate`: for a block shape `B` with at least two blocks and a
  permutation `v` of `Fin (m + 1)`, some `s` has `block(v s) < block(v (ρ s))`, where
  `ρ = finRotate (m + 1)`. Otherwise `s ↦ block(v s)` would be antitone along `0, 1, …, m` and
  also satisfy `block(v 0) ≤ block(v m)`, hence constant; but it takes the values `0` and `1`.
- `upperTriangular_mem_parabolic`: an upper triangular element lies in every standard block
  parabolic.
- `exists_mem_iwahoriRadical_coe_eq`: for every `Y ∈ 𝔓` there is `g ∈ I⁺` with `g = 1 + Y` as
  matrices. The matrix `1 + Y` is integral and its reduction is upper unitriangular, so its
  determinant is a unit of `𝒪` and `1 + Y ∈ GL_{m+1}(𝒪)`; its inverse lies in the Iwahori
  order by `isIwahoriOrder_of_reduction`, hence `(1 + Y)⁻¹ - 1 = -(1 + Y)⁻¹ Y ∈ 𝔓`.
- `weight_ne_zero`, `coord_single`: the weight is nonzero. The elementary matrix supported
  at `(s, ρ s)` with entry `(weight ϖ s)⁻¹ c` has coordinate `resOf c` at `s` and `0`
  elsewhere. If `ϖ` is a uniformizer and `c` is integral, the matrix lies in `𝔓`
  (`isIwahoriRadical_single`).
- `affineForm ϖ r g` defines `λ_r(g) = Σᵢ rᵢ aᵢ(g - 1)` for `r : Fin (m + 1) → k`.
  For a uniformizer `ϖ` the restriction to `I⁺` is additive (`affineForm_mul`).
- `exists_unipotent_affineForm_eq` (**genericity**) assumes `ϖ` is a uniformizer and every
  `rᵢ ≠ 0`. For every `t ∈ k`, every `x ∈ GL_{m+1}(F)` and every block shape `B` with at
  least two blocks there is `u` in `B.unipotentSubgroup F` with `x u x⁻¹ ∈ I⁺` and
  `λ_r(x u x⁻¹) = t`.

**Proof of genericity.** Write `x = ι w β b⁻¹` by `exists_iwahori_decomposition`. Use
`exists_blockIndex_lt_finRotate` to choose `s` with `block(w⁻¹ s) < block(w⁻¹ (ρ s))`. Put
`e = r_s res(ι_{ss}) res((ι⁻¹)_{ρ s, ρ s})`, which is nonzero since `res(ιᵢᵢ) res((ι⁻¹)ᵢᵢ) = 1`
(`IsIwahoriOrder.resOf_mul_diag`). Let `E ∈ I⁺` be `1` plus the elementary matrix at `(s, ρ s)`
whose coordinate at `s` is `t / e` and whose other coordinates vanish. The off-diagonal
entries of `w⁻¹ E w` are supported at `(w⁻¹ s, w⁻¹ (ρ s))`, so `w⁻¹ E w` lies in the
unipotent radical of `B`. Since `β b⁻¹` is in the parabolic, `u = (β b⁻¹)⁻¹ (w⁻¹ E w) (β b⁻¹)`
lies in the same radical (`BlockShape.conj_mem_unipotentSubgroup`). Now `x u x⁻¹ = ι E ι⁻¹ ∈ I⁺`
(`conj_mem_iwahoriRadical`). By `groupCoord_conj` its coordinates other than `s` vanish, and
`r_s` times its coordinate at `s` equals `e · (t / e) = t`. Hence `λ_r(x u x⁻¹) = t`.

## Origin

For a uniformizer `ϖ`, additivity makes `ψ ∘ λ_r` a character of `I⁺` for every complex
additive character `ψ` of `k`. When `m ≥ 1`, `ψ ≠ 1` and every `rᵢ ≠ 0`, this character is
affine generic. On the `i`-th affine simple root quotient it is `x ↦ ψ(rᵢ x)`, which is
nontrivial since multiplication by `rᵢ` permutes `k`.

- Gross and Reeder define affine generic characters of `Z(F)I⁺` through the affine simple
  root quotients for split simply connected almost simple groups in *Arithmetic invariants
  of discrete Langlands parameters*, Duke Math. J. 154 (2010), §9.2 (manuscript pp. 60–62).
  Proposition 9.3 (manuscript pp. 62–63) proves that compact induction from each such
  character of `Z(F)I⁺` is irreducible and supercuspidal.
  [March 2010 author manuscript](https://people.math.harvard.edu/~gross/preprints/AdjointGamma5.pdf).
- Knightly and Li define `χ` on `H = ZI⁺` for `GL_n` with restriction `ψ ∘ λ_r` to `I⁺`
  in *Simple supercuspidal representations of GL(n)*, Taiwanese J. Math. 19 (2015),
  §2, (2.1)–(2.2) (p. 997). Proposition 3.1 (p. 998) proves
  supercuspidality of every irreducible subrepresentation of `c-Ind_H^G χ` using a matrix
  coefficient compactly supported modulo the centre. For `n ≥ 2`, Theorem 4.4 (p. 1006)
  decomposes `c-Ind_H^G χ` into `n` inequivalent irreducible summands. In (4.8)–(4.9)
  (p. 1007) each summand is realized as `c-Ind_{H′}^G χζ`, where `H′ = ⟨gχ⟩H` and `χζ`
  extends `χ` to `H′`. [Journal article](https://doi.org/10.11650/tjm.19.2015.3853).

The direct computation in `exists_unipotent_affineForm_eq` gives the intersection property
used to prove vanishing constant terms in `TestFunction` and vanishing Jacquet coinvariants
in `Supercuspidality`.

For `m = 0` and a uniformizer `ϖ`, the formula on `I⁺ = 1 + 𝔭` is
`λ_r(g) = r₀ res(ϖ⁻¹ (g - 1))`, a multiple of the principal-unit homomorphism. The root system
of `GL_1` is empty. The intersection property is vacuous because no block shape of total
size `1` has two blocks.
