# The cuspidal-pair Eisenstein series as a group-scheme Eisenstein series

Module `Langlands.Global.Factors.CuspidalPairSchemeSeries` identifies the Eisenstein series
`CuspidalPairEisenstein.eisensteinSeries` of the matrix model (module
`Langlands.Global.Factors.CuspidalPairEisensteinSeries`) with the Eisenstein series
`IsIwasawaCompact.eisensteinSeries` of the group-scheme model (module
`Langlands.Global.AdelicEisensteinSeries`) on one complex line of parameters. With the module
`Langlands.Global.Factors.CuspidalPairSchemeAutomorphy` it states and proves the proposition
`Langlands.Global.CuspidalPairEisenstein.CuspidalPairSchemeComparisonStatement.{u}`.

Throughout, `F : Type u` is a number field, `N = r + t + 2`, `B = blockShape r t` is the upper
block shape of type `(r + 1, t + 1)`, `P` is the scheme block parabolic
`blockParabolicScheme (Fin N) 𝕜 (blockShapeWeight B)` of the scheme `GL_N` with inclusion `p`,
and `hK = isIwasawaCompact_blockParabolic F B` is the Iwasawa property of the standard maximal
compact subgroup `standardCompactPoints F N`.

## The statement

`CuspidalPairSchemeComparisonStatement` says: for every number field `F : Type u` with
`[CompactSpace (AdeleQuotient F)]`, all `r t : ℕ`, actual cuspidal realizations
`T : CuspidalOperatorRealization F r`, `T' : CuspidalOperatorRealization F t` and every `φ` with
`IsSection T T' φ`,

1. for all smooth-structure data `hsmooth`, `hcalc` of the scheme `GL_N`, the function
   `φ ∘ adelicHomeomorph F N` on the adelic points of the scheme `GL_N` satisfies
   `IsAutomorphicFunctionOn` for `parabolicQuotientSubgroup F p (blockUnipotentInclusion F B)
   (blockLeviInclusion F B)`, the subgroup
   `(standardCompactPoints F N).comap (ofInfinite F GL_N)` and the standard matrix embedding;
2. for every `s : ℂ` and every adelic point `g` of the scheme `GL_N`,

   `eisensteinSeries F φ s (adelicHomeomorph F N g) =
     hK.eisensteinSeries (φ ∘ adelicHomeomorph F N) (s • lineParameter F r t) g`.

No unitarity of central characters is assumed. Both sides of 2 are unconditional sums
(`tsum`), so 2 holds for every `s`, including where neither sum converges (both are then `0`).
The theorem `cuspidalPairSchemeComparison` proves the statement: part 1 is
`isAutomorphicFunctionOn_of_isSection` and part 2 is
`eisensteinSeries_eq_schemeEisensteinSeries`.

## The line parameter

`firstBlock r t` and `secondBlock r t` are the two indices of `B`; `eq_firstBlock_or_eq_secondBlock`,
`prod_blocks`, `prod_filter_firstBlock` and `prod_filter_secondBlock` evaluate the finite products
over the blocks.

`lineParameter F r t` is the element

  `λ₁ = ((t + 1)/N) ⊗ det₁ + (-(r + 1)/N) ⊗ det₂`

of `X^*(P) ⊗ ℂ`, where `det₁` and `det₂` are the block determinant characters
`parabolicBlockCharacter B 𝕜 (firstBlock r t)` and `parabolicBlockCharacter B 𝕜 (secondBlock r t)`
(module `Langlands.Global.AdelicBlockParabolicCharacters`).

- `log_parabolicCharacter`: for `q` in the adelic block parabolic,
  `log δ_P(q) = (t + 1) log |det m₁| - (r + 1) log |det m₂|`, where `δ_P` is
  `parabolicCharacter F B`, `m` is the Levi projection of `q` and `|det mᵢ|` is
  `blockDeterminantNorm F B i m`. It is `leviCharacter_apply` for two blocks.
- `heightPower_eq_schemeHeightPower`: Shahidi's twist of the matrix model equals the
  group-scheme twist on the line,

  `heightPower F r t s (adelicHomeomorph F N g) = hK.heightPower (s • λ₁) g`.

  Proof: factor `adelicHomeomorph F N g = q k` with `q` in the matrix block parabolic and `k` in
  the standard compact subgroup (`exists_parabolic_mul_standardCompact`), so that the left side is
  `exp (s/N · log δ_P(q))` (`heightPower_eq`). On the scheme side `g = p(y) z` with
  `y = (blockParabolicPointsEquiv F B 𝔸).symm q` and `z ∈ standardCompactPoints F N`, so
  `hK.height g = characterLog F P y` (`IsIwasawaCompact.height_eq`). The pairing of `s • λ₁`
  with it is `s ((t + 1)/N · log |det m₁| - (r + 1)/N · log |det m₂|)` by
  `complexParameterPairing_tmul` and `characterLog_parabolicBlockCharacter`, and
  `log_parabolicCharacter` finishes the proof.

## The coset spaces

- `rational_generalLinear_injective`: the principal map on rational points of the scheme `GL_N`
  is injective (by `adelicEquiv_rational` and `AdelicGL.rational_injective`).
- `rationalPointsEquiv F r t`: the subgroup `rationalSubgroup F GL_N` of rational points is
  isomorphic to `RationalGL F N`; `rational_rationalPointsEquiv` says that the principal adelic
  matrix of its value is the matrix of the point (`adelicHomeomorph`).
- `adelicHomeomorph_map_rational_blockParabolic`: the adelic matrix of a rational point of `P`
  is the principal adelic matrix of its block upper triangular rational matrix.
- `mem_parabolicRationalSubgroup_iff`: a rational point of `GL_N` lies in
  `parabolicRationalSubgroup F p` exactly when its matrix lies in `B.parabolic F`.
- `parabolicCosetsEquiv F r t`: hence the right coset spaces `ParabolicRationalCosets F p` and
  `Quotient (QuotientGroup.rightRel (B.parabolic F))` are equivalent (`Quotient.congr`).

## The series

- `isSection_rational_mul`: a section is left invariant under the principal matrices of
  `B.parabolic F` (`AdelicBlockScalarSections.realizedSection_rational`, through
  `realizedSection`).
- `heightPower_rational_mul`: so is Shahidi's twist, by `heightPower_eq` and
  `parabolicCharacter_rational`.
- `eisensteinSeries_eq_schemeEisensteinSeries`: the series identity of part 2. The terms of the
  matrix sum, as a function `f` of the rational matrix, are left invariant under `B.parabolic F`
  by the two previous lemmas. For a coset `c` of the scheme model, the chosen representative of
  `parabolicCosetsEquiv F r t c` and the matrix of the chosen representative of `c` lie in the
  same right coset, so `f` takes the same value at both; at the latter it is the scheme term
  `hK.eisensteinTerm (φ ∘ adelicHomeomorph F N) (s • λ₁) g c` by
  `rational_rationalPointsEquiv` and `heightPower_eq_schemeHeightPower`. Reindexing the matrix
  sum along `parabolicCosetsEquiv` (`Equiv.tsum_eq`) gives the identity.

## Provenance

This is a derived comparison of two Library formalizations of the same Eisenstein series. The
group-scheme series is that of Bernstein–Lapid, *On the meromorphic continuation of Eisenstein
series*, J. Amer. Math. Soc. 37 (2024), §2.2, (2.1), p. 191: `E(g, φ, λ) = ∑_{γ ∈ P(F)\G(F)}
φ_λ(γ g)` with `φ_λ(g) = φ(g) m_P(g)^λ`. The cuspidal-pair series is the series on Shahidi's line
of parameters (F. Shahidi, *On Certain L-Functions*, Amer. J. Math. 103 (1981), §5, proof of
Theorem 5.1, p. 351), written with the twist `δ_P(g)^(s/N)` as in the module
`Langlands.Global.Factors.CuspidalPairEisensteinSeries`. Mœglin–Waldspurger, *Spectral
Decomposition and Eisenstein Series* (1995), II.1.1, pp. 78–79, define the inducing spaces
`A(U(𝔸)M(k)\G)_π` and their twists by characters composed with `m_P` (formula (2)); the
sections of `IsSection` and the twist `H^s` are of this kind. They define the Eisenstein series
`E(φ, π)(g) = ∑_{γ ∈ P(k)\G(k)} φ_π(γ g)` in II.1.5, p. 85, where the series converges. In the
convergence region the common value of the two sums is therefore Mœglin–Waldspurger's
`E(φ H^s, π_s)(g)`, with `λ = s λ₁`. The Lean identity itself holds for every `s`, between the
two unconditional sums (`tsum`), which are `0` where their terms are not summable. For `q` in the
adelic block parabolic,
`⟨λ₁, log_P(q)⟩ = (1/N) log δ_P(q)`. This module does not compare `λ₁` with the parameter
`modulusParameter` of the adjoint determinant, and it does not prove that the parameters
`s • λ₁` are regular in the sense of `IsRegularParameter` for large `Re s`.
