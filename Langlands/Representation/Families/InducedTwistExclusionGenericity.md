# Zariski-generic separation of geometric-lemma pieces

Author: Worker 5120.

This internal supporting module produces the polynomial genericity condition for the
exclusion statement. For an irreducible admissible `ρ` of an actual rational Levi `M(k)` and a
nonidentity double coset `P z P`, there is a nonzero polynomial `f` in the canonical
coordinates of the unramified characters. Off the zero set of `f`, no generalized
`A_M(k)`-eigencharacter of `ρψ` is one of the geometric-lemma piece at `z` evaluated at
`ρψ`. Its provenance is internal; the geometric input is the published nonidentity-piece
displacement theorem (`UnramifiedPieceDisplacement`).

## Declarations

- `Langlands.InducedTwistExclusion.finite_isGeneralizedEigencharacter`: an admissible
  representation that is finitely generated over its group algebra has finitely many
  generalized eigencharacters along a central map. This is the published
  `finite_generalizedWeights` with the discrete topology on the source group, where every
  kernel is open.

The remaining declarations are in `Langlands.Aubert.General.RepresentedParabolic`.

- `normalizedRealPart_eq_of_norm_eq`: two characters of a split torus with the same modulus
  at every point have the same normalized real part. The real part only depends on the
  character moduli.
- `exists_norm_ne_of_nonidentity`: let `pres` be a parabolic root presentation of `(p, l, a)`
  and `R` integral reflection data. Let `ψ` be an unramified character whose real part lies in
  the open chamber. Let `D` be an intersection datum for `(P, P)` at a nonidentity double
  coset, and let `g ≫ a' ≫ (L' → M) = a` factor `a` through a split component `a'` of
  `L'`. Then some `t ∈ A(k)` has `‖ψ(m t)‖ ≠ ‖ψ(a t)‖`, where `m = g ≫ a' ≫ φ ≫ l' ≫ p'`.
  The displacement theorem gives a nonzero `δ` with
  `ℜ(ψ ∘ m) = ℜ(ψ ∘ a) - δ`, while equal moduli would force equal real parts.
- `mem_rationalUnramifiedPrincipalOpen_prod`: a character lies in the principal open set of a
  finite product exactly when it lies in that of every factor.
- `exists_polynomial_ne_of_two_points`: suppose two points `g₁, g₂` of `M(k)` have
  `ψ₀(g₁) ≠ ψ₀(g₂)` for one unramified `ψ₀`. Then for all units `c₁, c₂` there is a nonzero
  polynomial off whose zero set `c₁ ψ(g₁) ≠ c₂ ψ(g₂)`. The regular function
  `c₁ ev_{g₁} - c₂ ev_{g₂}` is turned into a polynomial by the published
  `rationalRegularPolynomial`. The polynomial is nonzero: otherwise the function would
  vanish at the trivial character and at `ψ₀`, giving `c₁ = c₂` and then `ψ₀(g₁) = ψ₀(g₂)`.
- `exists_polynomial_pieceSeparation`: the separation for one nonidentity piece. Factor `a`
  through a split component `a'` of the intersection Levi
  (`exists_isSplitComponent_factor`) and take the point `t` of
  `exists_norm_ne_of_nonidentity`. The set `Θ` of normalized Jacquet exponents of `ρ` along
  `P'` is finite. The Jacquet module is admissible (`arbitraryParabolicJacquetAdmissibility`)
  and finitely generated: `leviJacquetFiniteType`, with `moduleFinite_asModule_of_isIrreducible`
  for `ρ`. The set `Ω` of generalized `A(k)`-eigencharacters of `ρ` is also finite. The
  polynomial is the product over `(θ, ω) ∈ Θ × Ω` of the two-point polynomials for
  `g₁ = m t`, `g₂ = a t`, `c₁ = θ(g t)`, `c₂ = ω(t)`. Now suppose `χ` is an eigencharacter of both
  `ρψ` and the piece at `ρψ`. Untwisting `ρψ` (`isGeneralizedEigencharacter_twist_iff`) gives
  `χ = ω · (ψ ∘ a)` with `ω ∈ Ω`. The published
  `exists_untwisted_sourceJacquetExponent_of_twisted_piece` gives
  `χ = (θ ∘ g) · (ψ ∘ m)` with `θ ∈ Θ`. Evaluating at `t` contradicts the factor of
  `(θ, ω)`.
