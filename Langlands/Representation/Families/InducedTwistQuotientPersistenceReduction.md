# Persistence of the inducing exponent, from four named inputs

Author: Worker 5120.

This module proves one theorem,
`Langlands.Renard.AlgebraicFamily.inducedTwistQuotientPersistence_of_statements`:

```
GenericInducedIrreducibilityStatement.{u, max u v} →
Plancherel.WallUnramifiedTwistSurjectivityStatement.{u} →
RationalParabolicGalleryAvoidingStatement.{u} →
LeviSecondAdjointnessStatement.{u, v} →
InducedTwistQuotientPersistenceStatement.{u, v}
```

The four hypotheses are published proof targets, not theorems:

- Renard VI.8.5: generic irreducibility of induction from a maximal parabolic of a
  supercuspidal representation, applied at carrier universe `max u v`;
- wall twist surjectivity: at a rank-one wall where a split component `A_M` is not central,
  restriction maps `X(M) × X(M₁)` onto `X(L)`;
- existence of rank-one galleries between two parabolics with Levi `L` that agree in the
  centralizer of a central split torus `b` of `L`, using only walls where `b` is not
  central;
- Bernstein's second adjointness `i_P ⊣ r_P̄` for opposite parabolics.

The module does not prove persistence unconditionally. Its conclusion is the persistence
half of `InducedTwistQuotientExponentStatements`. With the published exclusion proof, it
feeds `irreducibleInducedTwistExistence_of_quotientExponentStatements`.

## Mathematical argument

Let `ρ` be irreducible and admissible on `M(k)`, with `P = MN` and a split component
`A_M`. Write `I_ψ = i_P(ρψ)`.

1. **Cuspidal data.** Choose a parabolic `Q = LV` of `M` and an irreducible supercuspidal
   `σ` of `L(k)` with `ρ ↪ i^M_Q(σ)`. Then `ρψ ↪ i^M_Q(σψ_L)`, where `ψ_L = ψ|_L`. Choose
   a split component `A_L` of `L`, and let `χ_0(ψ)` be the central character of `σψ_L`
   on `A_L`.
2. **Two parabolics with Levi `L`.** `R₀ = Q N` lies in `P`. `R₁ = Q N̄` lies in the
   opposite parabolic `P̄`. Both meet `M` in `Q`. So `R₀` and `R₁` agree inside the
   centralizer `M` of `A_M`, and the gallery input joins them by walls where `A_M` is not
   central.
3. **Start.** For `S ≠ ⊤`, second adjointness embeds `ρψ` in `r_P̄(I_ψ/S)`. Applying
   `r^M_Q` shows that `χ_0(ψ)` is an `A_L`-exponent of `r_{R₁}(I_ψ/S)`.
4. **Walls.** At each wall, second adjointness in the wall Levi `M₁` moves the exponent
   from one side to the other. This needs `i^{M₁}_{Q₁}(C)` to be irreducible for the
   irreducible pieces `C` of the Jacquet modules with that exponent. Since
   `I_ψ ↪ i_{R₀}(σψ_L)`, the pieces are conjugates of `σψ_L` by the finitely many
   representatives of `N_G(L)(k)/L(k)`. They are supercuspidal, and VI.8.5 with wall
   surjectivity makes the inductions irreducible off one nonzero polynomial per wall.
5. **End.** At `R₀ ⊂ P`, the exponent `χ_0(ψ)` of `r_{R₀}(I_ψ/S) = r^M_Q(r_P(I_ψ/S))`
   restricts (Renard VII.1.1 (ii)) to an `A_M`-exponent of `r_P(I_ψ/S)`. The same
   restriction applied to `r^M_Q(ρψ) ↠ σψ_L` shows that it is an `A_M`-exponent of `ρψ`.

The polynomial is the product of the wall polynomials. It depends on `ρ` and the choices
above, but not on `ψ` or `S`.

## Lean proof

After `intro`, the proof does the following:

- applies the published `leviCuspidalEmbedding` to `ρ` (giving `Q`, `L`, `σ`, `J ↠ σ`
  and `ρ ↪ i^M_Q(σ)`);
- applies `exists_splitComponent_factor` (`b_L`, `b`, `e`);
- shows `σ` admissible: `J` is admissible, and `isAdmissible_of_surjective_coefficients`
  applies with `exists_compact_openSubgroup_le`;
- sets the twists `θ ψ = leviRestrictedCharacter q lQ ψ`. Supercuspidality of the twists
  comes from `properJacquet_subsingleton_unramifiedTwist` and `twist_eq_of_eq`. The
  exponents `χ0 ψ` come from `exists_isGeneralizedEigencharacter_of_isAdmissible`;
- builds `ρψ ↪ i^M_Q(σ ⊗ θ ψ)` from `twistIntertwining` and
  `leviInductionUnramifiedTwistIso`;
- obtains `R₀` and `R₁` from the published `leviParabolicExtension`, applied to `P` and
  to the opposite parabolic from `InducedTwistsDetection.exists_opposite_parabolic`;
- takes representatives of `N_G(L)(k)/L(k)` from `leviNormalizerFiniteQuotient`;
- builds `I_ψ ↪ i_{R₀}(σ ⊗ θ ψ)` from `leviInductionMap` (cross-universe, injective) and
  induction in stages (`leviParabolicTransitivity`);
- shows the quotients `I_ψ/S` admissible: `leviInductionFunctor_obj_isAdmissible_of_quotientCompactStatement`
  and surjectivity of the quotient map.

The gallery hypothesis is applied to `b`. Its centralizer condition is checked with the
published `IsSplitComponent.torusCentralizer_comp_eq_of_parabolicDynamic` (the centralizer
of `A_M` is `M`) and the intersection clauses of the two extensions.

`exists_polynomial_persistenceInvariant_of_gallery` is then applied to the family
`Z ψ S = I_ψ/S` (`S ≠ ⊤`) with exponents `χ0 ψ`. Finite length comes from
`pieces_of_supercuspidal_normalizer` and `isSubquotient_leviJacquet_quotient_of_injective`.
The wall hypothesis is `exists_polynomial_wall_isIrreducible`. The invariant at `range r₁`
is `persistenceInvariant_opposite`. The conclusion at `range r₀` gives the exponent of
`r_P(I_ψ/S)` by `isGeneralizedEigencharacter_of_persistenceInvariant`. The exponent of `ρψ`
comes from `isGeneralizedEigencharacter_jacquet_of_ne_zero_induction` and
`isGeneralizedEigencharacter_of_leviJacquet_restrict`.

The theorem uses only the axioms `propext`, `Classical.choice` and `Quot.sound`.

## Provenance and dependency boundary

The proposition is derived from Takuya Konno, *A note on the Langlands classification and
irreducibility of induced representations of p-adic groups*, Kyushu J. Math. 57 (2003),
Theorem 4.2 and its proof (registered `konno-2003-langlands-classification`). Konno
compares the Jacquet modules of a submodule and a quotient with the pieces of the Bruhat
filtration. The implemented route differs. It moves an `A_L`-exponent from the opposite
parabolic to `P` along a rank-one gallery, using second adjointness at each wall and
Renard VI.8.5 for genericity. It needs VI.8.5, second adjointness, wall twist surjectivity
and gallery existence as stated hypotheses. Every other result used is proved in the
Library. The supporting modules are `InducedTwistPersistence{Algebra, Endpoints, Wall,
Pieces, Genericity, Gallery, Assembly, WallPolynomial}`. No target Lean/Markdown pair is
changed.
