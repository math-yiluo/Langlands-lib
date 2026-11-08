# Cuspidal detection in the Gelfand–Graev representation of a product Levi

Internal helper module for the proof of
`Langlands.RankinSelberg.SupercuspidalProductCompletenessStatement`.

## Main theorem

`leviGelfandGraev_cuspidalDetection T B ψ hn` has the following hypotheses:

- a prime `p` and `F : PadicField p` with realization `T`, whose topology is installed;
- a positive rank `n` and a block shape `B` of `n`;
- an arbitrary additive character `ψ : AddChar F ℂ`;
- `x ∈ LeviGelfandGraevFunctions B ψ` with `x ≠ 0`;
- the cyclic subrepresentation `Cyclic.orbitSpan (leviGelfandGraev B ψ) x` satisfies
  `CuspidalSupport.IsLeviQuasicuspidal B`.

The conclusion provides:

- irreducible supercuspidal block representations `A i : SupercuspidalRep (B.size i)`, with
  carriers in an arbitrary universe `uW`;
- an intertwiner `Φ : leviGelfandGraev B ψ → B.blockTensor (A i)` with `Φ x ≠ 0`.

## Proof

Write `M = B.Levi F` and `M° = ker ν = determinantUnitSubgroup T B`, where
`ν = leviDeterminantNorm T B`. The product unipotent subgroup and every refined unipotent radical
lie in `M°` (`leviUpperUnipotent_le_ker`, `refinedUnipotent_le_ker`). The proof proceeds as
follows.

1. **Graded pieces.** `isLeviQuasicuspidal_orbitSpan_gradedPiece` shows that every graded piece
   of `x`, in the sense of `CompactGrading`, again has quasicuspidal cyclic span.
   - The graded projections commute with refined unipotent radicals, so they preserve the ambient
     coinvariant relations.
   - The relations of the span of a piece lie in the ambient relations.
   - Injectivity of coinvariants of smooth representations (`coinvariants_map_injective_of_smooth`
     with `refinedUnipotent_finite_containment`) concludes.
2. Choose a nonzero piece of degree `ν t` and set `y = R(t) gradedPiece (ν t) x`. Its span is the
   span of the piece (`orbitSpan_translate`).
3. **A map on `M°`.** `exists_determinantUnit_map_ne_zero` takes a smooth `M`-representation `A`
   and a nonzero `y ∈ A` with quasicuspidal span. It produces an irreducible quasicuspidal
   quotient `π` of the span of `y` and a linear map `f0 : A → π` that intertwines `M°`, with
   `f0 y ≠ 0`. The construction:
   - `leviQuasicuspidalDecomposition` gives `A = S ⊕ Q`. The vector `y` lies in `S`
     (`mem_of_isLeviQuasicuspidal_orbitSpan`): the projection of its span to `Q` is a
     quasicuspidal subquotient of `Q`, hence zero.
   - By `leviHarishChandraTheorem`, the restriction of `S` to `M°` has compact coefficients. Then
     `determinantUnitTotalIsotypic_exhaust` and `isotypicSemisimplicityTheorem` make it
     semisimple, and `exists_isCompl_of_top` gives an `M°`-complement of the `M°`-span of `y`.
   - `π` is the quotient of the span of `y` by a maximal subrepresentation
     (`exists_isCoatom_subrepresentation`, `isIrreducible_of_isCoatom`).
   - `f0` projects to `S`, then to the `M°`-span of `y`, then to `π`.
4. **Twist.** `exists_twistedExtension_ne_zero` applies, since the coordinate characters separate
   points of `(ℝ≥0ˣ)^k` (`separating_characters`). It gives `χ` with `twistedExtension χ x ≠ 0`,
   an intertwiner into `π' = (χ ∘ ν)⁻¹ ⊗ π`.
5. **Factorization.** `π'` is smooth and irreducible (`SmoothRep.isIrreducible_twist_iff`). It is
   quasicuspidal (`Jacquet.subsingleton_coinvariants_twist_iff`, because `χ ∘ ν` is trivial on
   refined unipotent radicals), hence admissible
   (`LeviAdmissibility.irreducibleQuasicuspidalLeviAdmissibility`). Then
   `padicLeviCuspidalFactorization` makes it equivalent to an external tensor product of
   irreducible supercuspidal representations in universe `uW`. Composing gives `Φ`.

## Provenance

This is an internal result. It replaces, in the form needed here, the cuspidal-detection step in
the proof of Whittaker completeness: a nonzero cuspidal vector of a Gelfand–Graev representation
is not killed by all maps to supercuspidal representations. The ingredients are the
Bernstein–Zelevinsky decomposition and the Harish-Chandra compactness criterion (BZ76 §3, BZ77
§2.4) in the Library's published forms.
