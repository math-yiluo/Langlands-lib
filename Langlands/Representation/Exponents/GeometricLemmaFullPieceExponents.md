# Exponents of the full pieces of the represented geometric lemma

This internal unit supports the proof task on the unitarizable-constituent step of
Renard, Théorème VII.1.3 (printed pp.224–226, PDF pp.230–232). There Renard reads off
the Jacquet modules of `i_P^G ρ` along the parabolics with Levi factor `M` from the
geometric lemma VI.5.1: only the pieces whose source parabolic is all of `M` survive,
and each is a conjugate of `ρ`. This module records the exponent half of that
identification. Its provenance is the published constructions it combines:

- `GeometricLemmaIntersectionDatum.exists_isNormalizedJacquetExponent_of_piece`;
- `normalizedJacquetFunctor_obj_apply_of_mem_center`;
- `isNormalizedJacquetExponent_iff`;
- `splitComponentPointsMap_mem_center_of_isIso`;
- `IsRationalLeviSubgroup.isIso_of_isIso_parabolic`.

It asserts no new source translation.

## Central values without a unitary central character

The Library's `normalizedJacquet_generalizedEigencharacter_apply_eq_centralCharacter`
assumes a unitary central character. The two lemmas here use only that one point acts
by a scalar.

- `normalizedJacquet_generalizedEigencharacter_apply_eq_of_smul` works for a locally
  compact nonarchimedean group `Γ`, closed `N` and normalizing `L`. Let `χ` be a
  generalized eigencharacter of the normalized Jacquet module along `z : B →* L`. Let
  `z b` be central in `Γ` and act on `π` by a scalar `s`. Then `χ b = s`.
  - The normalized action of a central point has trivial half-modulus, so `z b` acts by
    `s` on the Jacquet module.
  - Some nonzero vector `v` satisfies `((z b) - χ b)^d v = 0`. This becomes
    `(s - χ b)^d • v = 0`, hence `χ b = s`.
- `normalizedJacquetExponent_apply_eq_of_smul` is the same statement for an actual
  normalized Jacquet exponent of a represented parabolic. Its point is the split-component
  point `splitComponentPointsMap (l ≫ p) a t`.

The proposition `NormalizedJacquetCentralScalarStatement.{uG, uV, uB}` states the first
lemma over every such `Γ` (group universe `uG`, carrier universe `uV`, index group
universe `uB`). `normalizedJacquetCentralScalar` proves it by that lemma.

Neither lemma assumes irreducibility, admissibility or unitarity. The scalar action is a
hypothesis. In the intended application the field is a nonarchimedean local field
(`ValuativeRel F` and `IsNonarchimedeanLocalField F`, as in Renard VII.1.3). There the
published `leviPoint_scalarEndomorphism` (Schur's lemma) makes every central point of the
Levi act by a scalar on an irreducible smooth representation. This module does not use
that theorem, and over the broader fields allowed here a central point of an irreducible
smooth representation need not act by a scalar.

## Exponents of a full piece

`GeometricLemmaIntersectionDatum.piece_exponent_apply_eq_of_isIso` takes a datum `D`
for `(P, Q)` and the double coset of `z`. It assumes:

- the source parabolic `p' : P' ⟶ M` is an isomorphism;
- `lQ' ≫ q' : L' ⟶ L` is an isomorphism;
- `a : A ⟶ L` is a split component of `L`;
- `σ` is a smooth representation of `M(F)` whose Jacquet module along `P'` is
  admissible;
- `χ` is a generalized eigencharacter of `A(F)` on the piece at `σ`;
- the point `(a ≫ (lQ' ≫ q')⁻¹ ≫ φ ≫ l' ≫ p')(t)` of `M(F)` acts on `σ` by a scalar
  `s`.

It concludes `χ t = s`. The datum's equation
`φ ≫ l' ≫ p' ≫ l ≫ p = lQ' ≫ q' ≫ lQ ≫ q ≫ innerIso z` identifies the image of that
point in `G(F)` with the `z`-conjugate of `a(t)`.

The proof applies the published piece-exponent transfer with `f = 𝟙` and the split
component `a' = a ≫ (lQ' ≫ q')⁻¹` of `L'`, which satisfies
`a' ≫ lQ' ≫ q' = a`. This gives an exponent `ψ` of `σ` along `P'` for the split
component `a' ≫ φ`, with `ψ = χ`. Since `p'` is an isomorphism, so is `l'`, because `M`
is connected reductive. The split-component point of `a' ≫ φ` is therefore central in
`M(F)`, and the central-value lemma gives `ψ t = s`.

## Scope

The ambient group `G` is affine. `G(F)` carries the canonical topology, assumed locally
compact and nonarchimedean, and the field is Hausdorff. No local-field structure,
reductivity of `G` or unitarity is used. Fullness of `lQ' ≫ q'` and admissibility of
the source Jacquet module are hypotheses. The first follows from Worker 1658's
`isIso_q'_of_isIso_p'_of_iso` and `isIso_lQ'_of_isIso_p'_of_iso` when `M ≅ L`. This
module does not identify the piece itself with a conjugate of `σ` as a representation,
and it does not count the surviving pieces.
