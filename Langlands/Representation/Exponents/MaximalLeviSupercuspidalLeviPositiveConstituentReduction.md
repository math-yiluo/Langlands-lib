# The good constituent of Renard VII.1.3 from the geometric lemma

Author: Worker 1714. Module
`Langlands.Representation.Exponents.MaximalLeviSupercuspidalLeviPositiveConstituentReduction`.
It is an internal conditional reduction for the proof of Renard VII.1.3.

## Statements

`MaximalLeviSupercuspidalLeviPositiveConstituentReductionStatement` (namespace
`Langlands.Aubert.General.RepresentedParabolic`) is the implication

```lean
RepresentedGeometricLemmaStatement.{u, v} →
  MaximalLeviSupercuspidalInductionLengthTwoStatement.{u, v} →
    MaximalLeviConeComplementStatement.{u} →
      ParabolicSelfNormalizerStatement.{u} →
        CenterSplitComponentCompactnessStatement.{u} →
          MaximalLeviSupercuspidalLeviPositiveConstituentStatement.{u, v}
```

`maximalLeviSupercuspidalLeviPositiveConstituent_of_geometricLemma` proves it. The five
premises are published statements, used unchanged; none is proved here.

- `RepresentedGeometricLemmaStatement` is the geometric lemma (Renard VI.5.1–VI.5.3) for
  represented parabolics: `r_Q ∘ i_P` is glued from the pieces of the double cosets
  `P(F) z Q(F)`.
- `MaximalLeviSupercuspidalInductionLengthTwoStatement` gives a short exact sequence
  `π₁ ↪ i_P ρ ↠ π₂` with `π₁, π₂` irreducible when `i_P ρ` is reducible.
- `MaximalLeviConeComplementStatement` (module
  `Langlands.GroupScheme.Rational.MaximalLeviConeComplementStatement`) concerns an actual
  maximal proper parabolic `P = MN` with split component `a`. Take two parabolics with Levi
  factor `M` and presentations for `a` whose positive cones both miss a nonzero
  `x ∈ X^*(A) ⊗ ℝ` that pairs to zero with the cocharacters central in `G`. Then the two
  parabolics have the same range in `G`, and so do their unipotent radicals.
- `ParabolicSelfNormalizerStatement` says that the range of a parabolic subgroup is its own
  normalizer.
- `CenterSplitComponentCompactnessStatement` says that the centre of a connected reductive
  group is compact modulo a split component.

The conclusion `MaximalLeviSupercuspidalLeviPositiveConstituentStatement` (published) is
Renard's choice between `π₁` and `π₂`. For an actual maximal proper rational parabolic
`P = MN`, an irreducible supercuspidal `ρ` of `M(F)` with no unitary central character,
and `i_P ρ` reducible with a unitary central character, it gives an irreducible
subrepresentation or quotient `W` of `i_P ρ` with `HasPositiveLeviJacquetExponents (l ≫ p) W`.
That is, along every parabolic `Q` with Levi factor `M` (`lQ ≫ q = l ≫ p`), every
normalized Jacquet exponent of `W` has real part in the positive cone of `Q`.

## Auxiliary lemmas

Namespace `Langlands.ScalarGraded`:

- `intertwiningMap_pow_sub_smul_apply`: an intertwining map `T` commutes with every power
  of `ρ(g) - c`.

Namespace `Langlands.RepFunctorFiltration`. Here `s` is a finite filtration of a functor
`F : C ⥤ Rep k Γ`, `e i` identifies its graded pieces at `X` with `R i`, and
`ScalarGraded.ZeroOrScalarIrreducible R κ c` says that each `R i` is zero, or irreducible
with `κ t` acting by the scalar `c i t`.

- `exists_grade_of_injective`: a generalized eigencharacter `χ` of `σ₁ ∘ κ`, for an
  injective intertwining map `σ₁ → F.obj X`, is the scalar character `c i` of a nonzero
  piece.
- `exists_grade_of_surjective`: the same for a surjective intertwining map `F.obj X → σ₂`.
- `exists_two_grades_of_comp_eq_zero`: if `T₁ : σ₁ → F.obj X` is injective,
  `T₂ : F.obj X → σ₂` is surjective and `T₂ ∘ T₁ = 0`, a common generalized eigencharacter
  of `σ₁ ∘ κ` and `σ₂ ∘ κ` is the scalar character of two distinct nonzero pieces.

These are the vector-level lemmas `exists_grade_of_pow_apply_eq_zero`,
`exists_grade_of_pow_apply_mem` and `exists_two_grades` of module
`Langlands.Representation.Filtration.ScalarGradedOccurrences`, applied to `T v`, to a
preimage under `T`, and with `E = ker T₂`.

Namespace `Langlands.Aubert.General.RepresentedParabolic`. Fix `P = MN` and a parabolic
`Q` with Levi factor `M` and `lQ ≫ q = l ≫ p`, intersection data `D i` for representatives
`z i`, an irreducible supercuspidal `ρ`, a split component `a : A ⟶ M`, and a character
`ω_A` of `A(F)` by which `a` acts on `ρ`.

- `exists_zeroOrScalarIrreducible_pieces`: there are scalars `c` such that the pieces
  `(D i).pieceFunctor.obj ρ` are zero or irreducible with `a` acting by `c i`. For a nonzero
  piece there are `ψ : M ≅ M` and `e : A ≅ A` with `ψ ≫ l ≫ p = l ≫ p ≫ Int(z i)`,
  `e ≫ a = a ≫ ψ` and `c i = ω_A ∘ e`.
- `exists_conjugation_of_injective` (locating, subrepresentation): if `IsGluedFrom` holds
  for `r_Q ∘ i_P` and these pieces, and `r_Q(f)` is injective for `f : W ⟶ i_P ρ`, then every
  normalized Jacquet exponent `χ` of `W` along `Q` is `ω_A ∘ e` for some `i`, `ψ`, `e` as
  above.
- `exists_conjugation_of_surjective`: the same for `g : i_P ρ ⟶ W` with `r_Q(g)` surjective.
- `false_of_isNormalizedJacquetExponent_of_isShortExact` (uniqueness): let `cc` be the
  bijection of `Fin n` with the double cosets `P(F)\G(F)/Q(F)`, with `z i` in the coset
  `cc i`. Let `f : W₁ ⟶ i_P ρ`, `g : i_P ρ ⟶ W₂` stay short exact under `r_Q`, and let `ω_A`
  be an exponent of `W₁` and of `W₂` along `Q`. Suppose that every `w ∈ G(F)` with
  `ψ ≫ l ≫ p = l ≫ p ≫ Int(w)`, `e ≫ a = a ≫ ψ` and `ω_A ∘ e = ω_A` lies in `Q(F)`. Then
  `False`.

## Provenance

Renard, VII.1.3, proof (printed pp.224–226, PDF pp.230–232). Renard computes `r_P π₁`,
`r_P π₂` and `r_{P̄} π₁`, `r_{P̄} π₂` from the geometric lemma and concludes that one of `π₁`,
`π₂` satisfies Casselman's criterion. This module proves the same choice by contradiction,
for all parabolics with Levi factor `M`, without fixing standard representatives. The
argument through `ω_A`, the cone complement statement and the fixed-direction lemma is
internal. The fixed-direction lemma is
`MaximalLeviFixedDirectionNormalizerStatement` (module
`Langlands.Representation.Exponents.MaximalLeviFixedDirectionNormalizer`).

## The proof

Lemma proofs.

- `exists_zeroOrScalarIrreducible_pieces` applies
  `GeometricLemmaIntersectionDatum.subsingleton_or_isIrreducible_scalar` (module
  `Langlands.Representation.Geometric.LeviConjugatePiece`) to each piece and chooses the
  scalars.
- The locating lemmas turn the exponent into a generalized eigencharacter of the
  `Rep`-valued Jacquet module (`isNormalizedJacquetExponent_iff_leviJacquet`). The filtration
  of `IsGluedFrom` has graded pieces isomorphic to the pieces, so `exists_grade_of_injective`
  or `exists_grade_of_surjective` gives a nonzero piece with `c i = χ`.
- The uniqueness lemma gets `r_Q(g) ∘ r_Q(f) = 0` from exactness and two distinct nonzero
  pieces `i ≠ j` with `c = ω_A` from `exists_two_grades_of_comp_eq_zero`. For each of them
  `ω_A ∘ e = ω_A`. So the hypothesis puts its representative in `Q(F)`, and its double coset
  is that of `1`. Then `cc` and the permutation of `IsGluedFrom` give `i = j`.

Main theorem. The length-two statement gives `f : π₁ ↪ i_P ρ` and `g : i_P ρ ↠ π₂`. If
`π₁` has positive exponents, it is the answer. Otherwise assume a bad exponent `χ₁` of `π₁`
along `(Q₁, a₁)` and a bad exponent `χ₂` of `π₂` along `(Q₂, a₂)`, and derive `False`.

1. `exists_hasCentralCharacter_of_isIrreducible` gives the central character `ω` of `ρ`.
   Its restriction `ω_A = splitComponentCentralCharacter a₁ ha₁ ω` acts through `a₁`.
   `IsSplitComponent.exists_iso_comp` gives `ε : A₂ ≅ A₁` with `ε ≫ a₁ = a₂`.
2. `leviParabolicFunctorsExact` makes `r_{Q₁}(f)` injective and `r_{Q₂}(g)` surjective. The
   geometric lemma and the locating lemmas give `χ₁ = ω_A ∘ e₁` and, after composing with
   `ε`, `χ₂ = ω_A ∘ e₂`, with representatives `z₁`, `z₂`, automorphisms `ψ₁`, `ψ₂` of `M`
   and isomorphisms `e₁ : A₁ ≅ A₁`, `e₂ : A₂ ≅ A₁`.
3. Conjugate: `Q₁' = Int(z₁) Q₁` with Levi factor `ψ₁⁻¹ ≫ lQ₁` and split component `a₁`,
   and similarly `Q₂'`. Both have Levi composite `l ≫ p`.
   `isNormalizedJacquetExponent_conjugate_iff` (module
   `Langlands.Representation.Exponents.MaximalLeviExponentTransport`) makes `ω_A` an
   exponent of `π₁` along `Q₁'` and of `π₂` along `Q₂'`.
   `normalizedRealPart_notMem_positiveCone_conjugate` puts the real part `x` of `ω_A` outside
   the cones of the conjugated presentations `ParabolicRootPresentation.conjugate`.
4. `x ≠ 0`: otherwise `nonempty_unitaryCentralCharacter_of_normalizedRealPart_eq_zero`,
   with compactness of the centre modulo `A₁`, makes the central character of `ρ` unitary,
   against the hypothesis. `x` pairs to zero with the cocharacters of `A₁` central in `G`
   (`pair_normalizedRealPart_eq_zero_of_isCentral`, with the unitary central character of
   `π₁` from `unitaryCentralCharacterOfInjective`).
5. The cone complement statement gives equal ranges of the unipotent radicals of `Q₁'` and
   `Q₂'`. With the common Levi composite, `isNormalizedJacquetExponent_congr` makes `ω_A` an
   exponent of `π₂` along `Q₁'` too.
6. `mem_pointImage_of_fixes` (the fixed-direction lemma, from the cone complement and
   self-normalizer statements) gives the hypothesis of the uniqueness lemma for `Q₁'`.
   The fixed-point condition `x ∘ e = x` comes from `ω_A ∘ e = ω_A` by
   `normalizedRealPart_comp_points`.
7. The geometric lemma for `Q₁'`, exactness of `r_{Q₁'}` and the uniqueness lemma give
   `False`.
