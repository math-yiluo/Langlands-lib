# Translation-difference lifting when only finitely many translation differences are trivial

Authors: Worker 3613, adapting Worker 2029's proof of
`Langlands.AbelianScheme.algClosedFieldTranslationDifferenceLifting_of_cube` (Task 2029,
module `Langlands.AlgebraicGeometry.Picard.AlgClosedFieldTranslationDifferenceLiftingProof`).

Module `Langlands.AlgebraicGeometry.Picard.FiniteTranslationDifferenceLifting`, namespace
`Langlands.AbelianScheme`.

## Role and provenance

This is a support module of
`Langlands.AlgebraicGeometry.Picard.FieldFiniteMumfordMapSurjectiveProof`, the proof of `Langlands.AbelianScheme.FieldFiniteMumfordMapSurjectiveStatement`. It is the
two-projection argument from the proof of Proposition (7.21) in Edixhoven, van der Geer and
Moonen, *Abelian Varieties* (registered source
`edixhoven-vandergeer-moonen-abelian-varieties-draft`), printed pp.105–106 (PDF pp.109–110).
That proof uses Lemma (7.19) and Fact (7.20) on printed p.105.

The source states the result for an ample line bundle `L`. Ampleness is used only to know
that the set `K(L)` of rational points `x` with `t_x^* L ≅ L` is finite (Lemma (2.19),
printed p.23). The theorem of the square is used only to know that every translation
difference `t_x^* L ⊗ L^{-1}` is translation invariant. In this module both facts are
explicit hypotheses, `hD` and `hF`, and ampleness is not assumed. The proof module
`FieldFiniteMumfordMapSurjectiveProof` applies the theorem to a base change `A_Ω` of an
abelian variety along an algebraically closed field `Ω`. There `hD` follows from the
Picard-zero property of the Mumford family, and `hF` follows from finiteness of the Mumford
map.

## Declarations

- `not_isZero_relativeCohomology_zero_trivial K X x`: for a scheme `X` over `Spec K`, where
  `K` is a field, with a rational section `x`, the degree-zero relative cohomology of the
  trivial line bundle is not zero.
- `translationDifferenceLifting_of_finite preservation K A L N evaluation hD hF P hP`. Let `K`
  be algebraically closed, `A` an abelian scheme over `Spec K`, and `L`, `N` line bundles with
  `evaluation : L ⊗ N ≅ 𝒪`. Write `D(x) = t_x^* L ⊗ N` for a rational point `x`. Assume:
  - `hD`: every `D(x)` is translation invariant;
  - `hF`: the set of rational points `x` with `D(x)` trivial is finite.

  Then every translation-invariant line bundle `P` is isomorphic to `D(x)` for some rational
  point `x`.

## Proof

`not_isZero_relativeCohomology_zero_trivial`: by `relativeCohomologyZeroIso` and
`relativeGlobalSectionsIso`, the degree-zero cohomology of `𝒪_X` is identified with the
global functions `Γ(X, ⊤)`. If it were zero, then `1 = 0` in `Γ(X, ⊤)`. Pulling functions
back along the section `x` and composing with `ΓSpecIso` gives a ring homomorphism
`Γ(X, ⊤) → K`, so `1 = 0` in `K`, which is impossible.

`translationDifferenceLifting_of_finite`: suppose that no `D(x)` is isomorphic to `P`.

1. Choose an inverse `R` of `P` with `P ⊗ R ≅ 𝒪`
   (`LineBundle.exists_tensorObj_iso_structureSheaf`). `R` is translation invariant
   (`GroupScheme.isTranslationInvariant_tensorInverse`). In the group of isomorphism classes
   of line bundles, `[L][N] = 1` and `[P][R] = 1`.
2. On `A ×_K A` (`pullback A.X.hom A.X.hom`) put
   `Q = m^* L ⊗ fst^* N ⊗ snd^* N ⊗ snd^* R`, where `m` is `mumfordAddition A`.
3. First projection. By `fieldTwistedMumfordFibreRestriction` (first part), the restriction
   of `Q` to the fibre over `x` is `D(x) ⊗ R`. It is translation invariant, by `hD` and
   `GroupScheme.isTranslationInvariant_tensor`. It is not trivial: otherwise cancelling `[R]`
   against `[P][R] = 1` gives `D(x) ≅ P`. So all its cohomology vanishes
   (`algClosedFieldTranslationInvariantCohomologyVanishing`). The first-projection theorem
   `algClosedFieldSquareFirstProjectionAcyclicity` then gives that all cohomology of `Q` over
   `K` vanishes.
4. Second projection. By `fieldTwistedMumfordFibreRestriction` (second part), the restriction
   of `Q` to the fibre over `x` is `D(x)`. Let `F` be the finite set of points `x` with `D(x)`
   trivial (`hF`). For `x ∉ F`, `D(x)` is translation invariant and not trivial, so its
   cohomology vanishes. The finite-support detection theorem
   `algClosedFieldSquareSecondProjectionFiniteSupportDetection`, applied with step 3, then
   gives vanishing of the cohomology of `D(x)` for every rational `x`.
5. At the origin `x = 1`, translation is the identity (`GroupScheme.translation_one`,
   `LineBundle.pullbackHom_id`). So `[D(1)] = [L][N] = 1` and `D(1)` is trivial. Step 4 makes
   `H⁰` of the trivial line bundle zero. This contradicts
   `not_isZero_relativeCohomology_zero_trivial` at the unit section.

The proof follows Worker 2029's proof line by line. The only changes are that the finiteness
of `F` and the invariance of `D(x)` are hypotheses, and that `F` is the set of points with
`D(x)` trivial. In Worker 2029's version `F` is the set of points with `t_x^* L ≅ L`. The
step for `x ∉ F` therefore uses `x ∉ F` directly. Worker 2029's version needs a cancellation
argument there.
