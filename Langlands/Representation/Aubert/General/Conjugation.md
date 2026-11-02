# Conjugation compatibility of normalized induction and Jacquet restriction

Implementation and documentation: Worker 23 (task
`593ef603-6672-4424-976c-14e11e920d9c`, the initial adapter unit of the general
Aubert program `46df6a68-5db4-4428-8044-05151d6ce1f6`).

This module proves that the normalized functors of
[`Aubert.General.Parabolic`](Parabolic.md) are compatible with conjugation by an
element `g` of the ambient group. It also proves the corresponding identities
of the exact-K0 maps of [`Aubert.General.AlternatingOperator`](AlternatingOperator.md).
These are intrinsic laws of the generic layer. No reductive structure, no
unimodularity and no finite-length statement is assumed beyond what each
declaration names.

## Setting

`G` is a locally compact nonarchimedean group. There are two actual semidirect
decompositions, `h : IsSemidirectDecomposition P M U` and
`h' : IsSemidirectDecomposition P' M' U'`, with closed `U` and `U'`. The
primed subgroups are the conjugates by `g`. This is stated by three membership
hypotheses of the form used by `conjugationEquiv`:

    hPP' : ∀ x, x ∈ P' ↔ g⁻¹ x g ∈ P,
    hMM' : ∀ x, x ∈ M' ↔ g⁻¹ x g ∈ M,
    hUU' : ∀ x, x ∈ U' ↔ g⁻¹ x g ∈ U.

Both decompositions are inputs. The module does not derive `h'` from `h`. For
the published dynamic subgroups both come from
`dynamic_isSemidirectDecomposition`. `ᵍ(-)` denotes the published transport
`conjugationFunctor g hMM'`, `(ᵍσ)(x) = σ(g⁻¹ x g)`.

## Moduli and projections

* `mulEquivHaarChar_trans_symm e φ` shows that for a topological group
  isomorphism `e : H ≃ₜ* K` and `φ : K ≃ₜ* K`, Mathlib's Haar scaling factor
  satisfies `mulEquivHaarChar (e⁻¹ ∘ φ ∘ e) = mulEquivHaarChar φ`. The proof
  pushes a regular Haar measure `μ` of `K` forward to `ν = e⁻¹_* μ`, which is
  Haar and regular on `H`. It then applies
  `mulEquivHaarChar_smul_map` to `ν`, maps the identity back along `e`, and
  compares the two scalars with `haarScalarFactor (c • μ_φ) μ_φ = c`, where
  `μ_φ = φ_* μ`.
* `closedNormalizerCharacter_conj` is the Haar modulus statement
  `δ_{U'}(x) = δ_U(g⁻¹ x g)` for `x` in the normalizer of `U'`. Conjugation by
  `x` on `U'` is `e⁻¹ ∘ (conjugation by g⁻¹xg on U) ∘ e`, with
  `e = conjugationEquiv g hUU'`. Then the previous lemma applies, with the
  Borel structures used by the published `HaarModulus.normalizerCharacter`.
* `closedRestrictCharacter_conj`, `closedHalfCharacter_conj` and
  `closedInverseHalfCharacter_conj` give the same identity for the restriction
  to `M'`, for `δ^{1/2}` and for `δ^{-1/2}`, each composed with
  `conjugationEquiv g hMM'`.
* `projection_conj` shows that the Levi projections correspond:
  `g⁻¹ proj'(p) g = proj(g⁻¹ p g)`. The proof uses `projection_eq_iff` and
  `projection_inv_mul_mem`.

## Jacquet restriction

* `coinvariantsTranslate g hUU' ρ` is the linear map `[v] ↦ [ρ(g) v]` from the
  `U`-coinvariants to the `U'`-coinvariants. It is well defined because
  `ρ(g)(ρ(u)v - v) = ρ(g u g⁻¹)(ρ(g)v) - ρ(g)v` and `g u g⁻¹ ∈ U'`.
  `coinvariantsTranslate_mk` records the formula on classes.
  `coinvariantsTranslateEquiv` is the linear equivalence whose inverse is the
  translation by `g⁻¹`. `conj_inv_iff` supplies the inverse membership
  relation.
* `jacquetConjugationIsoApp` is the component `ᵍ(r_P A) ≅ r_{P'} A`. It
  intertwines because `ρ(g) ρ(g⁻¹ x g) = ρ(x) ρ(g)` and because of
  `closedInverseHalfCharacter_conj`.
* `jacquetConjugationIso h h' g hMM' hUU' hU hU'` is the natural isomorphism

      jacquetFunctor h hU ⋙ conjugationFunctor g hMM' ≅ jacquetFunctor h' hU'

  on the full smooth category. Naturality is the `G`-equivariance of maps.
  `jacquetConjugationIso_hom_mk` records `[v] ↦ [A(g) v]`.

## Induction

* `coindTranslate g hPP' σ σ' hσ` is left translation `f ↦ f(g⁻¹ ·)` from
  `P`-covariant to `P'`-covariant functions. Its input is a representation
  `σ'` of `P'` with `σ'(p') = σ(g⁻¹ p' g)`. It commutes with right
  translation. Covariance holds because `g⁻¹ p' y = (g⁻¹ p' g)(g⁻¹ y)`.
* `inducingRepresentation_conj` checks that hypothesis for the inducing
  representations: `δ'(p)^{1/2} σ(g⁻¹ proj'(p) g)` equals
  `δ(g⁻¹pg)^{1/2} σ(proj(g⁻¹ p g))`, by `closedHalfCharacter_conj` and
  `projection_conj`.
* `inductionConjugationIsoApp` is the component `i_P A ≅ i_{P'} (ᵍA)`. It is
  `smoothMap` of `coindTranslate` on the smooth parts, with inverse the
  translation by `g⁻¹`.
* `inductionConjugationIso h h' g hPP' hMM' hUU' hU hU'` is the natural
  isomorphism

      normalizedInductionFunctor h hU ≅ conjugationFunctor g hMM' ⋙ normalizedInductionFunctor h' hU'

  on the full smooth category. Naturality is postcomposition.
  `inductionConjugationIso_hom_eval` records `f ↦ (y ↦ f(g⁻¹ y))`.

## Exact K0

Both statements are at the saturated carrier universe `max uG uV` of
`inductionK0`/`jacquetK0`. Their finite-length and exactness hypotheses for
both decompositions are explicit arguments, exactly as in those maps.

* `inductionK0_comp_conjugationK0`:
  `(inductionK0 h' ..).comp (conjugationK0 g hMM') = inductionK0 h ..`.
* `conjugationK0_comp_jacquetK0`:
  `(conjugationK0 g hMM').comp (jacquetK0 h ..) = jacquetK0 h' ..`.

Each follows from the published `FiniteLengthGrothendieckGroup.map_comp` and
`map_eq_of_iso`, applied to the natural isomorphisms above.
`conjugationK0` is the published pullback map, and the published
`pullbackFunctor_preservesFiniteLength` and
`pullbackFunctor_preservesShortExact` supply its preservation properties.

## Provenance

This is a derived, internal result: transport of structure along an inner
automorphism. The sources use it without a displayed statement. For example,
Renard VI.2.1 (Remarque 1, printed p. 137, and "par conjugaison" in the proof of
the Théorème, printed p. 138) reduces statements about `r^G_P` to standard
parabolics by conjugation. The normalizations being compared are those of
`Parabolic.md`: the Haar modulus convention of Bernstein–Zelevinsky 1977 §1.7,
the localization of §1.8(b), and the induction character on `P` described in
"Source identification" there. The compatibility proved here holds for the
generic functors, with no unimodularity assumption.

## Sources

* D. Renard, *Représentations des groupes réductifs p-adiques* (2026 version),
  registered as `renard-2026-representations-groupes-reductifs-padiques`:
  VI.2.1, printed pp. 137–138 (PDF pp. 143–144; printed = PDF − 6).
* I. N. Bernstein and A. V. Zelevinsky, *Induced representations of reductive
  p-adic groups I*, Ann. Sci. ENS 10 (1977), registered as
  `bernstein-zelevinsky-1977-induced-i`: §1.7 (modulus of an automorphism),
  §1.8 (normalized induction and localization), printed p. 444.
