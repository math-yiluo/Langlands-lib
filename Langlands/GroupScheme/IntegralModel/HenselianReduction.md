# Generic injectivity and Henselian surjectivity of integral reduction

This module proves two general facts about the supplied models of
`Langlands.GroupScheme.IntegralModel` and their reduction maps from
`Langlands.GroupScheme.IntegralModelReduction`. They are internal
infrastructure for the depth-zero reduction of Kaletha–Prasad,
*Bruhat–Tits Theory: A New Approach* (2023), 13.2.6 (printed p. 470 /
PDF p. 501). The second fact is the case `n = 1` of KP Lemma 8.1.3 (printed
p. 284 / PDF p. 315). KP prove that case by citing EGA IV 18.5.17 and
Bosch–Lütkebohmert–Raynaud §2.3, Proposition 5. The registered original is
`kaletha-prasad-2023-bruhat-tits-new-approach`, SHA-256
`05ad9a284a2577b34d1a270228b74dfb28f520561ae7772d8f38dddb78938732`.
No model existence assertion is made.

Throughout, `R` is a commutative ring and `K` is a field with
`IsFractionRing R K`, both in an arbitrary universe `u`, and `M` is an
`IntegralModel R K G` of a group scheme `G` over `Spec K`. Such a model
requires `R` to be a domain and its structural morphism to be affine.

`isDominant_specAlgebraMap` states that `Spec.algebraMap R K : Spec K → Spec R`
is dominant. It does not use the domain hypothesis. The proof rewrites density
of the image of `PrimeSpectrum.comap` as containment of the kernel in the
nilradical, and the kernel is zero because the fraction-field map is
injective.

`integralPointMap_injective` states that `M.integralPointMap`, from the
integral sections `G_R(R)` to the generic rational points `G(K)`, is
injective. It needs no local, Henselian or smoothness hypothesis. If two
sections have the same image, cancelling the supplied generic isomorphism
gives equal base-changed sections. By `baseChangeSectionHom_fst`, the two
underlying sections then agree after composition with `Spec K → Spec R`.
Mathlib's `ext_of_isDominant_of_isSeparated` then gives equality. It applies
because `Spec R` is reduced, the map from `Spec K` is dominant, and the affine
structural morphism is separated.

`reduction_surjective` assumes that `R` is a `HenselianLocalRing` and that the
model is smooth (`M.IsSmooth`). It states that `M.reduction`, from integral
sections to residue-field points of the actual special fibre, is surjective.
In KP's notation, `X(o) → X(f)` is surjective for the smooth model `X`. The
proof composes a residue point of the special fibre with the first pullback
projection. This gives a residue-field point `b` of the total space lying over
`Spec f → Spec R`. The published
`Langlands.CommutativeAlgebra.HenselianSections.exists_section_of_smooth_of_surjective`
lifts `b` to a section `σ` of the smooth structural morphism that restricts to
`b`. `reduction_left` and the uniqueness of pullback lifts then identify the
reduction of `σ` with the given point.

KP state Lemma 8.1.3 for the Henselian ring of integers `o` of their discretely
valued base field (Chapter 8 introduction, printed p. 283 / PDF p. 314). The
Lean theorem assumes only a Henselian local domain, with no discreteness or
completeness hypothesis. The case `n > 1` of Lemma 8.1.3, surjectivity onto
`X(o/m^n)`, is not formalized here.
