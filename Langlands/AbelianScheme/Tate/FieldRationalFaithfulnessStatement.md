# Faithfulness target for the actual full rational Tate construction

This file states the characteristic-zero, algebraically closed field case of
faithfulness needed for the Harris moduli problem. It uses the existing
`Langlands.AbelianScheme.Tate.rationalHomMap`, `rationalEndAction` and
`rationalIso`. It constructs no alternative Tate module or endomorphism algebra.

`FieldRationalFaithfulnessStatement` is a proposition. For every algebraically
closed field `Ω` of characteristic zero and actual abelian schemes `A` and `B`
over `Spec Ω`, it asserts injectivity of the existing rational linear map from
`Rationalization.Hom A B` to linear maps between their full rational Tate
modules. The test object is exactly `Over.mk (𝟙 (Spec Ω))`, so the torsion points
are all the `Ω`-valued torsion points of these abelian schemes. The inverse limit
uses all positive torsion orders through the existing predicate `fun _ => True`.
In the existing convention its rationalization is `ℚ ⊗[ℤ] TA`.

Algebraic closedness is essential to this formulation with the identity test
object: evaluating only rational torsion over an arbitrary ground field would
not give this assertion. Characteristic zero is the restriction used by the
full-adelic Harris application. No assertion over arbitrary schemes, or using
an arbitrary torsion predicate, is made here.

The proposition is not proved. In particular, construction of the rational Tate
map and its functoriality do not establish its injectivity. A proof must connect
the actual inverse limits and rationalized Hom groups used here with geometric
torsion or a faithful prime-adic realization; it may not replace this map by a
chosen faithful representation.

Two consequences are proved conditional on this precise proposition.
`rationalEndAction_injective_of_fieldFaithfulness` specializes it to `A = B`;
the existing endomorphism action is definitionally the same rational Hom map.
`rationalIso_injective_of_fieldFaithfulness` takes equality of the existing
induced linear equivalences, evaluates it at each vector, applies the asserted
Hom-map injectivity to the two forward rational morphisms, and uses categorical
isomorphism extensionality. Thus both conclusions concern the original
endomorphisms and isomorphisms.

## Original source and provenance

Edixhoven–van der Geer–Moonen, *Abelian Varieties*, preliminary draft,
registered as `edixhoven-vandergeer-moonen-abelian-varieties-draft`, Chapter XII
§1, Theorem (12.10)(i), printed pp.183–184 (one-based PDF pp.187–188), proves
injectivity, with torsion-free cokernel, of
`Hom(X,Y) ⊗ ℤ_ℓ → Hom_{ℤ_ℓ}(T_ℓ X,T_ℓ Y)` for a prime `ℓ` different from the
characteristic. Lemma (12.8), printed p.182 (PDF p.186), gives the torsion
factorization input. The full-rational formulation above is a derived target,
restricted to the algebraically closed characteristic-zero case. It is not the
verbatim statement of (12.10), and neither that theorem nor the comparison from
the full Tate module is proved by this file.

Harris–Taylor, *The Geometry and Cohomology of Some Simple Shimura Varieties*
(2001), Chapter I, printed p.18 (one-based PDF p.26), supplies the full integral and rational Tate
conventions; III.1, printed pp.90–91 (PDF pp.98–99), supplies the rational-isogeny
classes and full-adelic level structures motivating this target. Kottwitz,
*Points on some Shimura varieties over finite fields* (1992), §6, printed p.392
(PDF p.20), requires levels for which moduli objects have no nontrivial
automorphisms before asserting the level covers.

The latter two registered sources are
`harris-taylor-2001-geometry-cohomology-simple-shimura` and
`kottwitz-1992-points-shimura-finite-fields`. No matching project erratum file is
present under `notes/errata` at preparation.

This target and its conditional lemmas supply only faithfulness obligations and
consequences. They do not show that polarized rational stabilizers have finite
order, that sufficiently small levels kill them, that the residual class action
is free, that the original level projection is étale, or that the residual
kernel comparison is invertible. Applicable representability, source comparison,
canonical models and coefficient descent remain separate obligations.
