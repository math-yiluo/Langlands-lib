# Closed classification of full integral Harris CM actions

This internal construction represents the existing full integral Harris
Rosati and normalized determinant conditions over a supplied abelian
family. It uses the published finite equality locus for maps into the
chosen dual, so the mixed relative-Hom representative required by
`HarrisIntegralCMActionLocus` is no longer an input. The supplied
relative-End representative and its geometry remain explicit.

All public declarations are in
`Langlands.Shimura.PEL.HarrisPolarizedWeilLevel`. The arithmetic carriers,
schemes and coefficient universes in this module have universe zero.

## Inputs and unchanged conditions

Retain the existing number-field and scalar structures, the central simple
unitary datum `D`, the auxiliary imaginary quadratic field `L`, and the
normalized Harris signature charts `C`. Supply the named prerequisite
package `P`, a locally noetherian scheme `S` with an actual morphism
`p : S ⟶ Spec F`, an actual abelian scheme `B/S`, its chosen `DualWitness W`,
and an actual morphism `lam : B ⟶ W.dual P`. A polarization condition on
`lam` is not a premise of this action-locus construction.

Write `O = D.harrisHodgePELIntegralOrder C`, with its original finite
integer basis. Supply `R : Over S`, separated and locally of finite type
over `S`, together with the displayed natural comparison identifying its
restricted actual Yoneda functor with the underlying relative
endomorphism functor of `B` on the full locally noetherian test category.
No mixed relative-Hom representative, or separatedness assumption for
such a representative, is supplied.

Let `U` be the original `relativeIntegralActionLocusTest` for `B,O,R`.
It has the original universal integral action `a_U` on
`B_U = (baseChange U.hom).obj B`. Let `W_U` be the canonical pullback
of `W`, and let `lam_U` be exactly `W.pullbackMap` of `lam`. The raw
classification equivalence is the existing
`relativeIntegralActionUniversalHomEquiv`.

The conditions and subfunctors being represented are the existing ones:

- `harrisIntegralCMActionCondition` requires the original finite-basis
  Rosati equations and the unchanged
  `HarrisTaylorCMRationalLieDeterminantCondition` for the rational extension
  of the actual integral action on the direct family `B_T`.
- `harrisIntegralCMFullActionCondition` requires those Rosati equations
  for every element of `O`, together with that same determinant condition.

The positive auxiliary left involution and the conjugated normalized
reflex coefficient map in these predicates are preserved. The file does
not replace them with conditions on a different representative or a
supplied rational action.

## Actual closed locus

The private `fixedCMClosedLocus` works first with an actual integral action
on a supplied family. It takes the scheme pullback of the published
`integralRosatiClosedLocus` inclusion and the published global normalized
determinant inclusion. Its structural map is the first pullback projection
followed by the Rosati inclusion. Both inclusions are closed immersions,
so base change and composition prove closedness of this map.

The Rosati locus is the actual finite equality locus of
`a(b_k) ≫ lam` and `lam ≫ dual(a(tau(b_k)))`. Its construction and
all-test criterion use the original chosen dual, without representing a
mixed Hom functor. The determinant locus uses exactly
`harrisHodgePELRationalAction`, the unique rational extension of `a`.
For every scheme test of this fixed family,
`fixedCMClosedLocus_factors_iff_basis` identifies factorization through
the pullback with the conjunction of the original pulled-back Rosati
basis equations and the normalized determinant. In one direction,
compose with both pullback projections. In the other, the two known
factorization criteria provide morphisms to the two loci; the common
structural map gives the morphism to their pullback. The rational-action
base-change theorem identifies the displayed rational extension on the
pulled-back family.

`harrisIntegralCMClosedActionLocus` applies this private construction to
`B_U,a_U,W_U,lam_U`, then composes its structural map with `U.hom` to
obtain an actual object `Z : Over S`.
`harrisIntegralCMClosedActionLocusInclusion` is the resulting morphism
`i : Z ⟶ U`. The instances with suffixes
`Inclusion_isClosedImmersion` and `Inclusion_mono` prove that it is a
closed inclusion and a monomorphism. The suffixes `locallyOfFiniteType`,
`isSeparated` and `isLocallyNoetherian` record the corresponding geometry
of `Z/S` and `Z.left`. They follow from the closed inclusion and the
original raw-action locus's geometry; they are outputs for `Z`.

## Classification and naturality

For every locally noetherian `T : Over S` and raw classifying map
`f : T ⟶ U`, `harrisIntegralCMClosedActionLocus_factors_iff` proves

```text
(∃ k : T ⟶ Z, k ≫ i = f) ↔
  harrisIntegralCMActionCondition T (classify(f)).
```

Apply the private fixed-family criterion to `Over.mk f.left` over `U`.
The existing relative Rosati restriction comparison and determinant
restriction comparison identify its successive pullback conditions with
the original conditions on the direct family `B_T`. The existing
universal-action value formula identifies the resulting action with
`classify(f)`. A private elementary over-category factorization lemma
converts between the underlying scheme factorization and the displayed
factorization by actual morphisms in `Over S`.

`harrisIntegralCMClosedActionLocusHomEquiv` therefore gives the equivalence
between actual `Hom_Over(S)(T,Z)` and actual integral actions on `B_T`
satisfying this basis conjunction. Its forward function classifies
`k ≫ i`. Injectivity uses the monomorphism of `i` and injectivity of raw
action classification. Surjectivity first classifies the supplied action
on `U`, then factors that morphism using the proved criterion.
The suffix `_apply` gives its literal value:

```text
(k classified action) = (relativeEndRestrict B (k ≫ i)).comp a_U.
```

`harrisIntegralCMClosedActionLocusIso` assembles this equivalence into a
natural isomorphism from restricted `uliftYoneda.{0}.obj Z` to the
restricted original basis-action subfunctor. The existing functor uses
`ULift` of actual actions; the component equivalences retain this lift.
Naturality rewrites both sides by the literal value formula and applies
the composition law of actual relative-Hom restriction. The test category
includes every locally noetherian scheme over `S` and every actual
morphism between them, with no connectedness or reducedness restriction.

## Full order and rational consequences

The original dual-additivity proof identifies full-order and basis Rosati
conditions on quasi-separated schemes. Locally noetherian tests satisfy
this hypothesis. Consequently
`harrisIntegralCMClosedActionLocus_factors_iff_full` gives the same
factorization criterion with the original full-order conjunction.
`harrisIntegralCMClosedActionLocusFullHomEquiv` composes the basis Hom
equivalence with the identity-on-actions equivalence of those predicates.
Its suffix `_apply` preserves the same literal universal restriction.

`harrisIntegralCMClosedActionLocusFullIso` composes the preceding natural
classification with the existing `harrisIntegralCMActionBasisFullIso`.
Thus this actual closed locus naturally represents exactly the existing
`harrisIntegralCMFullActionSubfunctor` on the full locally noetherian test
category. Passing from basis to full equations changes only the proofs
of the conditions, not the classified integral actions.

Finally,
`harrisIntegralCMClosedActionLocusFullHomEquiv_involutionCompatible`
applies the existing full-condition rationalization theorem to every
classified action. It concludes actual rational involution compatibility
with the positive auxiliary involution and the rationalized canonical
pullback of `lam`, together with the unchanged normalized determinant.
These conclusions are derived from the action classified by a test
morphism, rather than supplied as new premises.

## Provenance and scope

This is an internal deduction from the published finite dual-map equality
locus, global determinant locus, universal integral-action classification,
relative Rosati and determinant comparisons, and full-order rationalization
and dual-additivity results. It introduces no external literature claim.
The previous mixed-Hom construction and all imported Lean/Markdown pairs
are preserved. This is a construction with fewer geometric inputs, not
an alteration of its original conditions.

The family, its chosen dual datum, and the relative-End representative
with the stated geometry are still supplied. The module does not construct
an ordinary polarized ambient moduli scheme, impose adelic level data,
compare the complete normalized rational-isogeny quotient, establish
output admissibility, or prove smoothness and division-case projectivity.
Those remain obligations of the exact
`DivisionCMRepresentabilityStatement`, which is unchanged and remains
open. No suspended generic representability branch is resumed here.
