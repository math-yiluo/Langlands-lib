# Higher direct images of the Poincaré bundle vanish away from the origin

This module is a helper for the direct-image half of
`AlgClosedFieldPoincareDirectImageStatement` (Edixhoven, van der Geer and
Moonen, *Abelian Varieties*, registered source
`edixhoven-vandergeer-moonen-abelian-varieties-draft`, Theorem (9.1)). It
proves the support step of their
argument: the sheaves `R^n p_* P` vanish outside the origin of the dual.
All declarations live in the namespace `Langlands.AbelianScheme`.

## Statements

Throughout, `K` is an algebraically closed field, `A` an abelian scheme over
`Spec K`, and `hA : HasDualScheme A` a chosen dual `D := dualScheme A hA`
with origin `dualOrigin A hA`. Write `B := (baseChange D.hom).obj A` (so
`B.X.hom` is the projection `A ×_K D → D`) and
`P := (poincareLineBundle A hA).obj`. Every theorem assumes the instance
`LocallyOfFiniteType D.hom`.

- `poincareDirectImage_isZero_away_from_origin K A hA n`: for every `n : ℕ`
  the restriction of `(DerivedSections.higherDirectImage B.X.hom n).obj P`
  to the open `rationalPointComplement D.hom {dualOrigin A hA} _` (the
  complement of the underlying point of the origin) is zero.
- `poincareDirectImage_hasFiniteClosedSupport K A hA n`:
  `(DerivedSections.higherDirectImage B.X.hom n).obj P` has finite closed
  support in the sense of the published `HasFiniteClosedSupport`.
- `poincareDirectImage_stalkSupport_subset K A hA n`: the stalk support of
  `(DerivedSections.higherDirectImage B.X.hom n).obj P` is contained in the
  singleton of the point `(dualOrigin A hA).left (IsLocalRing.closedPoint K)`
  of `D`, the image of the closed point of `Spec K` under the origin.

The local-finite-type hypothesis on `D → Spec K` is an explicit instance
argument; it is not derived here. It is needed because the published
rational-fibre and support results are stated for schemes locally of finite
type over `K`.

## Implemented proof

`poincareDirectImage_isZero_away_from_origin`. Apply the published
`DerivedSections.isZero_pullback_higherDirectImage_of_rationalFibres` with
the published proof `universalPerfectSections`, `g := D.hom`,
`f := B.X.hom` (smooth and proper by base change, inferred), and the open
`U` above. It remains to show that for every `K`-rational point `x` of `U`
all cohomology of the Poincaré bundle restricted to the fibre over
`x ≫ U.ι` vanishes. The point `x ≫ U.ι` gives a base point `y` of `D`;
membership of its closed point in `U` and `mem_rationalPointComplement_iff`
show `y ≠ dualOrigin A hA`. The restricted bundle is translation invariant
by `poincareLineBundle_picardZero`, and it is nontrivial by
`dualPoint_eq_origin_of_fibre_iso` from the module
`Langlands.AlgebraicGeometry.Picard.DualPointOriginTriviality` (a
nontrivialization of the fibre bundle would force `y` to be the origin). The
published `algClosedFieldTranslationInvariantCohomologyVanishing` then gives
the vanishing in every degree.

`poincareDirectImage_hasFiniteClosedSupport` follows from the previous
theorem by the published
`hasFiniteClosedSupport_of_isZero_rationalPointComplement`.

`poincareDirectImage_stalkSupport_subset` follows from the previous-but-one
theorem by the published `stalkSupport_subset_compl_of_isZero_pullback`:
the stalk support lies in the complement of `U`, and unfolding
`rationalPointComplement` (the complement of the image of the closed point
under the origin) with `compl_compl` and `Set.image_singleton` gives the
singleton.

## Provenance and scope

This is the support step in the proof of Edixhoven, van der Geer and
Moonen, Theorem (9.1):
for a closed point `y ≠ 0` of the dual, `P_y` is a nontrivial
translation-invariant bundle, so all its cohomology vanishes, and by
cohomology and base change `R^n p_* P` vanishes near `y`. The Lean proof
replaces cohomology and base change by the published open-local
rational-fibre vanishing theorem, and the nontriviality of `P_y` is derived
from the universal property of the chosen Poincaré family (through
`DualPointOriginTriviality`). The theorems say nothing about the direct
images at the origin.
