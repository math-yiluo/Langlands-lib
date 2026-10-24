# The actual base-changed Poincare family

For a morphism of arbitrary schemes `b : S' → S`, an abelian scheme `A/S`,
and a parameter scheme `P/S`, this module constructs the pullback of an
actual rigidified family on `P ×_S A` to
`P_{S'} ×_{S'} A_{S'}`. All schemes use the same universe.

`baseChangeParameterMap` is the projection `P_{S'} → P`, viewed as a
morphism over `S`. The construction uses the existing slice-category
pullback, so `P_{S'}` is the actual scheme fibre product.

`baseChangeFamilySpaceMap` first applies `familyBaseChangeSpaceMap` and
then the relative-space map induced by this parameter projection. Its two
projection identities state that it projects to `P` and `A` through the
respective base-change projections. The section identity states that the
induced unit section maps to the original induced section after
`P_{S'} → P`. The projection identities follow from the pullback lifts;
the section identity follows from ground-base section compatibility and
naturality of the original relative section.

`baseChangeFamily` is a functor on actual rigidified line bundles and their
morphisms. It first pulls back in the parameter scheme, then applies
`familyBaseChange` to change the ground base. Both operations retain the
rigidification through the canonical structure-sheaf comparisons.
`baseChangeFamilyForgetIso` identifies its underlying ordinary line bundle
with pullback along `baseChangeFamilySpaceMap`, using the existing
composition isomorphism for line-bundle pullback.

Given `hA : HasDualScheme A`, `poincareFamilyBaseChange` applies this functor
to the chosen actual Poincare family. Its parameter scheme is exactly
`(Over.pullback b).obj (dualScheme A hA)`. The final isomorphism identifies
its ordinary line bundle with pullback of the original parameter-first
Poincare bundle along the displayed total-space map.

This construction makes no representability or geometric Picard-zero
claim about the new family. In particular, it does not yet identify this
parameter scheme with a chosen dual of `A_{S'}`. Universality after base
change is a separate theorem obligation.

## Provenance

This is internal, derived infrastructure. The maps are forced by the
universal property of scheme pullbacks; the family is obtained by the
existing rigidified pullback functors. The Poincare specialization uses
the family already selected from the genuine universal-family existence
predicate `HasDualScheme`. No new desired morphism, family or universal
property is supplied as arbitrary data.
