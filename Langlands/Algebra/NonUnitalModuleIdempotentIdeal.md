# The actual ideal module Ae and evaluation at e

This construction supplies the ideal module and its additive Hom
correspondence used in the proof of the enough-projectives theorem in
Renard, *Représentations des groupes réductifs p-adiques*, French version
dated 9 July 2026, I.5.2, printed pp.26–27 / PDF32–33. The registered
source is `renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
The registered 2010 corrections were checked for the adjacent I.5.1
reflexivity argument; no change to this ideal construction is used.

The source's algebra is complex and idempotented. The ideal action and
evaluation correspondence use only the nonunital ring and original additive
module laws, so these constructions are supplied at that greater generality.
Only the proof that the ideal is nondegenerate requires the idempotented
hypothesis. No unital ring, chosen unit, ambient complex structure on the
test module, or finite dimension is assumed.

`Carrier e` is the actual published subgroup `Idempotent.rightImage e`,
whose elements satisfy `a * e = a`, transported through `ULift`. The
published image characterization identifies this subgroup with the image
of right multiplication by e, hence with Ae. The ring, optional lift and
test-module universes are independent. The lift places the ideal in
carrier universe `max uA uL`; it does not change any ring element or action
formula.

`action e` is left multiplication on that same subgroup:
`(a • x).down.val = a * x.down.val`. Associativity proves that it stays in
the subgroup and gives the original nonunital module laws. The vector
`generator e` is e itself, with its intrinsic idempotence witness.
`smul_generator` says that every ideal vector x equals `x.down.val • e`.
A two-sided local unit for the original element underlying x fixes x by
left multiplication. This proves `isNondegenerate` and constructs
`object hA e` in the actual `NondegenerateModuleCat A`. The carrier and
entire action are exposed by definitional equalities.

For any original additive A-module M, `toFixed e` evaluates an original
intertwiner at e. A-linearity and `e * e = e` show that the value belongs
to exactly `NonUnitalModuleCorner.FixedPart e M`. For a fixed vector m,
`fromFixed e m` sends a vector x of Ae to `x.down.val • m.val`, using M's
specified original action. The fixed-vector equation shows evaluation
recovers m. The equation `x = x.down.val • e` and A-linearity show that
the reconstructed map recovers the whole original intertwiner.
`homEquiv e` packages these proved intrinsic inverse laws as an additive
equivalence. Its naturality theorem is equality of entire additive maps
under original postcomposition and the published fixed-part restriction.

This is implementation infrastructure for the source's identification
Hom_A(Ae, M) = eM. The additive equivalence is sufficient to express the
exact-Hom projectivity argument after forgetting complex coefficients;
this pair does not assert a complex-linear equivalence. It does not yet
prove projectivity of Ae, preservation of projectivity by direct sums,
enough projectives, the dual injectivity lemma, enough injectives, or any
I.5.3 free-module assertion. Those remain separate statement and proof
obligations.
