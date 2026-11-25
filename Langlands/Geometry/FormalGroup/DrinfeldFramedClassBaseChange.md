# Nilp-base extension on actual framed comparison classes

This module descends actual representative base extension through the
existing original framed comparison quotient. `ComparisonClass.baseChange`
uses the proved actual `Comparison.baseChange` to identify the classes of
extended representatives at every original comparison step. It therefore
descends through the original finite-chain relation without replacing that
relation. `DirectlyComparable.baseChange` retains an actual original framed
comparison; `ChainEquivalent.baseChange` collapses a finite original chain
and extends its actual comparison.

The class map on an actual representative is the class of its actual extended
representative. The descended residue map extends along the actual induced
quotient scalar map. Forgetting framing commutes with extension of the actual
height-certified target class. The existing quotient/base-change naturality
for target classes gives the reduced target-class equation. These equations
use quotient induction or the already proved target-class identity.

`baseChangeRepresentativeComparison` uses the exact actual-comparison
criterion for class equality to construct a framed comparison between the
extension of the chosen old representative and the chosen new representative.
The reverse constructor is the inverse of those same actual framed maps.

All local-field, finite-dimensional central-division, embedded-field,
coefficient/residue and height-certified frame assumptions remain explicit,
with Nilp universes `{v,u}`. Actual representative framings retain their local
kernel-rank height-zero certificates. Covers may be infinite and scalar maps
may merge generators. Identity and composition laws for this class map,
action laws and representability are outside this module, and it asserts no
functor. The identity and composition laws are `ComparisonClass.baseChange_id`
in `DrinfeldFramedIdentityComparison` and `ComparisonClass.baseChange_comp` in
`DrinfeldFramedCompositionComparison`; `DrinfeldFramedClassFunctor` uses them
to construct the functor `comparisonClassFunctor`. Action laws and
representability remain separate.
