# Rational-point component quotients without smoothness

`IdentityComponent.rationalIdentityKernel G` is the subgroup of rational
sections whose actual scheme point lies in the identity component. It is defined
for every group scheme over a field, without smoothness or finiteness. It is
normal: actual inner automorphisms preserve connected components and fix the
identity. `ComponentPointQuotient G` is the ordinary group quotient of rational
points by this subgroup. It is not an asserted scheme quotient.

`componentPointEmbedding` embeds that quotient into the actual topological type
of connected components. Its criterion is that two rational points are in the
same component exactly when their quotient belongs to the rational identity
kernel. The proof translates both components by the inverse of the first point.
For any actual open immersion onto `IdentityComponent.identitySet G`,
`mem_rationalIdentityKernel_iff_lift` identifies this kernel with the rational
points factoring through that immersion.

An affine group scheme locally of finite type has finitely many connected
components: its space is compact, local Noetherianity makes each component
open, and its connected-component quotient is discrete. Thus the rational-point
quotient is finite. Over an algebraically closed field every component contains
a rational section, so `componentPointQuotientEquiv` is an equivalence onto all
actual components, requiring only local finite type.

For any group locally of finite type over a field, the theorem
`natCard_geometricComponents_eq_componentPointQuotient` identifies the
`Nat.card` in Nagata's statement with the cardinal of this ordinary quotient
after extension to the chosen algebraic closure. The final finiteness theorem
covers the full affine finite-type scope of Nagata, including nonreduced groups.
No group structure is installed on the existing `GeometricComponents` type.

## Provenance

This is internal derived component infrastructure. Milne, *Algebraic Groups*
(2022 corrected reprint), Proposition 2.37(b),(d), printed p. 51 (PDF p. 62),
identifies the identity-component kernel and the order of the finite component
quotient with the number of geometric components. The retained source is
`milne-2022-algebraic-groups`, SHA-256
`f2ddd8fa4d263085f173934664b246007a2c0bd539739b7c82de39bfb5d21f40`.
The official errata snapshot
`milne-2022-algebraic-groups-errata-2026-11-04` corrects the preceding
construction over a separable closure: rational points need not cover all
components there. This implementation uses an algebraic closure and the
published rational-representative theorem only under that hypothesis, and so
retains none of the erroneous separable-closure surjectivity claim.

The elementary translation and quotient proof adapts the public smooth-only
`IdentityComponentRationalQuotient` construction, with a directly defined normal
rational kernel. Finiteness adapts the public compact/discrete component proof
without its unnecessary smoothness assumption. These modules and all target
imports remain unchanged. Actual finite étale quotient representability and
representation semisimplicity are not asserted.
