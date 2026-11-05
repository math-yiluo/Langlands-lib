# Actual affine-line sources after field extension

This internal adapter compares the actual affine line after a change of base
with pullback of the original affine line, retaining its zero section.
It also transports nested universal sources through an isomorphism of their
initial source without changing any group parameter. The constructions are
deductions from the existing affine-line, scheme-pullback and nested-source
constructions, rather than additional structural assumptions about unipotent
groups.

`AffineLine.zeroSection_baseChange` works over arbitrary base schemes. Its
proof uses the two projections of the actual pullback. The affine-line
projection is determined by its structure morphism and its coordinate
function, which is zero on either section. The base projection agrees because
both arrows lie over the new base.

`sourceCongr` recursively tensors an isomorphism of initial sources with the
identity on the group. Functoriality of tensor products proves
`basepointSection_sourceCongr`, compatibility with the entire basepoint
section. Composing this comparison for `AffineLine.baseChangeIso` with the
inverse of `sourceBaseChangeIso` gives `affineLineSourceBaseChangeIso`.
The source is built from the actual affine line over the new base; the target
is pullback of the original nested source. The theorem
`basepointSection_affineLineBaseChange` identifies its entire zero section,
including every group parameter and the terminal parameter factor at index
zero, with pullback of the original section through the parameter comparison.

For fields `k` and `K` in the same arbitrary universe, an algebra structure
`Algebra k K`, and a separably closed `K`,
`family_eq_one_of_sepClosed_extension_of_rationalPointStatement` gives the
following conditional deduction. Suppose `G` is smooth over `k`, `W` is
separated over `k`, and the actual base change of `W` to `K` has constant
affine-line maps. A morphism from any nested affine-line source for `G` to
`W` whose entire basepoint restriction is the unit is itself the unit,
provided the exact proposition
`Langlands.CommutativeAlgebra.SeparablyClosedRationalPointStatement.{u,u}`
is supplied. No separability hypothesis on `K/k` is needed.

The proof transports the morphism and its entire basepoint restriction to
the actual affine-line source over `K`. Smoothness and separatedness survive
pullback. The previously proved conditional smooth-source theorem over a
separably closed field makes the transported family the unit. A field
extension is faithfully flat and quasi-compact, so pullback is faithful;
cancelling the source comparison and using faithfulness proves the original
morphism is the unit.

This file proves neither the algebraic rational-point proposition nor any
structural decomposition of a commutative unipotent group. Its last theorem
retains the rational-point proposition and affine-line rigidity of the
extended target as explicit hypotheses. It does not prove the unrestricted
unipotent woundness criterion.
