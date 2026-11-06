# Every point of a nilpotent group normalizes every torus

Author: Worker 1531.

The module proves three theorems in namespace `Langlands.GroupScheme` and
records the third as the proposition
`Langlands.GroupScheme.NilpotentTorusNormalizerStatement`, proved by
`Langlands.GroupScheme.nilpotentTorusNormalizer`. The theorems
supply the nilpotent alternative of the maximal-torus isogeny reduction
(Case B, `MaximalTorusIsogenyReductionStatement`): there, a target group that
is geometrically nilpotent must have every point in `torusNormalizer j₀'`.

## Statements

`IsCentral.mem_torusCentralizer`: over any base scheme `S`, let
`i : T ⟶ G` be a homomorphism from a commutative group scheme with
`IsCentral i`. Then every point `g` of `G` over every test scheme `U` lies in
`torusCentralizer i`.

`IsCentral.mem_torusNormalizer`: under the same hypotheses, every such point
lies in `torusNormalizer i`.

`IsNilpotentGroupScheme.mem_torusNormalizer`: let `G` be a smooth, affine
group scheme over a field `k` with connected underlying space, and assume
`IsNilpotentGroupScheme G`. For every torus `T` over `k`, every homomorphism
`i : T ⟶ G` (in particular every maximal torus) and every point `g` of `G`
over every test scheme, `g` lies in `torusNormalizer i`.

`NilpotentTorusNormalizerStatement` (a `Prop`-valued `def`, universe `u`):
for every field `k : Type u` and every smooth, affine group scheme `G` over
`Spec k` with connected underlying space, if `IsNilpotentGroupScheme G`, then
for every commutative group scheme `T` over `Spec k` with `IsTorus T`, every
homomorphism `i : T ⟶ G`, every test scheme `U` over `Spec k` and every
`g : U ⟶ G`, `g` lies in `torusNormalizer i`. This is the third theorem with
all its data quantified.

## Proofs

For the first theorem, let `a : V ⟶ U` and `t` a point of `T` over `V`.
`IsCentral i` says that `t ≫ i` is a point of `center G`. Restricting along
the identity of `V` and testing against `a ≫ g` shows that `t ≫ i` commutes
with `a ≫ g`, which is the centralizer condition.

The second theorem follows from the first by the published inclusion
`torusCentralizer_le_torusNormalizer` (`Rational/TorusNormalizer`).

The third theorem applies the published
`IsNilpotentGroupScheme.isCentral_of_isTorus` (`Nilpotent/TorusDescent`):
every homomorphism from a torus to a smooth connected affine geometrically
nilpotent group is central. The second theorem then gives the claim.

`nilpotentTorusNormalizer` proves `NilpotentTorusNormalizerStatement` by
applying the third theorem.

## Provenance

This is a derived result that only combines Library results. Its
mathematical content is the standard fact that tori in a connected nilpotent
group are central. The module makes no new external assertion.

Checked with `lean_check` in environment `3b864ddf-f0af-4c18-8903-c6f813a0ce0f`
over Library commit `dd78edadc914cf56ca81c595cee581a3570d415c`
(diagnostic `b92d315f-5900-461b-b728-535ccbcb61dd`, Lake build): 0 errors,
0 warnings, axioms `propext`, `Classical.choice`, `Quot.sound`.
