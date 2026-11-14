# Proof of the real simple relative-root basis

Author: Worker 612.

Module `Langlands.GroupScheme.Rational.RelativeRealSimpleRootBasisProof`.

`Langlands.GroupScheme.relativeRealSimpleRootBasis` proves exactly the published
proposition `RelativeRealSimpleRootBasisStatement.{u}` at an arbitrary universe
`u`. For every field `k`, connected reductive group scheme `G`, maximal split
torus `i : T.toGrp ⟶ G` and generic cocharacter `ν`, it supplies an
`ℝ`-basis of the existing `RealTorusSpace.relativeRootSpanReal i`, indexed by
the existing `simpleRelativeRoots i ν`. The basis vector at `α` is exactly
`(1 : ℝ) ⊗ₜ[ℤ] α.1` in
`RealTorusSpace.Vstar T = ℝ ⊗[ℤ] characterLattice T`.

## Implemented proof

The proof applies the published construction `realSimpleRootBasis` from
`Langlands.GroupScheme.Rational.LanglandsSimpleRootBasis`. Its hypotheses are
discharged as follows.

1. Affineness and smoothness come from `IsConnectedReductive`; smoothness
   supplies the locally finite type instance used in the finiteness theorem.
   The monomorphism instance comes from the split-subtorus part of maximal
   splitness.
2. The published theorem `relativeRootReflectionExistence` from
   `Rational.RootReflectionExistenceProof` supplies integral reflection data
   `D : RelativeRootReflectionData i`. Its additional kernel-centralization
   conclusion is not needed here.
3. Splitness of `T` comes from `IsMaximalSplitTorus i`.
   `IsSplitTorus.finite_relativeRoots`, from `Rational.RootSupportFiniteness`,
   supplies finiteness of the actual relative-root set.
4. Apply `realSimpleRootBasis i ν D` with these hypotheses and the given
   genericity. The published lemma `realSimpleRootBasis_apply` identifies its
   vectors with `realSimpleRootVector i ν α`; the definition of this vector
   gives the required tensor equality.

The reused basis construction proves real linear independence by flat scalar
extension of rational independence and the published tensor cancellation
equivalence
`ℝ ⊗[ℚ] (ℚ ⊗[ℤ] characterLattice T) ≃ₗ[ℝ] ℝ ⊗[ℤ] characterLattice T`.
It proves spanning by extending the rational simple-root span equality to
the actual real root span, then uses `Module.Basis.mk`. No additional
root-system or reflection-data premise is retained by the theorem here.

Nonreduced relative root systems and the empty root system are included.
The proof needs no positive-rank hypothesis.

## Provenance and scope

This is an internal composition of published Library results. The mathematical
source assertion is the real simple-root basis clause of Renard V.3.12
(printed p.112 / PDF p.118), as documented by the unchanged target module
`Rational.RelativeRealCorootStatements`. This file adds no new source
assertion and no independent geometric argument.

The result proves the simple-root basis component only. It asserts no coroot
basis, fundamental weights or standard Levi decomposition.
