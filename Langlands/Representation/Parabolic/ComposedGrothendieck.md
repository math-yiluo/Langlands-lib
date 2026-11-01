# Exact K0 transitivity for composed parabolics

Author: Worker 320.

`Langlands.Parabolic.normalizedComposedInductionK0` and
`Langlands.Parabolic.normalizedComposedJacquetK0` are integer-linear maps on
the existing exact finite-length smooth Grothendieck groups. They have the
generator formulas of the actual direct normalized functors for the composed
matrix parabolic. The module defines them as the existing maps in stages and
proves the direct formulas using the published actual natural transitivity
isomorphisms.

Fix an arbitrary prime `p` with `Fact p.Prime`, an actual
`F : PadicField.{uF} p`, supplied compatible `T : F.TopologicalData`, every
natural rank `n`, `B : GeneralLinear.BlockShape n`, and
`S : Geometric.BlockRefinement B`. Write `G = GeneralLinear n F.Carrier`,
`M = B.Levi F.Carrier`, and `L = Geometric.refinedLevi F.Carrier B S`.
The topology is the one supplied by `T`. There is no positive-rank restriction,
so all results include rank zero and the empty block shape and refinement.

The two maps have types

```text
normalizedComposedInductionK0 : K0(L) →ₗ[ℤ] K0(G)
normalizedComposedJacquetK0   : K0(G) →ₗ[ℤ] K0(L).
```

Here each `K0` is the published `SmoothRep.FiniteLengthGrothendieckGroup`
of actual smooth complex representations of finite group-algebra length,
modulo all actual short exact sequence relations, including nonsplit ones.
The `G` group is expressed using its existing specialized abbreviation.
The field universe `uF` and carrier parameter `uV` are independent; all
representations used by these two maps have carriers in `Type (max uF uV)`.
These groups impose neither admissibility nor finite complex dimension.

## The actual direct functors

The direct functors are the existing
`T.normalizedComposedInductionFunctor B S` and
`T.normalizedComposedJacquetFunctor B S` from `Parabolic.ComposedFunctors`.
The first uses smooth functions on `G` with covariance under the actual
`composedParabolic F.Carrier B S`, inflated through its actual projection
to `L`. Its normalizing character is the positive composed half-modulus,
and `G` acts by right translation. The second is the quotient by the actual
full ambient radical `composedUnipotent F.Carrier B S`, with the embedded
`L` action twisted by the inverse half of the composed modulus.

`normalizedComposedInduction_preservesFiniteLength` proves finite-length
preservation for direct induction at arbitrary input carrier universe `uV`,
with output carrier universe `max uF uV`.
`normalizedComposedJacquet_preservesFiniteLength` does the same for the
direct Jacquet functor, whose carrier universe remains `uV`. In the induction
proof, `normalizedRefinedFiniteLengthExactness` first supplies finite length
of the refined induction to `M`, and `normalizedParabolicFiniteLength`
supplies finite length after induction from `M` to `G`. In the Jacquet proof,
these two finite-length results are used in the reverse order for the two
Jacquet functors.

For each proof, choose the natural isomorphism from the published theorem
`normalizedRefinementInductionTransitivity` or
`normalizedRefinementJacquetTransitivity` and evaluate it at the input
object. `SmoothRep.equivOfIso` gives an actual equivariant linear
equivalence from the iterated output to the direct output. Its inverse is
injective from the direct output into the finite-length iterated output.
`FiniteLengthAssembly.finiteLength_of_injective` therefore proves finite
length of the direct output. No preservation or transitivity assumption
is added to either theorem.

## Construction and direct generator formulas

The definitions are exactly

```text
normalizedComposedInductionK0 =
  normalizedInductionK0 B ∘ normalizedRefinedInductionK0 B S

normalizedComposedJacquetK0 =
  normalizedRefinedJacquetK0 B S ∘ normalizedJacquetK0 B.
```

All four maps on the right are the existing maps, with their published
finite-length and exactness proofs. Their composition is consequently a
well-defined integer-linear map on the full exact quotient.
`normalizedInductionK0_comp_refinedInductionK0` and
`normalizedRefinedJacquetK0_comp_jacquetK0` state these equalities as
equalities of linear maps, hence on all virtual classes.

For every actual finite-length smooth `L` representation `A`,
`normalizedComposedInductionK0_finiteLengthClass` proves

```text
normalizedComposedInductionK0 [A] =
  [ (T.normalizedComposedInductionFunctor B S).obj A ].
```

For every actual finite-length smooth `G` representation `A`,
`normalizedComposedJacquetK0_finiteLengthClass` proves

```text
normalizedComposedJacquetK0 [A] =
  [ (T.normalizedComposedJacquetFunctor B S).obj A ].
```

Each formula accepts any proof of finite length of the displayed direct
output. Such a proof is always supplied by the preservation theorem above.
The implementation first applies the two existing generator formulas to
obtain the class of the iterated output, then applies
`FiniteLengthGrothendieckGroup.ofObject_eq_of_iso` to the component of the
actual published transitivity isomorphism. Thus these are formulas for the
literal direct functor outputs with the existing normalizations. Proof
irrelevance permits every choice of the finite-length witnesses.

`normalizedComposedInductionK0_eq_iff` and
`normalizedComposedJacquetK0_eq_iff` characterize each map uniquely:
an integer-linear map equals the named map if and only if, for every actual
finite-length input, some finite-length witness for the direct output gives
the displayed generator formula. The forward implications use the proved
preservation results and direct formulas. The reverse implications use
`FiniteLengthGrothendieckGroup.hom_ext_object`; the two maps agree on
every genuine finite-length object and therefore on the whole quotient.

## Provenance and scope

This is an internal derived construction from the published exact K0 maps,
their generator formulas, the two actual refinement transitivity proofs,
and finite-length transfer along injective intertwiners. It introduces no
new transcription from original literature. The original provenance of
the direct functors and transitivity theorems remains in their paired
Markdown. This module reuses their actual upper-block subgroups and
normalizing characters without alteration.

The complete project import closure was checked against the workspace's
published Library base: all 610 dependency modules and their Markdown
pairs agree with that base, and the closure contains no excluded downstream
classification declaration. The new module is the only additional pair.

The results supply the exact K0 transitivity bridge for composed
parabolics. They do not assert an identification with a flattened block
shape, a geometric-lemma class sum, an Aubert identity, or the analytic
segment classification.
