# Closed torus lifts through split-unipotent quotients

For an arbitrary field `k : Type u`, this internal construction lifts a closed
torus homomorphism `j : H ⟶ Q` through an fppf quotient `q : G ⟶ Q` whose full
kernel has a smooth connected split-unipotent representative.

`IsTorus.exists_splitUnipotentQuotientLift` takes group schemes `G`, `U`, `Q`
and `H` over `Spec k`, affine `G`, smooth connected `U`, a homomorphism
`n : U ⟶ G` monomorphic as a map of relative schemes, and
`RelativeRoot.IsFppfQuotient (SubgroupFunctor.range n) q`. The last predicate
identifies `n` with the full scheme-theoretic kernel on all test schemes.
It also takes `IsUnipotent U`, `RelativeRoot.IsSplitUnipotent U`,
`IsTorus H`, `IsClosedSubgroup j`, and the exact propositions
`RelativeRoot.SplitUnipotentStableVectorSubgroupStatement.{u}` and
`RelativeRoot.TorusVectorActionLinearizationStatement.{u}`.
It returns `l : H ⟶ G` with `l ≫ q = j`. The lift is a group-scheme morphism
over the original field.

`IsTorus.splitUnipotentQuotientLift` chooses such a morphism.
`IsTorus.splitUnipotentQuotientLift_comp` records the same prescribed composite
with `q`. Smoothness or connectedness of the whole `G`, and affineness of `U`
or `Q`, are not separate hypotheses.

The proof first uses separatedness of field group schemes and affineness of `G`
to establish quasi-compactness of `q`. The represented-kernel smoothness theorem
then makes `q` smooth. Its actual kernel is smooth by pullback, affine by its
closed inclusion into `G`, and connected by comparison with `U`. The published
finite-type connected-group theorem makes this kernel geometrically connected.

The actual inverse image of `j` is affine by its closed inclusion into `G`,
smooth since both its projection and the torus are smooth, and connected by the
geometrically connected-kernel theorem. Its projection to `H` is smooth and
surjective. The published inverse-image kernel isomorphism identifies its
actual full kernel with that of `q`, which in turn is isomorphic to `U`.
Connectedness, unipotence and splitness transfer along these comparisons.
`TorusUnipotentExtension.exists_section_of_smooth_kernel` supplies a section of
the projection. Composing with the actual inverse-image inclusion proves the
required lift equation by pullback commutativity.

The provenance is internal: the proof combines the published actual subgroup
preimage, full-kernel comparisons and geometric connectedness results with the
split-unipotent extension section construction. No field characteristic,
perfection, cardinality or torus splitting restriction is imposed. The two exact
structural propositions remain explicit inputs. This supplies a torus-lifting
premise for quotient maximality; full rational maximal-torus conjugacy and the
two structural proofs remain separate obligations.
