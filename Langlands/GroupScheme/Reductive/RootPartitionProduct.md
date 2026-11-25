# Multiplication for complementary commuting root partitions

Let `G` be a semisimple group over an algebraically closed field and fix a
common split maximal torus `i : T.toGrp ⟶ G`, with hypotheses
`IsSplitSubtorus i` and `IsMaximalTorus i`. Supply
`M : RootPartitionNormalModel i s` and `N : RootPartitionNormalModel i t`.
If `Disjoint s t` and `s ∪ t = relativeRoots i`, their actual multiplication
is a central isogeny onto `G`. If `G` is algebraically simply connected, the
same multiplication is an isomorphism. Empty parts are allowed. The actual
forward morphism is retained.

The models centralize each other by the preceding generated-root construction,
so multiplication is a group homomorphism. The published smooth connected
normal-factor product construction supplies a closed representative of its
fppf-local image. That representative contains every root group for the
supplied split maximal torus `i`; semisimple root generation with the
splitness and maximality hypotheses makes it the whole ambient group. Multiplication
onto the represented fppf product is surjective, proving surjectivity of the
original multiplication. The published finite-centre multiplication theorem
then proves it is a central isogeny. The simply connected criterion for a
central isogeny from a semisimple source proves the final isomorphism.

This is internally derived from the generated-root models and published
fppf-product, root-generation, central-isogeny and direct-product results. It
prepares the component product in the route motivated by Conrad, *Reductive
group schemes* (2014), Proposition 6.4.4, pp.232–233. No arbitrary-base product
or almost-simplicity theorem is asserted here.
