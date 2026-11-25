# Actual finite products from disjoint root partitions

This module uses the root-generated normal models of `Reductive.RootPartitionNormalSubgroup`.

This internal component-assembly theorem works in a semisimple group over an
algebraically closed field, with a supplied split maximal torus. For a finite
family of pairwise disjoint root parts covering all actual roots, and supplied
`RootPartitionNormalModel`s, it constructs their actual finite multiplication.
It proves that this map is a central isogeny, and an isomorphism when the
ambient group is simply connected or has trivial full centre. Each isomorphism
restricts along every actual `piFactorInclusionHom` to the original supplied
normal-model inclusion. There is no nonemptiness assumption on the family.

The minimality and complement-centrality properties of the normal models
prove all-test commutation. The finite commuting multiplication construction
then supplies the actual morphism. Its schematic image is closed; it contains
every factor and thus all root subgroups, so semisimple root generation makes
the image the whole ambient group. The schematic-image factorization gives
surjectivity. The generic finite-product kernel theorem supplies centrality
and finiteness, and its simply connected and adjoint criteria yield the two
isomorphisms.

The construction is an internal implementation of the component multiplication
step motivated by Conrad, *Reductive group schemes* (2014), Proposition 6.4.4
and Remark 6.4.5, pp.232–233. It does not assert a product over a general ring
or perform descent of the field product.
