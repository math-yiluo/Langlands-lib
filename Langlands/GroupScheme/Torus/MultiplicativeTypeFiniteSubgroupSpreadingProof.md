# Spreading of finite and trivial fibres of closed subgroups

`Langlands.GroupScheme.multiplicativeTypeFiniteSubgroupSpreading.{u}` proves
`Langlands.GroupScheme.MultiplicativeTypeFiniteSubgroupSpreadingStatement.{u}`
for every universe `u`. For a finitely presented closed subgroup `K` of a
group of multiplicative type, a finite residue fibre gives an open
neighbourhood on which `K` is finite and one positive exponent kills every
scheme-valued point. A unit residue fibre gives an open neighbourhood
on which the subgroup's structure morphism is an isomorphism.

The Lean proof applies `finiteSubgroupSpreading_of_uniformExponent` to
`quasiFiniteCommutativeUniformExponent`, the published proof of
SGA 3, Exposé IX, Lemma 6.1. The reduction uses that the subgroup's
structure morphism is affine and locally of finite type to obtain local
quasi-finiteness near the finite fibre. It shrinks to an affine open neighbourhood `U`, where the
uniform-exponent theorem applies to the commutative base-changed group.
Finiteness follows by splitting the ambient group fppf-locally. In the
split case group-like elements span the coordinate algebra of the
subgroup and are integral by the exponent identity. The algebra is
therefore integral and of finite type, hence finite as a module.
Finiteness descends along the splitting cover.
[Spreading reduction](FiniteSubgroupSpreadingReduction.md),
[Uniform-exponent proof](../QuasiFiniteCommutativeUniformExponentProof.md),
[Bounded-exponent finiteness](BoundedExponentSubgroup.md).

For a unit fibre, the reduction first obtains a finite neighbourhood.
The finite-group Nakayama argument uses the augmentation to split off
the scalars and shrinks further so that the complementary finite
module vanishes.
[Finite-group Nakayama argument](../FiniteUnitFibreSpreading.md).

The target is Theorem 6.4 and Corollary 6.5 of A. Grothendieck,
*SGA 3*, Exposé IX, Gille–Polo recomposed edition of 8 November 2009,
p. 54 (original margin 66), registered as `sga3-expose-ix-gille-polo-2009`
with SHA-256 `7c1e3d5b9d01ad01d0dd7b8b62045d012052e7890fb37adc3e7934ebb5fd6fc3`.
[Statement and source comparison](MultiplicativeTypeFiniteSubgroupSpreadingStatement.md).
