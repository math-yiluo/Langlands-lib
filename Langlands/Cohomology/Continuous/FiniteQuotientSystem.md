# Finite quotient cohomology system

This construction belongs to Worker 22's continuous cohomology task
`c6ea3f74-2826-48db-9ab1-46587ae2dd92`, revision 1.

`Langlands.Continuous.DiscreteModule k G` contains an actual Mathlib
`TopRep k G`, a discrete topology on its carrier, and continuity of the
joint action map from `G` times the carrier. The last condition is additional
data: continuity of the individual operators in `TopRep` does not supply it.
The underlying ordinary representation is obtained by forgetting continuity.
`DiscreteModule.ofAdditiveAction` accepts a discrete additive commutative
group in arbitrary `Type u` with a distributive, jointly continuous G-action,
and constructs its representation over `ULift.{u} Z`. Scalar multiplication
is the usual integer multiplication after applying `ULift.down`.
The scalar compatibility certificate is the fact that additive homomorphisms
commute with integer multiplication. No coefficient action or field is
introduced by this constructor.

The finite quotient index consists of the actual open normal subgroups,
ordered by reverse inclusion. For such a subgroup N, `finiteQuotientRep`
is Mathlib's representation of `G/N` on the submodule of N-fixed elements.
If M is contained in N, `quotientTransition` is the induced homomorphism
`G/M` to `G/N`, and `fixedTransition` is the inclusion from N-fixed elements
to M-fixed elements, with equivariance proved on representatives.
`finiteInflation` uses Mathlib's actual `groupCohomology.map` for these two
maps. `finiteQuotientCochainDiagram` packages the actual inhomogeneous
cochain complexes and their inflation maps as a functor; its identity and
composition certificates are proved from the corresponding cochain
map laws and equality on quotient representatives. Applying Mathlib's
homology functor gives `finiteQuotientDiagram`.
`finiteQuotientCohomology` is the categorical colimit of that diagram.
`finiteStageToColimit` is its canonical structural map from each stage.
The index is nonempty because it contains the whole group, and filtered
because intersection is a common refinement. In a compact group,
`finite_quotient` certifies that every quotient in this diagram is finite.

`finiteQuotientTopRep` gives the actual fixed-submodule quotient representation
the topology inherited from A. It is discrete. `finiteQuotientModule`
certifies that the quotient action is jointly continuous, using openness
of N to make G/N discrete. `quotientProjection` is the continuous quotient
homomorphism, and `fixedCoefficientInclusion` is the continuous equivariant
inclusion of fixed elements into A. `continuousFiniteInflation` applies
Mathlib's existing `ContinuousCohomology.map` to this pair.
Its source is the finite quotient's actual continuous cohomology.
Converting ordinary finite-group cohomology to this source requires the
separate cochain comparison; that conversion is not asserted here.

`DiscreteModule.restrict` restricts the joint action along a subgroup's
continuous inclusion, preserving the discrete coefficient topology.
`continuousRestriction` is defined by Mathlib's `ContinuousCohomology.map`
for that inclusion with identity coefficient map. Thus the eventual transfer
laws will use the existing restriction map.

The algebraic diagram is defined for any representation and any topological
group carrier; compactness is needed to conclude that its quotients are
finite, and profiniteness and the continuous discrete action are needed
for the intended comparison. No comparison is assumed or supplied by
the definition of this colimit. The comparison with Mathlib's nested
continuous homogeneous-cochain homology and the transfer laws remain
separate proof obligations.

All ring, group and coefficient carriers inhabit arbitrary `Type u`.
This follows the common-universe requirement of pinned `groupCohomology`;
in particular the scalar type can be `ULift.{u} Z`, rather than restricting
the coefficient carrier to `Type 0`.

The mathematical source is Jean-Pierre Serre, *Local Fields*, English
translation by Marvin Jay Greenberg, GTM 67, Springer, 1979, Chapter X,
Section 3, printed page 154 / PDF page 160; and Chapter VII, Section 5,
printed pages 115-116 / PDF pages 121-122. Serre defines the cohomology
of a profinite group on a discrete continuous module as this inflation
direct limit and states its continuous-cochain computation. His change-of-group
construction uses a group homomorphism and a compatible coefficient homomorphism;
the quotient projection and fixed-coefficient inclusion define inflation.
Worker 22 read these original passages. Source ID: `serre-1979-local-fields`; SHA-256:
`109b461d42915da70771c70c4b551a363fc1f33412331ae2671c5c85be433112`.
Retained original: `C:/Central-Library/Serre--Local Fields--1979.pdf`.

There are no project mathematical imports. The prepared environment is
`2ecc41bc-2901-4e34-96c5-6d98fbb3c74d`, version 1, Lean 4.34.0 at commit
`293d5d0c0c3f3dded4688b3ccd6a33939ac5102b`, with Mathlib commit
`5ed2965256430c3649e86755f9576b54eca72435`.
This definition contribution supplies the system and the basic continuous maps.
The remaining comparisons and transfer laws require their own exact statements,
checked proofs, independent semantic review and publication.
