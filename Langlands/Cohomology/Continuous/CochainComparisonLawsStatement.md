# Discrete comparison and naturality: exact proposition

Author: Worker 22. Task `d00aea55-1beb-48a0-8f3c-d6c87b070309`, revision 1.

`Langlands.Continuous.CochainComparisonLaws` is a proposition definition,
not a proof. It specifies two assertions about the canonical maps defined
in `Langlands.Cohomology.Continuous.CochainComparison`.

First, let `k` be a commutative ring with a topology, let `G` be a discrete
topological group, and let `A : TopRep k G`. The named cochain map
`continuousToOrdinaryCochains A` is an isomorphism. Every degree component
is an isomorphism in `ModuleCat k`, and the named induced map
`continuousToOrdinary A q` is an isomorphism in every natural degree `q`.
The coefficient action and module are the same on both sides. The source
is the underlying module of Mathlib's actual `continuousCohomology q A`,
and the target is its actual
`groupCohomology (Rep.of A.ρ.toRepresentation) q`. No finiteness of `G` or
discreteness of the coefficient space is required. In particular, the
assertion applies to finite discrete quotient groups.

Second, let `G` and `H` be topological groups, let `A : TopRep k G` and
`B : TopRep k H`, let `φ : H →ₜ* G` be a continuous group homomorphism, and
let `f : TopRep.res φ A ⟶ B` be a compatible continuous coefficient map.
Discreteness of these groups is unnecessary for this assertion.
The canonical cochain comparison commutes with
`ContinuousCohomology.cochainsMap φ f` and
`groupCohomology.cochainsMap (φ : H →* G) (Rep.ofHom f.hom.toIntertwiningMap)`.
The first map has its topology forgotten. The ordinary coefficient map is
the same linear function with the same equivariance certificate.
In each natural degree the analogous square commutes for the actual
`ContinuousCohomology.map` and `groupCohomology.map`.

Both assertions quantify over arbitrary common universe `u` for `k`, the
groups and the coefficient carriers. They therefore support the lifted
integer ring `ULift.{u} ℤ` and coefficient carriers in arbitrary `Type u`.
There is no assumed cochain equivalence, homology equivalence, bijectivity
certificate, or other conclusion-bearing hypothesis.

The comparison is specifically the canonical evaluation map through the
standard and bar resolutions. The proposition does not merely ask for
an unspecified isomorphism between abstract modules. The naturality square
uses the existing Mathlib maps. The full profinite colimit comparison and
continuous transfer are subsequent obligations.

Original source: Serre, *Local Fields*, translated by Marvin Jay Greenberg,
Springer, 1979, Chapter VII, Section 3, printed pages 112–113 /
PDF pages 118–119 (homogeneous and inhomogeneous cochains); Chapter VII,
Section 5, printed pages 115–117 / PDF pages 121–123 (compatible
group and coefficient maps); Chapter X, Section 3, printed pages 154–155 /
PDF pages 160–161 (continuous cochains).
The exact assertion for Mathlib's nested cochain model is derived from
these descriptions; its proof must explicitly handle that nested model.

Literature ID: `serre-1979-local-fields`, content SHA-256
`109b461d42915da70771c70c4b551a363fc1f33412331ae2671c5c85be433112`.
Retained original: `/home/taskhub/central-library/Serre--Local Fields--1979.pdf`.

The imported Library module is
`Langlands.Cohomology.Continuous.CochainComparison`; its selected canonical
maps are `Langlands.Continuous.continuousToOrdinaryCochains` and
`Langlands.Continuous.continuousToOrdinary`.
The independently reviewed definition pair is present in the development
Library base `30ceb5a0d89d8094c1663fc19f35416519b9a125`.
Its Lean SHA-256 is
`366686fcafa0e27da39a197a19945b24d9bc5c97b81cc8a532339d058e963c0d`;
its Markdown SHA-256 is
`873df0d4540b0679653573ad972feac5aecc02430ac21ea2cd7ef536126bc618`.
This contribution adds only the exact proposition definition and its
explanation. Its proof requires a separate independently checked and
semantically reviewed contribution after statement publication.

Environment: `3b864ddf-f0af-4c18-8903-c6f813a0ce0f`, version 1,
Lean 4.34.0 (`293d5d0c0c3f3dded4688b3ccd6a33939ac5102b`) and
Mathlib `5ed2965256430c3649e86755f9576b54eca72435`.
