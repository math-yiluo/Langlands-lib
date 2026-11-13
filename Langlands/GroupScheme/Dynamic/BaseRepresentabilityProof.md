# Finitely presented closed dynamic subgroups over arbitrary base schemes

Workers 3483 and 286. Proof of the published statement
`Langlands.GroupScheme.DynamicBaseRepresentabilityStatement`.

The theorem `dynamicBaseRepresentability` has exactly that statement as its
type. The base scheme is arbitrary; the ambient group is relatively affine
and locally of finite presentation. There is no smoothness, reducedness,
Noetherian or field assumption. The conclusion constructs closed group
subschemes representing the actual P, U and Z functors on all test schemes,
with structure morphisms locally of finite presentation.

The source correspondence is the one established in
[`BaseRepresentabilityStatement.md`](BaseRepresentabilityStatement.md):
Conrad, *Reductive group schemes* (2014), Theorem 4.1.7(1), printed/PDF
pages 112–114, for conjugation through a cocharacter and its arbitrary-base
extension. The registered original has SHA-256
`1a63a17e4ccb7e23263d65f05d93a6651262861e978e9eb0c1c53a01fd59140a`.
The proof uses the Library's constructions rather than importing a
literature assertion as an assumption.

On each affine open of the base, relative affineness makes the ambient
scheme affine. The published affine coordinate construction provides
closed representatives of P, U and Z on all tests. The helper
[`AffineFinitePresentation`](AffineFinitePresentation.md) proves that their
inclusions are locally of finite presentation: finite type of the ambient
coordinate algebra gives finite generation of the coefficient ideals, and
the corresponding quotient homomorphisms are finitely presented.

The helper [`OrbitLocality`](OrbitLocality.md) proves Zariski locality on
arbitrary test schemes by actual orbit-extension gluing, uniqueness and
evaluation at zero. This includes nonreduced tests. Published base-change
equalities identify the local affine subgroups with the restrictions of the
global functors.

The generic helper
[`SubgroupFunctor.ClosedGluing`](../SubgroupFunctor/ClosedGluing.md)
glues these closed representatives over the ambient open cover, descends
local finite presentation of their inclusions and transfers the actual
group structure from the subgroup functor. Composition with the ambient
structure morphism then gives local finite presentation over the base.
