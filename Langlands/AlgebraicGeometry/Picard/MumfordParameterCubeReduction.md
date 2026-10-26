# Reduction of actual Mumford parameter additivity to ordinary cube triviality

This module isolates the geometric input sufficient for the exact published
`Langlands.AbelianScheme.MumfordBundleParameterAdditivityStatement` and proves
the conditional reduction to that input. The geometric input remains unproved,
so this module does not establish the unconditional parameter-additivity theorem.

`MumfordSelfCubeTriviality A` is a `Prop`-valued definition for an actual abelian
scheme `A/S`. For every ordinary line bundle on the categorical product
`A.X × (A.X × A.X)` in `Over S`, it asserts triviality when the three restrictions
obtained by setting one coordinate equal to the actual unit section are
trivial. Each restriction is the ordinary module pullback along the underlying
scheme morphism of the corresponding `CubeFace`. Both the restrictions and the
conclusion require actual isomorphisms with the appropriate structure sheaf.
The definition has no quasi-separatedness hypothesis; it only describes the
criterion for a fixed abelian scheme and supplies no proof of that criterion.

`mumfordBundleParameterAdditivity_of_ordinaryCubeTriviality` assumes this
criterion for every abelian scheme over every quasi-separated base, in the
same universe as the conclusion. Its conclusion is precisely the existing
`MumfordBundleParameterAdditivityStatement`. Thus canonical pullback-tensor
preservation, the base, the abelian scheme, the unit-rigidified line bundle,
the supplied ordinary inverse and its evaluation are quantified exactly as in
the published target. The ordinary cube criterion is an additional explicit
hypothesis of this conditional theorem.

The implemented proof introduces the target's inputs and applies
`rigidifiedClasses_eq_of_ordinaryCubeTriviality` with all three abelian schemes
equal to `A`. The two classes are the multiplication pullback of the actual
normalized Mumford family and the rigidified tensor of its two projection
pullbacks. The published `mumfordBundleParameterAdditivity_firstAxis` and
`mumfordBundleParameterAdditivity_secondAxis` provide the two required
equalities along `(id,e)` and `(e,id)`. The imported detection lemma handles
the comparison between categorical and cartesian monoidal products, uses an
actual line-bundle dual to form a difference bundle, and obtains an isomorphism
respecting the specified rigidifications. No new product comparison or
rigidification adjustment is implemented here.

The result concerns equality of the full actual rigidified family classes over
`A.X ⊗ A.X`. It applies without restricting the base or parameter schemes to
reduced schemes or fields, and hence retains infinitesimal parameters whenever
the stated cube criterion is supplied. Picard-zero membership, a chosen dual
scheme, representability and a general local-rank-one versus tensor-invertibility
comparison are not inputs to this reduction.

The provenance is internal. The proposition packages the ordinary geometric
premise of the published `RelativeCubeDualComparison` interface in the
self-product case. Its conditional consequence composes that interface with
the published `MumfordParameterAxes` lemmas and the unchanged published target.
No unconditional geometric theorem or direct assertion from literature is
claimed by this module.
