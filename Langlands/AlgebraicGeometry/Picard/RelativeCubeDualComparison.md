# Actual dual inverses and the monoidal relative cube comparison

This internal adapter composes the published ordinary cube transport with the
published comparison using actual line-bundle dual inverses. The ordinary
geometric cube criterion and canonical pullback-tensor invertibility remain
explicit hypotheses. No unconditional theorem of the cube or Mumford
parameter-additivity theorem is proved here.

`rigidifiedClasses_eq_of_cubeTrivialityWithDual` applies to any three pointed
schemes over a base. Its ordinary cube hypothesis says that a line bundle on
`X × (Y × Z)` is trivial when its restrictions to the three section faces are
trivial. The first face corresponds to the rigidification along the section of
`X`. The other two faces correspond to the axes `(e_Y,id_Z)` and `(id_Y,e_Z)` in
the parameter product. The conclusion is equality in the published quotient of
actual relative rigidified line bundles, given equality after these two actual
axis pullbacks.

The proof passes the ordinary cube hypothesis to
`CubeRelativeTransport.relativeTrivializationOfCubeTriviality`, which transports
it to the actual relative space. It then applies
`RigidifiedLineBundle.classes_eq_of_threePullbackTrivialityWithDual`. That
published comparison uses an actual dual inverse and closure of actual line
bundles under tensor. Consequently the general local-rank-one versus
tensor-invertibility comparison is not a premise of this adapter.

`CubeRelativeTransport.parameterProductIso` compares the chosen cartesian
monoidal product in `Over S` with the categorical product. Its forward map pairs
the two monoidal projections; its inverse pairs the two categorical projections.
The two inverse equations follow from the respective product universal
properties. The lemmas `secondAxis_parameterProductIso_inv` and
`thirdAxis_parameterProductIso_inv` identify the transported pointed axes with
the corresponding monoidal pairings.

`Langlands.AbelianScheme.rigidifiedClasses_eq_of_ordinaryCubeTriviality` specializes
the detection principle to actual abelian schemes `A`, `B`, and `C` over `S`. Its
classes live on the parameter object `B.X ⊗ C.X` used by the existing relative
family. Its first axis is the monoidal pairing `(id_B,1)` and its second is
`(1,id_C)`, where `1` is the actual unit-valued morphism of schemes. Pulling the
classes along the inverse parameter-product isomorphism reduces the conclusion
to the categorical detection lemma. The two axis equations identify its
hypotheses, using functoriality of rigidified pullback and the unit-valued
composition law. Pullback along the forward isomorphism recovers the original
classes, using composition and identity comparisons.

The base is arbitrary; quasi-separatedness is not needed by this categorical
adapter. There is no restriction to reduced schemes, geometric points, fields,
Picard-zero classes, or schemes with a chosen dual. This scope does not supply
the missing ordinary geometric cube criterion for these schemes.

The provenance is internal: all results are compositions of the published
`RelativeCubeClassComparison`, `CubeLineBundleComparison`,
`RigidifiedPullbackProofs`, and `RelativePicardZero` interfaces and cartesian
product universal properties. No claim is attributed directly to literature.
