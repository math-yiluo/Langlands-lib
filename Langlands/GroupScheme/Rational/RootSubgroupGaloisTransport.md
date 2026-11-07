# Actual root subgroup transport under coefficient automorphisms

This internal construction identifies the existing intrinsic root subgroup functors
under canonical coefficient transport, and restricts the existing coefficient
conjugation to multiplicative equivalences of their rational points. The base
schemes in the first part are arbitrary. In the field specialization, both fields
range over an arbitrary common universe, with only field and algebra structures.
The commutative group scheme, ambient group scheme and homomorphism are supplied.
There is no splitness, smoothness, affineness, finiteness or Galois-extension
assumption. The subgroup identity holds for every character, without a premise
that it occurs as a root.

`commDescentBaseChangeIso` retains the underlying canonical descent isomorphism
for the actual group, together with its commutative structure. Its action on
pulled-back characters is the existing character transport by definition.
Naturality supplies the commuting square between the acting groups and ambient
groups. `RelativeRoot.subgroup_transportCharacter` applies the published subgroup
transport theorem for that square and the arbitrary-base-change subgroup theorem.
Cancellation of the inverse isomorphism identifies the complete subgroup functors
on every scheme test. `RelativeRoot.subgroup_galoisTransport` specializes this
identity to the spectrum of an actual coefficient automorphism, using the existing
character-lattice Galois representation and subgroup Galois transport.

The rational-point comparison uses the existing `rationalConjugate` map, with its
existing multiplication convention. `galoisIdentityTestIso` identifies the identity
test whose structure morphism is twisted by the coefficient spectrum map with the
identity test itself; its underlying morphism is that same spectrum automorphism.
`descentPoint_rationalConjugate` proves that descending a conjugated rational point
is the original point restricted along this test isomorphism. The proof applies
the base-change point equivalence, its naturality, and the existing projection
formula for coefficient conjugation.

For any supplied all-test subgroup functor, functoriality along both directions of
that test isomorphism proves `rationalConjugate_mem_galoisTransport_iff`. Thus an
original rational point belongs to the original subgroup exactly when its actual
coefficient conjugate belongs to the transported subgroup.
`galoisTransportRationalEquiv` restricts coefficient conjugation to the resulting
multiplicative equivalence; its inverse is the inverse of the same coefficient
conjugation, with membership justified by the equivalence just proved.

`RelativeRoot.rationalConjugate_mem_subgroup_iff` combines that result with the
all-test root subgroup identity. `RelativeRoot.rationalGaloisEquiv` consequently
maps the rational subgroup at a character to the rational subgroup at its actual
Galois-transformed character. It composes the generic rational equivalence with
the identity equivalence of subgroups supplied by the all-test equality. The
stated coefficient formula proves that its carrier map is exactly the existing
`rationalConjugate`, with no new choice of point transport.

All content is derived internally from the imported transport, base-change,
character and point constructions. This unit supplies subgroup transport; the
construction of an apartment, a preserved valuation class, a metric, the
supplied-model stabilizer comparison and the full building comparison remain open.
