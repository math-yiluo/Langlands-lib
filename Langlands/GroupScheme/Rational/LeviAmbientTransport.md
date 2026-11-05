# Ambient isomorphisms of actual rational Levi subgroups

This internal derived unit supplies transport lemmas for the existing
`IsRationalLeviSubgroup` predicate. It is used when conjugating a Levi by a
rational point of its ambient parabolic.

`subgroupMultiplication_postcomp` identifies multiplication of two
postcomposed subgroup maps with their original scheme multiplication followed by
the ambient group homomorphism. This is an equality of actual morphisms of
schemes over the base, proved by the group-homomorphism multiplication law.

`LeviSubgroup.IsGeometricUnipotentRadical.comp_iso` transports a specified
geometric unipotent radical through an ambient isomorphism. It applies the
published `IsUnipotentRadical.comp_iso` both over the ground field and after
algebraic-closure base change. The base-change functor carries the ambient
isomorphism to the isomorphism required in the second application.

`IsRationalLeviSubgroup.comp_iso` retains the original connected reductive Levi
source and transports its closed embedding and the ambient affineness. It
postcomposes the specified geometric unipotent radical with the same ambient
isomorphism. The multiplication equality above expresses the new Levi-first
multiplication as a composite of isomorphisms, so it remains an isomorphism.

These are formal consequences of the published definitions and the radical
transport lemmas in `Rational.PseudoParabolicAmbientTransport`. They assert no
Levi-existence theorem.
