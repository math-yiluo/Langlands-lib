# Commutators in the kernel of a relative-torus quotient

`TorusQuotientCommutatorsStatement` asserts the following in every universe.
Let `S` and `S'` be schemes, let `d : D ⟶ G` and `q : G ⟶ Q` be group-scheme
homomorphisms over `S`, and suppose
`RelativeRoot.IsFppfQuotient (SubgroupFunctor.range d) q` and
`RelativeTorus.IsTorus Q`. For every map `b : S' ⟶ S`, the full range of the
actual base-changed map `d` contains the commutators on every test scheme
over `S'`. `torusQuotientCommutators` proves this statement; the method
`RelativeRoot.IsFppfQuotient.containsCommutators_range_baseChange_of_isTorus`
provides it for supplied data. No closedness, reductivity, field or additional
base hypothesis is assumed.

This is an internal consequence of the published full-kernel definition of
`IsFppfQuotient`, commutativity of relative tori, and elementary base change of
subgroup functors. It supplies commutator containment on the geometric fibres
in the central multiplication argument of Task 6385. It does not assert that
the supplied subgroup is the derived subgroup, construct a central torus or
prove a central isogeny.

The implemented proof first establishes the general method
`RelativeRoot.IsFppfQuotient.containsCommutators_of_isCommMonObj` for any
specified subgroup functor and any commutative quotient target. The kernel
clause of the quotient predicate identifies that subgroup functor with
`SubgroupFunctor.range (kernelι q)`. The published
`SubgroupFunctor.containsCommutators_range_kernelι` then applies: a
homomorphism to a commutative group kills every commutator.

For a relative-torus target, `RelativeTorus.IsTorus.isCommMonObj` supplies
commutativity. The proof transports the resulting containment along any
base change with `SubgroupFunctor.ContainsCommutators.baseChange`, and
`SubgroupFunctor.range_baseChangeHom` identifies the resulting subgroup
functor with the full range of the actual base-changed map. This uses only
the original quotient's kernel clause; it needs no lifting of points along
the quotient map and no surjectivity on the original test's point groups.
