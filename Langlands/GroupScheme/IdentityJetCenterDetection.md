# Identity-jet detection of the centre

`DetectsCenter G n` says that the kernel of conjugation on the actual
order-`n` identity jet is the centre of `G`, as a subgroup functor.
Kernel membership requires fixedness on every relative scheme over the
test scheme. This predicate packages the internal interface to
representations obtained from the coordinate algebra of a finite jet.

For a smooth separated quasi-compact group over a quasi-compact base,
with geometrically connected fibres, `exists_order_detects_center`
gives one order that works on every test scheme. Central points fix
every jet by the conjugation formula. For the converse, apply the
finite-jet homomorphism comparison over the parameter scheme `G` to
universal conjugation and the identity. A point acting trivially on
the jet satisfies the comparison's hypothesis because the actual
identity jet commutes with base change. Equality of homomorphisms
then gives commutation after every refinement of the test scheme.
