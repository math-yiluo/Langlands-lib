# Existence of field pinnings

Author: Worker 1472.

This module defines two propositions over every field `k : Type u`.
It proves neither proposition.

`RootPinningExistenceStatement` takes an actual connected reductive group
`G`, a split maximal torus inclusion `i : T.toGrp ⟶ G`, a root datum `P`
with `IsRootDatumOf i P`, and any Mathlib base `b : P.Base`. It asserts
`Nonempty (RootPinning i P b)`. Thus every simple root in the supplied
base has a linear equivalence from `k` to its actual Lie weight space.
The conclusion uses the given torus, inclusion, root datum and base.
No finite-index or reducedness premise on the supplied datum is needed
for this conclusion: its root range is already the actual `roots i`,
and the assertion only chooses trivializations of those root spaces.

`SplitPinningExistenceStatement` starts with the actual connected
reductive group and a split maximal torus inclusion. It asserts
`Nonempty (SplitPinning G)`. In this conclusion, the finite root index,
realized reduced root datum, base and simple-root trivializations are
outputs, together with a split maximal torus of `G`. The bundled torus
is not required by this proposition to equal the supplied witness.
The statement does not take a root datum, a base or any Lie
trivialization as a premise.

These field formulations are derived from Conrad, *Reductive group
schemes* (2014), opening discussion of §5.1 and Definition 5.1.1,
printed/PDF p.136, and Definition 6.1.1, printed/PDF p.186. Over a field,
a connected reductive group with a split maximal torus has free
rank-one nonzero Lie weight spaces. Definition 6.1.1 chooses a base and
trivializing sections in its simple-root lines and explicitly records
that a pinning can be chosen for any positive system. For a field, a
trivializing section is encoded by a linear equivalence from `k` to the
line, with root vector its value at `1`. For the second proposition,
the actual finite reduced root datum and a base also have to be
constructed; the existing `RootDatumExistenceStatement` records the
root-datum part as a separate unproved proposition.

The imported maximal-torus predicate uses maximality among closed
field tori by factorization. Conrad uses geometric maximality and
records the equivalence with other field conventions on p.136.
The actual weight spaces retain the published equation on every
coefficient algebra and every torus point over that algebra. Affineness
for these Lie constructions is obtained from the supplied connected
reductivity proof. Both propositions retain arbitrary universe `u`
without a characteristic, perfectness or algebraic-closedness premise.

These propositions assert pinning existence only. They supply no
pinned isomorphism, automorphism section, descent datum, quasi-split
model, adjoint quotient or finite-Galois inner-form presentation.
