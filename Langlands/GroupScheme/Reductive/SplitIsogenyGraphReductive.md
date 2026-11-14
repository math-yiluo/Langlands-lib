# Reductivity of local-isogeny graphs

This derived support proves connected reductivity of an actual smooth connected
affine graph with flat surjective projections to two connected reductive groups.
It works over any field in the original universe.

Base change both actual projections to an algebraic closure. Flatness and
surjectivity survive base change, so the extended projections are epimorphisms.
A smooth connected normal unipotent closed subgroup maps trivially under both
extended projections by `normal_unipotent_comp_eq_one`, using the two ambient
geometric-radical hypotheses. The base-change point equivalence and the graph's
joint projection injectivity show that its inclusion is the trivial morphism.
Its subgroup functor is therefore trivial. This is exactly the required
geometric unipotent-radical condition on the original graph. No claim that an
arbitrary smooth connected subgroup of a reductive group is reductive is used.

The specialization to a local-isogeny family applies the two proved projection
geometry results under source and target simple-direction coverage. The generic
chamber-centralizer identities follow from the published generic-centralizer
and maximal-torus-centralizer theorems. Thus the explicit hypotheses retain
two actual maximal split tori, the actual torus isogeny and both root data, with
possibly different characteristic-power local maps.

These results do not prove transport of simple systems, identify the graph
torus as maximal, or make the first graph projection invertible. Those are
separate remaining obligations for general split isogeny realization.

`ReductiveLocalIsogenyGraphEnvelope` retains a certified graph with both
faithfully flat projections and its connected reductivity. Its constructor
applies the general arbitrary-field theorem to the two actual projection
geometries and ambient reductivity hypotheses.
