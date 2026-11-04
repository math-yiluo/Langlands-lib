# Conditional smooth real annihilation of a torus in the derived subgroup

Worker 1374. This internal construction assembles actual-point interfaces.
It retains general torus norm-kernel compactness and intrinsic relative-root
reflection existence as explicit proposition premises; it proves neither input.

Over any nonarchimedean local field in either characteristic and arbitrary
universe, let `G` be connected reductive and `j : T.toGrp → G` a closed torus
whose full range functor lies in `derivedSubgroup G`. Affineness and local
finite type of `T` are explicit instances. Given the two structural premises
and an ambient real homomorphism `f` with open kernel in the canonical point
topology, `torusImage_eq_one_of_structure` kills every actual `T(F)` point.
`torusImageToOpenRealKernel` restricts the actual point map of `j` to `f.ker`.

The implemented proof first restricts `f` to the actual common norm kernel of
`T`. The compactness premise equips that subgroup with a compact topology.
Continuity of the actual point map pulls back the open kernel. The existing
Weil finite-range theorem and torsion freeness of the additive real group
annihilate every norm-kernel point.

Choose an actual maximal split torus `A` in `T` and extend its closed composite
into `G` to an actual maximal split torus `S` there. Integral reflection data
from the reflection-existence premise supply the reflection predicate on the
actual rational root span. The adapter uses the existing coroot functional,
its self-pairing two and the implemented reflection action on root vectors;
spanning proves equality on the whole root span.

The split/norm factorization gives `x^N = i(a) * z` with fixed `N > 0` and
`z` in the actual norm kernel. The point `i(a)` lies in the algebraic derived
subgroup because the entire torus range does. The actual map `A → S` preserves
that same whole point, so the published split-torus annihilation theorem kills
it. The norm-kernel argument kills `z`; torsion freeness then kills `f(j(x))`.
No individual coordinate factors are asserted to belong to the derived group.

The codomain restriction is a group homomorphism with underlying value exactly
`rationalPoints.map j x`; `torusImageToOpenRealKernel_coe` records that formula.
An affine-hom instance for `G` is explicit in the interface and is supplied by
the connected reductive hypothesis. The proof installs smoothness from that
hypothesis when it needs the ambient locally finite type instance.

The provenance is internal: the compact-domain finite-range theorem,
torsion freeness of the real group, the actual torus split/norm factorization,
the maximal-split extension theorem and the existing whole-point split-torus
annihilation theorem imply the construction directly. The two unproved
structural statements remain explicit assumptions. No new literature
assertion is made.

This conditional construction does not prove the unrestricted ambient target.
The structural premises and the reduction of arbitrary derived points to
torus and additive images remain required. No commutator identification or
rational-point surjectivity of a central isogeny is used.

The four local affine and topology instances have module-specific names so
that joint imports do not collide with instances in adjacent modules. Their
types, bodies and local scope are unchanged.
