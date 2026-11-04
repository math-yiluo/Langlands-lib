# Maximal split tori of a simply connected cover

Authors: Worker 1463 and Worker 1469.

The theorem `Langlands.GroupScheme.simplyConnectedCoverSplitTorus` proves the
published proposition `SimplyConnectedCoverSplitTorusStatement.{u}` from
[`SplitTorusStatement`](SplitTorusStatement.md).
For every field `k : Type u`, a supplied simply connected cover `π : C → G`
and a maximal split torus `i : S → G`, it produces a maximal split torus
`j : T → C` and a homomorphism of commutative group schemes `f : T → S`
such that `j ≫ π = groupHom f ≫ i` and `groupHom f` is a central isogeny.

This is an internal consequence of the published theorem
`centralIsogenyMaximalSplitTorusLift` in
[`CentralIsogeny.MaximalSplitTorusLiftProof`](../CentralIsogeny/MaximalSplitTorusLiftProof.md)
and the accompanying
[`CentralIsogeny.Restriction`](../CentralIsogeny/Restriction.md).
The source provenance for lifting maximal split tori is documented in the
published lifting theorem and the unchanged target statement. This module
introduces no additional source assertion.

The Lean proof first extracts connected reductivity of `C` from
`hπ.isSimplyConnected.isSemisimple.isConnectedReductive` and of `G` from
`hπ.isSemisimple.isConnectedReductive`. It applies the published lifting
theorem to the central isogeny `hπ.isCentralIsogeny` and the given maximal
split torus. The result supplies `T`, `j`, `f`, maximality of `j`, the
commuting square, and flatness, surjectivity and local finite presentation
of the underlying scheme morphism of `f`.

The restriction lemma adds finiteness: the closed immersion `j` followed
by the finite cover `π` is finite, the square identifies this composite
with `f` followed by the closed immersion `i`, and `IsFinite.of_comp`
cancels that last immersion. Commutativity of `T` makes the full
scheme-theoretic kernel central, on every test scheme and after every
restriction. Together these fields give `IsCentralIsogeny (groupHom f)`.
Returning the same three objects and the supplied maximality and square
finishes the exact target.

The theorem is unconditional and universe polymorphic. It adds no
perfection, separability, characteristic or splitting hypothesis. The
universal-property field of the supplied cover is unused. All morphism
properties concern actual schemes; no surjectivity on rational points is
used, and `T` is not identified with the full inverse image of `S`.
