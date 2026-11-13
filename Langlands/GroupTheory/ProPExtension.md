# Pro-p normal subgroups and p-group quotients

This internal module packages inverse images of open normal subgroups
and proves the extension lemma for the Library's
`Langlands.Cohomology.IsProPSubgroup` predicate. All subgroup topologies
are the induced topologies.

`openNormalComap` pulls an `OpenNormalSubgroup Q` back along a continuous
homomorphism `G →* Q`. It uses the existing open-subgroup inverse image
and normality of the inverse image of a normal subgroup. The underlying
subgroup is exactly the usual algebraic inverse image. The source and
target may have independent universes.

Suppose `K` is normal in `G`, `K` is pro-p, and the abstract group
`G / K` satisfies `IsPGroup p`. Then
`isPGroup_openNormalQuotient_of_extension` proves that every quotient
of `G` by an open normal subgroup `N` is a p-group. For an element `x`,
the quotient by `K` supplies an exponent `p^m` with `x^(p^m) ∈ K`.
Pulling `N` back to `K` gives an open normal subgroup of `K`. Its
p-group quotient supplies `p^n` killing the image of `x^(p^m)`.
Consequently `x^(p^(m+n)) ∈ N`, as required.

`IsProPSubgroup.of_isPGroup_quotient` applies this argument to a subgroup
`H` of an ambient group. It assumes that `H` is compact and totally
disconnected and supplies a normal subgroup `K` of `H`, pro-p in its
induced topology, with `IsPGroup p (H / K)`. It then proves the full
`IsProPSubgroup p H` predicate. Primality is inherited from the pro-p
kernel, while compactness and total disconnectedness are the explicit
typeclass hypotheses.

No finiteness or openness of `K` is required by these lemmas: the
quotient assumption is the elementwise p-power torsion condition.
Applications to finite reductive reduction maps still have to supply
the actual kernel, its pro-p property, and the topology of `H`.
The module does not prove the smooth integral-model pro-p theorem
or KP Proposition 13.5.2. Its proof uses the existing pro-p definition
and elementary quotient-group identities, without an external
classification result.
