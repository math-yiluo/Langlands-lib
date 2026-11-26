# Intertwining transport and tensor twist

The representation-theoretic reduction follows the proof of Proposition
(5.3.2) in Bushnell–Kutzko, *The admissible dual of GL(N) via compact open
subgroups* (1993), printed pp. 176–177, registered as
`bushnell-kutzko-1993-admissible-dual-gln` with SHA-256
`811693b94c03fcbc2cfe33955bc5a00b0fc0b5645ca343f8cc1a3c6511de9c73`.
The space `intertwiningSpace` uses the `Hom(ρ^y, ρ)` direction.

Restriction keeps the underlying linear map. Transport across an isomorphism
of representations conjugates that map by the two restricted isomorphisms.
For a double coset element `a * y * b`, conjugation by `b` sends the domain to
that of `y`. Precompose an intertwiner by the inverse action of `a` and
postcompose by the inverse action of `b`. Applying the construction with
`a⁻¹` and `b⁻¹` proves invariance of the intertwining condition.

Let `K` and `U` be subgroups of `J`. Assume the intersection associated to `y`
factors as the product of those associated to `U` and `K`. A map intertwining
`ξ` on the `U` intersection then intertwines on the full intersection, since
`ξ` is trivial on `K`. Conversely, restriction to the `U` intersection keeps
the same map. On the `K` intersection the tensor coefficient lemma produces a
nonzero intertwiner of `κ` from any nonzero tensor intertwiner. At an element
where the restricted `κ` intertwining space has dimension at most one, the
restriction of a nonzero full `κ` intertwiner spans that space. The tensor
intertwiner equivalence gives equality of dimensions there.

`tprod_intertwining_of_restriction` combines these facts for a prescribed
subset `B` of the ambient group. Both representations are finite-dimensional
and complex, and `ξ` is trivial on `K`. Its input includes the restricted support
in `K · B · K`, the full `κ` intertwining on `B`, the dimension bound on the
restricted spaces at `B`, and the common-domain product on `B`. It concludes
the double coset support and the dimension comparison on `B`.
