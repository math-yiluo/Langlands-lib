# Local twist separation in the actual rational Levi topology

This derived specialization applies the finite-locus and local-isolation results
of `RationalTwistLocalSeparation` to the actual rational points of a rational
Levi subgroup `l : M ⟶ P`.

`leviPointTopology_eq_canonical` explicitly checks by reflexivity that
`leviPointTopology l hl` is the canonical evaluation topology
`rationalPointTopology k M.X`. Indeed, `leviPointTopology` uses
`RationalPointFamily.pointTopology`, whose definition is precisely that topology.
Connected reductivity of the Levi supplies affineness and smoothness. Thus the
canonical rational-point results apply to the same topological group and the
same smooth representations, without an isomorphism or carrier replacement.

`leviUnramifiedTwistIsoLocus l hl A B` uses the smooth-twist expression
`A.twist ψ.val.toMonoidHom (unramifiedCharacter_isOpen_ker _ ψ)` from the exact
irreducible-induced-twist existence target. The declaration
`leviUnramifiedTwistIsoLocus_eq_canonical` proves that this locus is
definitionally the canonical rational-point locus. The two constructions of
the open-kernel proof do not change the resulting smooth twist.

For an irreducible smooth complex `A` and arbitrary smooth complex `B`, the
mixed locus is finite. Its nonidentity characters can therefore be excluded
by an open neighborhood of the identity. The final theorem pulls the
neighborhood back to two character families continuous at a common base
point, where both have value one: nearby their twists are isomorphic exactly
when the characters agree and the original objects are isomorphic. The
character group has the subspace compact-open topology. The field,
representation and parameter universes are independent.

The specialization assumes the nonarchimedean-group structure on `M(k)` used
by the target's open-kernel expression; for the target's actual parabolic data
it is supplied by `leviPoints_nonarchimedeanGroup`. It makes no admissibility
assumption. The underlying source motivation remains Konno (2003), Claim
4.2.1, printed page 403, and the implemented proof imports the derived
canonical separation lemmas. No separation of Weyl-transformed Jacquet
constituents or irreducibility of induction is asserted here.
