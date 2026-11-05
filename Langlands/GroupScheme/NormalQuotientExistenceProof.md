# Existence of unrestricted affine normal quotients

Author: Worker 1228.

`Langlands.GroupScheme.normalSubgroupQuotientExistence.{u}` proves exactly
`Langlands.GroupScheme.NormalSubgroupQuotientExistenceStatement.{u}`. For every
field `k : Type u`, every affine locally finite-type group scheme `G` over
`Spec k`, and every normal closed subgroup inclusion `i : N ⟶ G`, it produces
an actual group scheme `Q` over the same base and an actual homomorphism
`q : G ⟶ Q`. The structure map of `Q` is affine and locally of finite type.
The projection is flat, surjective and locally of finite presentation, and
the range of its actual pullback kernel equals `SubgroupFunctor.range i` on
every test scheme over `Spec k`.

The field and universe are arbitrary. Finite and imperfect fields, positive
characteristic, and nonreduced ambient groups and subgroups are included.
Surjectivity is that of the underlying scheme morphism. Full kernel equality
uses all relative scheme tests, including nonreduced tests.

The implemented proof instantiates the published
`normalQuotientExistence_with_structural_inputs` with the published proofs
`affineCartierSmooth` and `affineHomImage`. The first input supplies Cartier
smoothness in characteristic zero; the second supplies unrestricted affine
image factorization over every field. Both inputs are discharged by the
imported theorems.

The reduction first works over an algebraic closure in the same universe.
`MatrixRepresentation.normalKernelRepresentationWithCartier` constructs a
finite matrix representation with the prescribed full normal closed kernel.
Its characteristic-zero branch uses Cartier smoothness and the reduced
exact-kernel construction. Its positive-characteristic branch uses the
Frobenius construction. Factoring this representation through its actual
affine image gives the fppf projection and a locally finite-type affine
quotient over the algebraic closure. Effective affine quotient descent then
descends the group, projection and full kernel equality to the original
field. Local finite presentation descends along the projection and yields
local finite type of the quotient over that field. These constructions and
their supporting proofs are imported unchanged from
`NormalQuotientExistenceReduction` and its dependencies.

`normalSubgroupQuotientData` uses classical choice on the proved existence
theorem to return the actual `Q` and `q` as dependent data. Its subtype retains
the proofs of affineness, local finite type and the full fppf quotient
predicate. It has precisely the hypotheses of the existence theorem.

The mathematical target is J. S. Milne, *Algebraic Groups* (2017),
Proposition 5.18, printed p. 103 / PDF p. 119, and the affine case of
Theorem 5.14, printed p. 102 / PDF p. 118. The registered source is
`milne-2017-algebraic-groups`, SHA256
`899b0f44f3c3ccfbaf5ed1cf9c180be7a8016b1c0e9709ca0c206304e5bd1cd0`.
The complete registered author-errata snapshot
`milne-2017-algebraic-groups-errata-2026-11-02`, SHA256
`a0c3a10dc376e1c9bd1de05b33beaf7d54e5f1ea7b408d594cfd70231a7ba0cf`,
changes neither result nor Lemmas 5.16–5.17. The source uses Weil restriction
to pass to the original field; the implemented reduction uses effective
affine descent. This final module is an internal assembly of the published
constructions and proofs, with the provenance of their individual steps
documented in their paired modules. The original statement and its imports
are unchanged.
