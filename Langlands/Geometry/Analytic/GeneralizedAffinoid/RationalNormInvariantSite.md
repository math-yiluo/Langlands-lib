# Finite sites of norm-invariant positive-radius rational charts

Authors: Worker 56 and Worker 36. Internal derivation adapting Worker 36's
published strict `InvariantRationalSite` construction to the actual
weighted rational chart category and its norm-continuous actions.

The inputs are an ultrametric normed field `K`, an actual
`PresentedAffinoidAlgebra K`, a topological group `G`, bounded algebra
automorphisms `ρ : G →* Aut A`, and continuity of every forward algebra
orbit. `H` is an open subgroup. The existing full category
`NormInvariantChart ρ hρ H` retains exactly those actual rational charts
whose loci are setwise preserved by `H`, and all their original bounded
restriction maps over `A`.

Completeness of `K` is required for the bounded intersection lift,
the terminal and finite-limit assembly, pullback stability and hence the
Grothendieck topology, and the quotient-spectrum comparison. The whole
and intersection objects and their locus identities, the covering
predicate, and its identity-cover and transitivity proofs require no
completeness.

`mem_normOpenStabilizer_inter` proves that preservation of two actual
loci implies preservation of their constructed weighted rational
intersection. Image under the ambient bijective spectrum operator
commutes with set intersection. This stabilizer lemma itself requires
no completeness of `K`.

In the `NormInvariantChart` namespace, `whole` retains the original
empty-numerator rational quotient and proves its invariance from
surjectivity of the ambient point operator. `toWhole` retains the bounded
whole-chart restriction, and `wholeIsTerminal` uses the proved uniqueness
of bounded restrictions. `inter`, `interLeft`, and `interRight` retain
the actual product-radius intersection quotient and both bounded
restrictions, with invariance proved by the preceding stabilizer lemma.
`inter_obj` and `locus_inter` identify the underlying original quotient
and its locus. `interLift` uses the published bounded rational quotient
pushout. `pullbackConeIsLimit` proves the universal property in this
full category of bounded restrictions over the fixed base. The
terminal object and constructed pullbacks give all finite limits.

`IsFiniteCovering` means that a sieve contains finitely many invariant
chart restrictions whose actual loci cover its target. The index type
belongs to the field universe and may be empty, as in the existing
ordinary finite rational topology. The identity singleton covers.
Intersecting each covering chart with an arrow's source constructs a
finite pullback cover: uniqueness of bounded restrictions identifies
the two triangles, and the actual intersection locus proves point
coverage. Dependent sums of finite index types construct composite
covers. These proofs give the Grothendieck topology
`NormInvariantChart.finiteRationalTopology`.

`ofArrows_mem_finiteRationalTopology_iff` characterizes finite generated
covering sieves by their original point coverage. Membership in a
generated sieve supplies a factorization through a generating arrow,
whose locus contains the corresponding covering locus.
`bot_mem_finiteRationalTopology_iff` shows that the empty sieve covers
exactly an empty locus, using the empty indexing type in the reverse
direction. `familyCovers_iff_jointlySurjective` reuses the original
rational spectrum-locus homeomorphism and bounded restriction triangle
to identify point coverage with joint surjectivity of the unchanged
continuous equivariant spectrum maps. This equivalence does not require
finiteness of the family.

The geometric conventions are Berkovich, *Non-archimedean analytic
spaces* (Trieste lectures, 2009), Definition 2.2.1 and Exercise
2.2.2(ii)-(iii), printed/PDF p.9, and Fact 2.2.3(i) and Definition
2.2.7, p.10. Registered source:
`berkovich-2009-trieste-analytic-spaces`, PDF SHA256
`8cfe4f6f35d5e717ac67c5c8f5ef9ff9185f460bbe5f9a10aeacd84cddeeb2ca`.
These give represented domains, positive-radius rational quotients,
their intersections and spectrum identification, and domain embeddings.
The actual constructions here are imported from the published
weighted rational algebra and chart modules; the invariant category,
finite limits and covering topology are internal derivations.

Berkovich's unfinished 1995-1996 manuscript, *Etale equivariant sheaves
on p-adic analytic spaces*, section 1.1 pp.1-3 and section 1.2 p.3,
motivates continuous group actions and equivariant sites whose covers
are underlying geometric covers. Registered folder:
`provided-7bb3903652336bd799aad8853b8efd7ff3bcc0c7652745417f4745a14ac08e90`,
digest `e046cadfb9dcec4b0cf6624f80d6316bf532416153b82023f5100bd1ab0726cd`;
PDF member *Berkovich--Etale equivariant sheaves on p-adic analytic
spaces (unfinished manuscript)--1996.pdf*, SHA256
`91567a75866a27cbe6690b6f075693df5afaa02524223d94d52ea37d77bb6637`.
The manuscript does not state this finite rational-site construction,
and its full analytic automorphism topology is not identified here
with the explicit norm-orbit input.

Field and group universes are independent. Arbitrary positive real
radii, trivial valuations, nilpotents, zero quotient algebras, and empty
loci and covers of empty targets remain included. Rational data retain
explicit unit generation; its implication of absence of common zeros
is used without claiming the converse. This is a local finite rational
site. Analytic-algebra sheafness, analytic atlases, full analytic group
topology, analytic etale and quasi-etale morphisms and sites, compact
and distinguished-domain lifting, and the Harris tower remain separate.
