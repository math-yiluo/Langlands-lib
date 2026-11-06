# Full Tate-normalized CM models on componentwise admissible bases

Author: Worker 344.

This internal construction extends the actual normalized-model presheaf,
at one fixed original Harris level, to the full existing
`ComponentwiseAdmissibleCMBaseCategory`. It uses the same universe-zero
arithmetic data, `Prerequisites` package, and named duality, polarization,
Weil, adelic comparison and torsion inputs as the connected construction.
No new source theorem is asserted.

`TateNormalizedCMComponentwiseFamily` is the product of the actual
normalized quotient families over the actual open connected component
schemes `componentCMBase`. Given any morphism of the original test bases,
`tateNormalizedCMDisconnectedPullback` uses its actual map on connected
components and the restricted scheme morphism `componentCMBaseHomTo`.
The component pullback is the existing actual normalized-model pullback.
Every original test morphism is retained, with no arbitrary factorization
or replacement of the scheme map.

Forgetting normalized models on each component gives the original
`disconnectedClassTower` value. This forgetful map is injective and
commutes with the literal original disconnected pullback. These facts
transfer its identity and composition laws, including the original
component identifications, to `tateNormalizedCMDisconnectedPresheaf`.
The map `tateNormalizedCMDisconnectedForget` is natural on the full
test category. An empty base has precisely the empty-product value.

At a fixed level contained in the source integral lattice stabilizer,
the explicit `ProperFibreAmpleAffineOpenStatement` and
`CommensurableInvariantLatticeRealizationStatement` give an equivalence
on each component by the existing normalized-model existence result.
The product equivalence and the literal pullback square give
`tateNormalizedCMDisconnectedIso`. Its forward natural transformation
is exactly the componentwise forgetful map. Thus the comparison is with
the original presheaf on its full componentwise admissible test category,
under the stated hypotheses.

The presheaf and its pullback require none of these model-existence
hypotheses. This file does not assert preservation of full normalization
by every level transporter, remove the source-stabilizer hypothesis from
the equivalence, or construct a representing scheme or its admissibility.
The exact division-case representability target remains open.
