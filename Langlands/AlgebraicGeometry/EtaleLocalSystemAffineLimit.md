# Trivializations on affine inverse limits

`EtaleLocalSystem.exists_level_trivialization` is an internal step in the
formalization of Conrad, *Reductive group schemes*, proof of Corollary B.3.6.
Given a cofiltered diagram of affine schemes over an affine base and a
trivialization of a finitely generated local system on its limit, it obtains
a trivialization at some stage with the same coefficient group.

Refine a trivializing étale cover of the base by affine opens of the cover
members. Their images form an open cover of the affine base, so compactness
gives a finite family of affine étale charts. On the pullback of each chart
to the limit, the two trivializations differ by a locally constant family of
additive equivalences. The affine-limit descent for locally constant functions
brings these families to a common stage, where they give isomorphisms with the
desired constant model.

The two isomorphisms on each pairwise overlap agree after pullback to the limit.
Express them using one of the original chart trivializations on that overlap.
Eventual equality of the resulting locally constant functions forces the
isomorphisms to agree at a further stage. Cofilteredness gives a single stage
where all pairs agree. The étale gluing theorem gives the desired isomorphism
there.
