# Irreducibility detected by an exact smooth functor

This internal algebraic prerequisite detects irreducibility of an actual
finite-length smooth complex representation using a supplied functor between
smooth representation categories. The group universes `uG`, `uH` and carrier
universe `uV` are independent. The groups have the group and topological-space
structures already required by `SmoothRep`; the theorem imposes no
representation-theoretic condition on either group.

`NonvanishingOnIrreducibleSubquotients J A` means that `J.obj D` has a
nontrivial carrier for every irreducible actual `SmoothRep.IsSubquotient D A`.
It uses actual objects and actual subquotient presentations. The supplied
`MapsShortExactIntertwiners J` hypothesis says that the functor preserves
injectivity, surjectivity and the equality of image and kernel for every
short exact sequence of actual smooth intertwiners. Finite length is finite
composition length for the group-algebra module underlying `A`.

The existing `Derivative.LevelCalculus.map_surjective_of_exact` applies
short exactness to the kernel sequence; the shared
`ExactSmoothTransport.map_isSubquotient` in
[`ExactSmoothSubquotients`](ExactSmoothSubquotients.md) combines this with
preservation of injections and the
published injection/surjection characterization of actual subquotients.
Nonvanishing passes to subquotients by the published transitivity theorem.
`obj_subsingleton` applies exactness to the identity sequence on a zero
carrier, proving that its image also has a zero carrier. Conversely,
`subsingleton_of_obj_subsingleton` uses finite length: a nonzero source has
an actual irreducible subquotient, whose mapped subquotient would be both
nonzero and a subquotient of a zero carrier.

For `isIrreducible_of_obj`, consider an arbitrary actual subrepresentation
`S` of `A`, with associated smooth objects `K` and `Q = A/S`. Finite length
and nonvanishing pass to both objects. Apply exactness to `K → A → Q`.
If `J(K)` is zero, the preceding detection lemma gives `S = 0`. Otherwise
the injective map `J(K) → J(A)` is nonzero, so irreducibility of `J(A)`
forces it to be surjective. Exactness and surjectivity onto `J(Q)` then make
`J(Q)` zero; detection gives `Q = 0` and hence `S = A`. Finally `A` itself
cannot be zero, because its irreducible image is nonzero.

`isIrreducible_of_finrank_eq_one` uses Mathlib's simplicity of the submodule
lattice of a one-dimensional vector space and the injective map from
subrepresentations to complex submodules. This gives
`isIrreducible_of_finrank_obj_eq_one`, the one-dimensional-image version of
the main criterion. No separate finite-dimensionality hypothesis is needed
when the finrank is one.

The provenance is internal: the proof is the elementary short exact sequence
argument above, using the Library's actual subquotient algebra and finite-length
constituent existence. Its direct project imports are `ExactSmoothSubquotients`,
`SubquotientAlgebraProof` and `Smooth.ConstituentSupport`. Before integration consolidation, the recursive
closure contained 116 existing project modules, with classification imports
limited to `ConstituentRelations`, `Segments`, `Supercuspidal`,
`SupercuspidalSupport` and `SupercuspidalTwist`. These provide definitions,
isomorphism transport and elementary implications, with no support-existence
or classification theorem. The actual helper proofs used here preserve
intertwiners, pass finite group-algebra length to subquotients, or extract
a factor from an actual finite composition series. None uses global support
decomposition, ordered quotient coverage, multisegment classification, or the
conclusions excluded by the repeated cuspidal triple task.

The functor's exactness, nonvanishing, source finite length and image
irreducibility or dimension are explicit hypotheses. This unit establishes
none of them for a particular derivative or induced representation. In
particular it does not prove a local rank-three structure calculation or
either ambient repeated cuspidal Jacquet transfer.
