# Finiteness from affinoid target neighborhoods

`AffinoidAtlasPresentation.StrongHom.FiniteOverTargetLocalityStatement K`
is the forward target-local criterion for finite morphisms, expressed for
actual strong maps between saturated analytic presentations and open
subsets `V` of the source and `U` of the target.

The map sends `V` into `U`. At each `x ∈ U`, the hypothesis provides a
finite set `I` of recognized target affinoids. Every member contains `x`
and lies in `U`, and their union is a neighborhood of `x`. For every
`W ∈ I`, the literal full preimage `V ∩ g⁻¹(W.locus)` is a recognized
source affinoid `P`. The bounded map supplied by
`g.fullRecognitionPairs.pullback P W h` is finite Banach, including its
positive uniform bound for coefficient lifts.

The conclusion is the existing `g.IsFiniteOver V U`. It therefore
constructs such a recognized preimage and a finite actual bounded map for
**every** recognized target affinoid contained in `U`, including those
spanning several members of the supplied neighborhood families. Neither
recognition of those arbitrary preimages nor finiteness of `g` on open
neighborhoods is an additional premise. The finite family at a point is
allowed to have several members; a single affinoid neighborhood is not
assumed.

The field, space, and index universes are independent. The field is any
complete ultrametric normed field; trivial valuations and arbitrary
positive finite polyradii remain allowed. The analytic spaces need not
be globally Hausdorff.

## Source and adaptation

The source is V. G. Berkovich, *Étale cohomology for non-Archimedean
analytic spaces* (1993), Lemma 1.3.7(a) implies (b), printed pages 27–28,
retained PDF pages 24–25. It is registered as
`berkovich-1993-etale-cohomology`, SHA256
`06b42aca1c8f237e607d2cf1f15a41fdc9718324a4dc9fd5bce66574254bb91c`.
The lemma uses a finite affinoid family through each point whose union is
a neighborhood. Its conclusion tests every affinoid domain. Its proof
refines an arbitrary affinoid into finitely many domains subordinate to
the family, then applies Kiehl's theorem.

This is a derived relative-open formulation of that implication. Open
subspaces are expressed by the ambient sets `V` and `U`, recognized
subsets express their actual affinoid domains, and `IsFiniteBanach`
expresses finiteness of the actual affinoid algebra maps. This statement
does not assert the converse or the closed-immersion variant of the
source lemma. It is independent of a composable second map and of any
right-cancellation hypothesis.

## Proof boundary

This module defines only a proposition. It supplies no proof of the
criterion or of effective finite-affinoid descent. In particular, a
Banach matching algebra or an already supplied global output algebra
alone does not establish the missing affinoid realization. A proof must
construct the arbitrary recognized preimages and compare their entire
bounded algebra maps, with the stated valuation and radius scope.
