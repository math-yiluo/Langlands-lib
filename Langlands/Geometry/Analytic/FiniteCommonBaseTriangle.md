# Actual finite affinoid triangles over a common base

This internal construction records the recognized affinoid triangle over one
recognized common-base subset `Z`. It assumes actual strong maps `g : A → B`
and `g' : B → C` on saturated analytic presentations, sets `V`, `U`, `T`, the
containment `g(V) ⊆ U`, finiteness of `g'` from `U` to `T`, and finiteness of
the specified saturated composite from `V` to `T`. The only condition on `Z`
is that its locus is contained in `T`. Openness is not needed for this local
construction.

`FiniteCommonBaseTriangle g g' V U Z` records recognized middle and source
subsets `P` and `Q` with the literal locus equalities

- `P = U ∩ (g')⁻¹(Z)`;
- `Q = V ∩ (g' ∘ g)⁻¹(Z)`;
- `Q = V ∩ g⁻¹(P)`.

It includes all three actual chart-image containments, finite Banach bounds
for the actual full-recognition pullbacks from `Z` to `P` and from `P` to
`Q`, and equality of their composite with the actual pullback from `Z` to
`Q`. The recognized subsets and their Banach algebras are those supplied by
the two finite-morphism hypotheses, rather than independently supplied
algebraic models.

`nonempty_finiteCommonBaseTriangle` proves that this data exists.
`finiteCommonBaseTriangle` chooses the resulting triangle. The proof applies
`IsFiniteOver` to `Z` for the second map and the composite. The containment
`g(V) ⊆ U` identifies the source subset with the preimage of the constructed
middle subset and proves admissibility of the actual intervening pullback.
`fullRecognitionPairs_comp` identifies the actual Banach maps. Finally,
`BoundedAlgHom.IsFiniteBanach.of_comp` transfers the composite's finite
Banach coefficient bound to the intervening map. It maps the composite's
coefficient lifts through the bounded pullback from `Z` to `P`, retaining
norm-controlled lifts.

The provenance is derived entirely from the published finite-morphism,
full-recognition composition and finite Banach cancellation interfaces.
No new external source assertion is used. Field, space and chart-index
universes are independent. There is no Hausdorffness, nontrivial valuation,
strictness or restriction on the allowed positive finite polyradii.

This construction concerns only the middle pieces obtained as preimages of
common-base pieces `Z`. It does not construct preimages of arbitrary
recognized subsets of `U`, does not assert `g.IsFiniteOver V U`, and does not
prove the host finite right-cancellation statement. The geometric upgrade
from this family to every recognized middle target remains a separate
prerequisite.
