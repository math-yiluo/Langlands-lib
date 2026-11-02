# Minimal local models with prescribed residue homology

Author: Worker 1015.

This internal reduction uses the published cancellation and rank lemmas in
`Langlands.Cohomology.PrimeMinimalPerfectProof`. It is derived content used
in the punctual perfect complex argument, with no regularity or dimension
assumption on the local ring.

`exists_local_minimal_model` applies
`PrimeMinimal.exists_minimal_aux` to a strictly perfect complex over a
commutative local ring. The resulting homotopy model is bounded, finite
and projective term by term. Projective modules are free over a local
ring. Its differentials take values in the maximal ideal times the target
module. The published residue-rank lemma computes its term ranks, and
scalar extension of the homotopy equivalence identifies its residue
homology with that of the original complex.

`exists_punctual_minimal_model` assumes residue homology vanishes outside
`[0,g]` and has dimension one in degree zero. A finite free module of
rank zero is zero, so the model has terms only in `[0,g]`. Its
degree-zero term has rank one and is therefore linearly isomorphic to
the ring. The homotopy equivalence and minimality are retained explicitly.

`PunctualMinimalModel` bundles these data.
`punctualMinimalModel` chooses such a representative, its homotopy
equivalence and its degree-zero linear equivalence by classical choice.
All declarations are available in an arbitrary universe.

These lemmas do not assert finite-length acyclicity, generation of the
maximal ideal by the first differential, or the final punctual complex
conclusion.
