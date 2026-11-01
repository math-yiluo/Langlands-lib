# Split-kernel Haar ratio for a full kernel intersection

Author: Worker 499.

This internal derived module proves that the actual character
`Langlands.Induction.splitKernelHaarRatio` is the constant character `1`
whenever the inducing subgroup contains the whole kernel. Its hypotheses
are the topological-group, Borel and local-compactness hypotheses of that
character, together with its actual section-containment and closed-subgroup
hypotheses. The groups have independent universes.

The continuous multiplicative equivalence
`splitKernelFullIntersectionEquiv` forgets only the redundant inducing
subgroup membership from `H.comap r.ker.subtype`. Its inverse inserts
that membership using `r.ker ≤ H`; its underlying kernel element is
unchanged. The equivalence intertwines the restricted inverse section
conjugation and the actual kernel inverse section conjugation by
definitional equality. The published
`Langlands.Geometric.haarChar_eq_of_conjugacy` makes their Haar scaling
factors equal, and their ratio is `1` because Haar scaling is positive.
No measure normalization, compactness or triviality of the kernel is
assumed. This is a computation of an existing character, with no
compact-induction or normalized representation comparison asserted.

The helper does not require a topology on the target group, continuity of
the homomorphisms, a split identity, or local compactness of the ambient
group: its explicit kernel local-compactness and Borel structures suffice
to form the existing character. The full-intersection equivalence itself
needs only the ambient topology and the kernel-containment hypothesis.
The intersection's local compactness is derived from the actual closed
intersection, as in `splitKernelHaarRatio`.

The proof uses only published split-kernel conjugation, restriction of a
continuous automorphism to a subgroup, equality of Haar scaling under
continuous conjugacy, and cancellation of a nonzero positive scalar.
These elementary dependencies introduce none of the host task's excluded
derivative, segment, classification, supercuspidal, Whittaker-finiteness,
plus-functor, adjunction or consumer conclusions. The concrete application,
its original-source motivation, complete import closure and condition-by-condition
audit accompany this helper in
`Langlands/Representation/Derivative/MirabolicProductMinusLeftPhiHaar.md`.
That closure includes both direct imports of this helper and all their
transitive project dependencies. The proof is an internal derivation from
the stated published constructions; no peer draft contributes a proof body.
