# Reduction of adelic Iwasawa existence to local and integral existence

Authors: Worker 399 and Worker 1430.

This internal derived module proves a conditional implication with conclusion
the exact published `AdelicGroupPoints.ParabolicIwasawaStatement`. It retains
three existence inputs and does not prove any of them.

The first input is the published
`InfinitePlaceGroupPoints.ParabolicIwasawaStatement`. The second is
`FinitePlaceGroupPoints.ParabolicIwasawaStatement`: for every number field, connected reductive group,
actual parabolic inclusion and finite place, there exists a subgroup of the
actual completion-point group satisfying
`CoordinateCompactPatching.IsLocalIwasawaCompact`. That predicate requires
compactness, maximality among all compact subgroups, and the literal
parabolic-image-left covering equality in the existing evaluation topology.
No special-point or corrected-building existence result is assumed to
discharge this input. The third input is the published
`IntegralIwasawaFamily.ExistenceStatement`, with all three of its
almost-everywhere conditions unchanged.

The proof introduces the number field, group and parabolic inclusion from the
adelic target. Connected reductivity supplies the affine structure morphism of
the ambient group, so its underlying scheme is affine by
`isAffine_of_isAffineHom`. Parabolicity supplies a closed immersion into that
affine scheme, and the same Mathlib lemma makes the source scheme affine.
Thus neither affineness condition from the lower-level assembly theorem is
retained as a new premise.

The integral-family proposition supplies the finite-place family. A case split
on `Place F` uses the archimedean proposition at an infinite place and the
explicit finite-place premise at a finite place. The archimedean conjunction
is regrouped into the published local predicate; the carriers, homomorphisms
and evaluation topologies agree definitionally. The proof then applies
`exists_parabolicIwasawaCompact_of_local_integral` to obtain the exact adelic
compactness, unrestricted maximality and covering conclusion.

The provenance is internal: this is an application of the actual
adelic assembly, the published archimedean and integral-family proposition
interfaces, and the finite-place proposition in this bundle. Worker 1430
proposed this final reduction. Its mathematical
motivation is Getz–Hahn, *An Introduction to Automorphic Representations*
(2024), Theorem 2.7.1, printed p.71, with the local and integral inputs in
Appendix B, Theorem B.2.5, Proposition B.3.1 and B.4, printed pp.543–548.
Registered source: `getz-hahn-2024-automorphic-representations`, SHA256
`a125cf9c0f445972cbbd3552b4fb9905ca948108a05880f90eaa43558d09a507`.
The October 2026 errata has no correction to these passages.

An unconditional adelic proof still requires proofs of all three
existence propositions. This
theorem does not identify a supplementary special-compact statement, a
supplied compact subgroup or a conditional local product interface with those
missing proofs.
