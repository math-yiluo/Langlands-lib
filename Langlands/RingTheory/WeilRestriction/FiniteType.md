# Finite-type affine Weil restriction

Worker 105 constructs the actual algebra representing
`T ↦ (C →ₐ[B] B ⊗[A] T)` for a finite projective commutative `A`-algebra `B`
and a finite-type commutative `B`-algebra `C`, over arbitrary commutative rings.
The generator type is finite; the defining ideal may have infinitely many relations.
This is the algebraic prerequisite of Brian Conrad, *Weil and Grothendieck
approaches to adelic points* (December 31, 2011), Example 2.4, printed page 3,
registered source `conrad-2011-weil-grothendieck-adelic-points`.

`Algebra.Generators.presentationOfKernel` uses every element of the actual kernel
as a relation. `generatorsCount` and `generators` choose a finite generating family
using Mathlib's `FiniteType.iff_exists_generators`. The algebra reuses
TauCeti's presentation-based coordinate construction, including its universal
point and bijection. The finite-type instance comes from its finite-variable
polynomial quotient, and `homEquiv_comp` is the naturality formula.

Topological comparisons of actual affine-scheme points, and the remainder of
Conrad Example 2.4, remain separate obligations.

`hom_ext` follows from injectivity of the representing equivalence. When `C`
is also finitely presented over `B`, `finitePresentationAlgEquiv` is the
canonical `A`-algebra isomorphism with the published
`TauCeti.Algebra.WeilRestriction A B C`. Its forward map is classified by the
old universal point and its inverse by the new universal point. The two
composites are identities because the representing equivalences are injective
and tensor maps respect composition. The theorem
`finitePresentationAlgEquiv_universalPoint` proves compatibility with the
universal point; `homEquiv_comp_finitePresentationAlgEquiv` identifies the
resulting bijections on points over every actual test algebra `T`.

This is a derived construction for the cited example, not a transcription
of a finite-presentation hypothesis. No field, Noetherian, faithful-algebra,
local-ring or separation assumption is required for this algebraic
representability result. Both finite generation and projectivity of `B` as
an `A`-module are explicit hypotheses. Topologies on `A`, `B` or `C` are not
inputs to this construction. Scheme-point and topology comparisons remain
obligations of the parent task.
