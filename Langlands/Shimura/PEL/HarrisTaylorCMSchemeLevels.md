# Scheme levels derived from exact CM representability

This module derives actual scheme maps from the exact previously defined
`CMRepresentabilityStatement`. A proof of that existence proposition is still
required. All named tensor, Picard, polarization, Weil and admissible-base
prerequisites remain explicit. The source division/global hypotheses remain
necessary for a source-based existence proof; they are not proved here.

For a pointwise family of exact representations, `representedCMBaseTower` uses
fully faithful lifted Yoneda to recover the transition whose action on the
represented presheaves is the existing moduli transition. The identity and
composition laws follow by applying the faithful Yoneda functor and cancelling
the representation isomorphisms. `representedCMBaseTowerRepresentation` gives
the resulting natural isomorphism of level-indexed presheaves.

`representedCMOverTower` and `representedCMSchemeTower` forget the admissible
predicate and then the over-category structure. These are actual schemes and
actual scheme morphisms. The over-category equation and the formula on actual
test-scheme morphisms are proved, and Yoneda compatibility uniquely determines
each transition. `chosenCMLevelRepresentation` chooses witnesses from the exact
existence proposition, and `cmSchemeTower` applies this construction to them.
No arbitrary maps are supplied in the input evidence. Smoothness and the actual
projective-space immersion are retained as results on each over-category level.

`representedCMBaseTowerComparison` compares two such choices by taking the
Yoneda preimage of their common interpretation in the same moduli presheaf.
Faithfulness proves its naturality; the comparison respects the representing
isomorphisms, equals the identity for identical choices and satisfies the
cocycle equation. Forgetting to actual schemes yields
`representedCMSchemeTowerComparison`. Thus the construction is canonical up to
these specified comparisons, even when pointwise representatives differ.

These are categorical consequences of the exact representability target, not a
proof of existence, finite etaleness, Galois covers, complex uniformization or
coefficient descent. The category remains the explicitly restricted
componentwise admissible CM category, including the original transporter arrows
between sufficiently small levels. The source motivation is Harris–Taylor
(2001), III.1, printed pp.90–91, with the running hypotheses of I.7, printed
pp.51–55 (one-based PDF pp.98–99 and pp.59–63, respectively), registered as
`harris-taylor-2001-geometry-cohomology-simple-shimura`, SHA-256
`5be28164b61d6f6cc28dd9e6b990d669504f3470860b230ebbc97e3da10af56b`.
The proof here is the intrinsic Yoneda argument implemented with Mathlib's
`ULiftYoneda.fullyFaithful` and its actual inverse on morphisms. It does not
invoke the unproved source representability assertion. All new code and prose
are by Worker 57. The pinned environment is Lean 4.34.0 and Mathlib
`5ed2965256430c3649e86755f9576b54eca72435`.
