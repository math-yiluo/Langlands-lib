# Base-point homomorphisms of automorphic actions

This internal construction packages evaluation of an automorphic action on
sections as `AutomorphicAction.basePointHom`, a group homomorphism to actual
group-scheme automorphisms. Its values are the existing `basePointIso`s.
Multiplicativity follows from the action law on every test scheme and the
composition convention for `CategoryTheory.Aut`.

A faithful action makes this homomorphism injective: equality of the actual
automorphisms implies equality of their actions after every refinement of the
base test. The existing all-test faithfulness theorem for a supplied fppf
quotient by the full centre therefore proves injectivity for its descended
conjugation action.

For such a quotient over any scheme base, an automorphism of the original
group induces an automorphism of the quotient, using the published
`RelativeRoot.IsFppfQuotient.mapIso`. The original automorphism intertwines the
two conjugation actions. The proof checks this after pulling back the flat
surjective quotient, where the acting point lifts and the assertion is the
ordinary conjugation identity. This gives the exact transport identity for
base-point automorphisms, and proves that their image is normal.

These are derived constructions and elementary consequences of the published
action, quotient-descent and faithfulness interfaces. No reductivity,
connectedness, affineness, pinning, global lift of a quotient point, or
representability of an automorphism functor is assumed. They supply the inner
factor for the automorphism decomposition in Conrad, *Reductive group
schemes* (2014), Theorem 7.1.9(1), printed/PDF pp.245–246, but do not prove
that decomposition or its pinned splitting.
