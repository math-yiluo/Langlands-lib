# Ordinary pullback and local finite presentations

This supporting construction implements preservation of the local finite
presentation condition in Stacks Project, Lemma 99.5.2 (Tag 08KA,
`08KA.html`, source `stacks-coherent-sheaf-stack-08ka-2026-11-01`). It uses
Mathlib's `SheafOfModules.IsFinitePresentation`, which specifies finite
free presentations locally. The schemes and morphism are arbitrary; no
noetherian assumption or finiteness condition on the base is used.

`presentationPullback` applies the actual ordinary module pullback functor
to a free presentation. Pullback preserves colimits and the ring sheaf,
so the resulting cokernel presentation has the same finite types of
relations and generators. `presentationRestrictOfOver` and
`presentationOverOfRestrict` transport presentations through the existing
equivalence between the over-site and the open subscheme. The published
restriction comparison then gives `presentationPullbackOver` on each
inverse-image open.

`isFinitePresentation_pullback` pulls back a covering family of such
finite presentations. The inverse-image opens cover the source, so these
presentations witness Mathlib's local finite-presentation predicate there.
These constructions are supporting interfaces for the groupoid of flat
finitely presented families; relative flatness and proper support are
separate obligations.
