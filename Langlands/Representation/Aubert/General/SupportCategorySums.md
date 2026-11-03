# Arbitrary invariant sums in the full smooth support category

`supportSubrepresentationSum` constructs, inside a fixed actual smooth
representation `E`, the invariant sum of all subrepresentations in
`IsInSupportCategory P M U h hU IsAssociate I hM hI`.
It is the largest subrepresentation in that support category. Its defining
family is a subtype of the actual invariant-submodule type; it requires no
categorical coproduct or resizing of representation carriers.

The intrinsic laws prove closure under arbitrarily indexed invariant sums,
the equivalence of membership of a sum with membership of all summands,
membership of the supported sum, and its universal property. They apply to
the full smooth category, including empty sums, without finite length or
admissibility. The indexing universe in the closure theorem is independent
of the group and carrier universes.

The argument is internal and derived from the published definition of
`IsInSupportCategory`, its actual-subquotient closure law, and the actual
constituent theorem `SmoothRep.irreducibleSubquotient_iSup` implemented in
`Category.SubrepresentationSums`. That theorem places every irreducible
actual subquotient of the sum in one summand. Applying that summand's defining
support condition proves closure; the universal property then follows
directly from the invariant-submodule supremum.

This construction does not assert that the supported sum is a direct summand,
construct a block decomposition, or establish preservation by induction or
Jacquet restriction. Those representation-theoretic steps remain separate
obligations for the general Aubert support-stability target. No classification,
geometric-lemma, adjunction, or character independence theorem is invoked by
this unit. The target and its imported Lean/Markdown pairs are unchanged.
