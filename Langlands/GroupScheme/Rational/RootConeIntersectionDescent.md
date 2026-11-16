# Descent of a smooth subgroup intersection

This internal helper first proves that the base-point equivalence for a
pullback commutes with group homomorphisms, and therefore preserves membership
in their represented subgroup functors.

For a smooth scheme-theoretic intersection of two supplied subgroups,
containment in a supplied closed subgroup can be tested on rational points
after any one algebraically closed extension in the same universe. The proof
uses smoothness to obtain reducedness and local finite type, identifies the
intersection range with the pointwise intersection, and applies the published
`SplitExistence.range_le_of_extPoints`. The base-point equivalence converts
the assumed containment into the factorization of every extension-valued
point needed by that theorem. The conclusion is containment on all scheme
tests.

These are derived categorical and geometric comparisons using published
Library results. No additional source premise is introduced.
