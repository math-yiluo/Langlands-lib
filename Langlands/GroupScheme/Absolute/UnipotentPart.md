# Greatest unipotent subgroups and changes of presentation

`IsUnipotentPart i` asserts that `i` is a smooth connected unipotent closed
subgroup whose all-test range contains the range of every unipotent closed
subgroup of the ambient group. Competing unipotent subgroups need not be smooth
or connected. This packages the greatestness clause of the published
`SolvableUnipotentPartStatement`; normality is not a separate field.

This is derived infrastructure for Milne 2017, Theorem 16.33(a)–(c), and
Proposition 17.14. The predicate can be formed for any ambient group. The
existence theorem assumes an algebraically closed field and a smooth connected
solvable affine ambient group, exactly as the published
`solvableUnipotentPart` theorem does.

Two unipotent parts have equal ranges by greatestness in both directions.
Their monic representatives therefore have a source isomorphism commuting
with the inclusions. The source and ambient isomorphism transport lemmas
transport closedness, smoothness, connectedness and unipotence through the
underlying isomorphisms. For greatestness, an ambient isomorphism pulls a
competing subgroup back, applies the original greatestness property, and
pushes the resulting factorization forward. All range inclusions hold on
every test scheme.

Source: James S. Milne, *Algebraic Groups* (2017), source ID
`milne-2017-algebraic-groups`, SHA-256
`899b0f44f3c3ccfbaf5ed1cf9c180be7a8016b1c0e9709ca0c206304e5bd1cd0`,
Theorem 16.33(a)–(c) and Proposition 17.14. These helpers retain the published
unipotent-part theorem's hypotheses and do not assert quotient compatibility.
