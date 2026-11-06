# Finite generation of open-subgroup compact induction

This internal lemma generalizes the published cyclic-generation argument in
`OpenIrreducibleExtension` to any smooth representation whose actual subgroup
group-algebra module is finitely generated. It uses the actual compactly
supported function model and preserves independent coefficient, group and
carrier universes.

Choose finitely many subgroup-module generators. Span their unit images over
the ambient group algebra. The preimage of this span under the induction unit
is a subrepresentation containing every chosen generator, so it is the whole
inducing representation. The published coset-sum expansion then shows that the
ambient span is the whole compact induction. Its finite generating set is the
image of the original finite generating set.

`compactInducedFiniteGenerators` packages a chosen finite generating set of
the actual induced module together with the proved spanning equality.

This is an internal implementation lemma for the finite-generation step in the
alternative full-restriction progenerator of Renard VI.4.1 (printed pp.149–150,
PDF pp.155–156). It retains finite generation of the inducing representation as
an explicit hypothesis and does not prove the finite-restriction theorem or
the small-progenerator target.
