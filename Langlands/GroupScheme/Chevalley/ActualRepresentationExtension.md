# Ambient subquotients for actual affine groups

This internal derived construction transports
`Chevalley.exists_corepresented_ambient_subquotient` through the existing affine
models of actual group schemes. It introduces no new structural premise or
external literature identification.

`MatrixRepresentation.HasAmbientSubquotients i` means that every actual
representation of the source of `i`, on `Fin n` for any natural number `n`, is
an actual subquotient of a restricted ambient representation on some `Fin m`.
The existing subquotient predicate requires an intermediate actual
representation with an injective intertwiner into the ambient representation
and a surjective intertwiner onto the specified source representation. The
intertwiner equations hold on every affine test algebra, including nonreduced
algebras.

The restriction lemmas preserve these intertwiners and subquotient witnesses.
For an intertwiner, evaluation after restriction is evaluation at the test
point composed with the given group-scheme morphism. For a subquotient, restrict
the intermediate representation and retain its two constant matrices and their
injectivity and surjectivity.

`Chevalley.hasAmbientSubquotients_of_isClosedSubgroup` proves the predicate
for every closed subgroup morphism `i : H → G` over a field, with `G` affine.
The closed immersion makes `H` affine as well. Choose affine models of both
groups, restrict the given representation to the source model, and apply the
corepresented ambient subquotient theorem. Restrict its witnesses back along
the inverse source-model isomorphism. The existing explicit formulas for
`modelMap` and `modelIso` identify this restriction with the restriction along
the original morphism `i` of the representation transported back to `G`.

`Lie.isSemisimpleElement_of_closed_subgroup` then applies the existing
subquotient semisimplicity theorem. Its hypothesis tests all actual ambient
representations by their dual-number differentials and geometric
semisimplicity over the algebraic closure. The ambient subquotient theorem
supplies a test for every source representation. Geometric semisimplicity
passes through its injective and surjective differentiated intertwiners.
The companion equivalence combines this reflection with the existing
preservation of semisimplicity under every actual group-scheme homomorphism.

All results allow an arbitrary field universe, empty coordinate sets, and
closed subgroups that are not smooth or reduced. No finite-type, connectedness,
infinitude, perfection, or splitting hypothesis is imposed. This contribution
does not prove the host Cartan-generation theorem.
