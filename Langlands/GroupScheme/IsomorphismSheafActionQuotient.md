# The action quotient of the full Isom sheaf

Worker 812. This internal construction uses the published `LocalGroupIso`
families, their fppf sheaf property, actual automorphic actions, and Mathlib
fppf sheafification. It assumes no scheme representing Isom and cites no new
literature theorem.

`LocalGroupIso.ActionQuotient.act` is inverse precomposition by the supplied
automorphic action `a : AutomorphicAction A G`. Its identity, multiplication
and refinement laws are checked on every further relative test. The actual
orbit relation is an equivalence relation and is preserved by refinement,
giving a presheaf of orbit classes.

`ActionQuotient.sheaf` is the fppf sheafification of that presheaf, and
`classMap` maps the full Isom sheaf to it. The class map is locally surjective
because each presheaf orbit class has an actual family representative and the
sheafification unit is locally surjective. Acting by an actual point preserves
the class. Equality of two class sections implies that the two families differ
by an acting point after restriction along an fppf covering sieve, using local
injectivity of the sheafification unit.

When the supplied source action is faithful on all refinements, it acts freely
on every Isom family: equality of the twisted families can be cancelled through
their pointwise multiplicative equivalences, and faithfulness detects the
acting points. For two families with equal quotient sections, choose local
acting points on the covering orbit sieve. Freeness makes them compatible,
and the represented fppf sheaf of acting points glues them. Separatedness of the
full Isom sheaf verifies the resulting global orbit equation. Thus
`existsUnique_act_of_classMap_eq` gives a unique acting point on the original
test, and `classMap_eq_iff` identifies the kernel with the actual orbit
relation there. This uses faithfulness explicitly; it is not asserted for a
general action.

The acting group and action are arbitrary. Identifying this construction as
the outer Isom sheaf requires the appropriate source adjoint action. Scheme
representability of this quotient and of the full Isom sheaf remain separate
obligations.
