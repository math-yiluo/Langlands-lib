# Actual universal families of closed torus subgroups

Author: Worker 1656.

This internal interface expresses torus-subgroup moduli using actual group
schemes over an arbitrary scheme in universe `u`. Its ingredients are the
published subgroup-functor and arbitrary-base pullback constructions and
`RelativeTorus.IsTorus`, the predicate of being an étale form of a finite
split torus with locally varying rank. The module asserts no existence of
a moduli scheme.

`IsAdmissible F` asks for an actual group scheme `K` and homomorphism
`j : K ⟶ G` whose underlying scheme map is a closed immersion, with `K`
a relative torus and `j` representing exactly `F`. Representation is the
published `SubgroupFunctor.IsRepresentedBy`: the underlying map over the
base is mono and its pointwise range on **every** test scheme is `F`.
Thus this predicate concerns literal closed subgroup functors, independently
of the choice of a representing group scheme. It uses no geometric-point
substitute and imposes no connectedness condition on the ambient group.

For a parameter scheme `M/S` and an actual homomorphism `j : K ⟶ G_M`,
`familyHom j a` pulls `j` back along the actual scheme map underlying
`a : T ⟶ M`, and then identifies its ambient target with `G_T` using
`Descent.pullbackComparison M.hom a.left T.hom (Over.w a) G`.
`evaluate j a` is the actual range of this resulting homomorphism.
It is a subgroup functor on all schemes over `T`, including nonaffine
and nonreduced ones.

`IsUniversal j` says that, for every `T/S` and every admissible subgroup
functor of `G_T`, there is a unique actual parameter morphism `a : T ⟶ M`
whose evaluated subgroup functor equals it. Closedness of `j` and the
relative-torus property of `K` are separate hypotheses; together they
ensure that every evaluation is admissible by the lemma
`isAdmissible_evaluate`. Consequently this condition is the intended
all-test existence-and-uniqueness condition for such a family, without
assuming any supplied moduli object.

The implemented elementary lemmas use closed-immersion monomorphy to show
that a closed torus inclusion represents its range. The base-change lemma
pulls back all three parts of an admissible representative. Closedness of
`familyHom` follows by composing the pulled-back closed immersion with
the actual comparison isomorphism; its source is a relative torus by
arbitrary base-change stability. These facts establish admissibility of
every evaluated family. No representability or smoothness theorem is
proved or assumed by this module.
