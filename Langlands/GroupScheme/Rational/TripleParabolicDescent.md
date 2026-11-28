# Descent from a cyclic triple of parabolics

`exists_tripleParabolic_descent` takes a connected reductive group `M`
over an infinite field `F` and a cyclic cubic Galois extension `K/F`.
Three cocharacters of a split torus in `M_K` satisfy the zero-sum and
root-weight conditions of `exists_open_tripleParabolic_rationalLift`.
The first parabolic, transported by a generator and its square, is
assumed to be conjugate over `K` to the second and third parabolics,
respectively. The result is a closed connected reductive subgroup of
`M` whose base change is a rational conjugate of the dynamic centralizer
of the first cocharacter difference.

The proof chooses a point over `K` whose translated Galois tuple lies
in the open lifting neighborhood. The common rational left factor
simultaneously conjugates the three model parabolics to the orbit of
one parabolic. Their intersection is the conjugated centralizer by
`parabolic_inf_parabolic_inf_parabolic_eq_centralizer`. The generator
cyclically permutes the three members of the orbit, making their
intersection Galois invariant. The closed-subgroup descent theorem
gives the subgroup over `F`. Dynamic centralizer reductivity and
reflection along the field extension give connected reductivity over
`F`.

This formulation isolates the geometric descent in the cyclic
construction of Platonov and Rapinchuk, *Algebraic Groups and Number
Theory* (1994), §6.8, printed p. 372. The same hypotheses can be used
with triples in different root systems.
