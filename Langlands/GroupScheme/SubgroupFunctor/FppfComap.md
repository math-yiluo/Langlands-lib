# Fppf inverse images reflect represented subgroup containment

`SubgroupFunctor.FppfComapReflectionStatement` is the `Prop`-valued
definition of containment reflection in an explicitly represented
subgroup. `fppfComapReflection` proves this named assertion using the
parameterized helpers below.

Fix an arbitrary scheme `S` and a homomorphism `q : G ⟶ Q` whose underlying
scheme map is flat, surjective, and locally of finite presentation.

`SubgroupFunctor.le_range_of_comap_le_of_fppf` proves that
`F.comap q ≤ (range j).comap q` implies `F ≤ range j` whenever
`j : H ⟶ Q` is monomorphic and `F` is any subgroup functor.
`comap_le_range_iff_of_fppf` includes the converse, and
`comap_le_iff_of_isRepresentedBy_of_fppf` uses an explicit representation of
the subgroup on the right.

`range_eq_of_comap_eq_of_fppf` and
`eq_of_isRepresentedBy_comap_eq_of_fppf` give equality reflection for two
monomorphically represented subgroups. No quasi-compactness assumption on
`q` and no representability assumption on `F` in the containment result
are required.

For a point `x : T ⟶ Q`, pull back `q` to obtain an fppf cover `a : V ⟶ T`
and a lift of `a ≫ x` to `G`. The assumed inverse-image containment places
this restriction in `range j`. Fppf morphisms are effective epimorphisms
in Mathlib; the published `mem_range_of_comp_mem_range` descends the
unique factorization through the monomorphism `j`. Equality follows by
applying containment reflection in both directions.

This is an internal derived variant of the published `FpqcComap` module,
using the fppf effective-epimorphism instance instead of its fpqc
instance. The results use actual pointwise range and full inverse image.
