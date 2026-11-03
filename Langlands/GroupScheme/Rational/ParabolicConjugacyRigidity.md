# All-test conjugacy rigidity from rational-point Tits transporters

This is derived infrastructure. The general construction assumes a Tits
system on the actual group of points of `G` over its base scheme. It applies
to any two subgroup functors whose base-valued subgroups contain `B`.

`SubgroupFunctor.mem_of_eq_comap_innerIso_of_tits` starts from the actual
all-test equality `P = Q.comap (G.innerIso g).hom`. For `b ∈ B`, containment
in `P` and the equality give `g * b * g⁻¹ ∈ Q` at the base test scheme.
The abstract transporter theorem, applied to `g⁻¹`, therefore places
`g⁻¹` in `Q`. Closure under inversion places `g` in `Q`.

`rationalConjugatingPointInSubgroup_of_tits` restricts that same actual
rational point to the target subgroup at the base test scheme. It changes
neither the ambient point nor the stated all-test conjugation equality.

`eq_of_isRationallyConjugate_of_tits` obtains a point `g` from rational
conjugacy, applies the membership theorem, and then uses the published
`comap_innerIso_hom_eq_of_mem`. A point of `Q` over the base restricts to a
point of `Q` on every test scheme. Subgroup closure on each test scheme makes
its inner conjugation preserve `Q`, so the original all-test equality yields
`P = Q`.

This argument does not infer equality of subgroup functors from equality of
their base-valued point sets. It proves membership of the actual rational
conjugating point, then uses functorial restriction. Thus it needs no
geometric-point detection, density, reducedness, or infinite-field premise.

`standardParabolic_eq_of_isRationallyConjugate_of_statements` specializes to
the full arbitrary-field, arbitrary-universe reductive setting. It explicitly
assumes the published `RelativeTitsSystemStatement` and
`StandardParabolicOrderStatement`. Order gives
`standardParabolic i ν ∅ ≤ standardParabolic i ν J` for each valid index
`J`, so its base-valued points contain the `B` of the relative Tits system.
The general functor theorem then proves equality of rationally conjugate
standard functors on every test scheme.

The specialization retains connected reductivity, the actual maximal split
torus, and the generic cocharacter. It adds no characteristic, perfectness,
splitness, root nonemptiness, or properness condition. The two structural
statements remain premises: this module proves neither their realization nor
the unconditional classification statement. The entire proof route is an
internal consequence of the published functor, conjugation, order, and Tits
interfaces, with no additional external source claim.
