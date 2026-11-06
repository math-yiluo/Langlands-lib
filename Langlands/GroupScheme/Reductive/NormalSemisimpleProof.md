# Semisimplicity of smooth connected normal subgroups

`finiteCenterOfNormalSemisimpleUnconditional` constructs `FiniteCenter H`:
an actual group scheme representing the full scheme-theoretic centre of
`H`, its closed inclusion, the all-test centre representation property,
and finiteness of its structure morphism. Its inputs are a semisimple
ambient group, a closed normal inclusion, and smoothness and connectedness
of the subgroup. It specializes the published
`finiteCenterOfNormalSemisimple` construction using the unconditional
`normalReductiveCenter` theorem.

`IsSemisimple.of_normalSubgroup` proves that a smooth connected closed normal
subgroup `H` of a semisimple group scheme `G` over any field is semisimple.
The field and schemes have arbitrary universe `u`; there is no restriction
on the characteristic. Normality is the existing all-test normality of the
range of the given closed inclusion.

The theorem combines `IsConnectedReductive.of_normalSubgroup` with the
constructed finite centre. The imported construction first proves
connected reductivity of `H`, represents its full
scheme-theoretic centre, and uses the centre containment to embed that centre
as a closed subgroup of the finite centre of `G`. This makes the full centre
of `H` finite and proves semisimplicity, including possible nonreduced
centres. No structural premise remains in this theorem.

The provenance is internal composition of the published
`Reductive.NormalSemisimpleReduction` and `Reductive.NormalCenterProof`
interfaces. This supporting result supplies semisimplicity of the prescribed
subgroup in the normal-isogeny-complement problem; it does not construct a
complement or prove that problem's exact proposition.
