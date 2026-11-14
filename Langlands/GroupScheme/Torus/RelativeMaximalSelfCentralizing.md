# Relative maximal tori with smooth centralizers

This is internal support for the derived-group correspondence. All declarations
use an arbitrary universe. The general comparison works over any scheme; its
split-torus consequence works over the spectrum of any commutative ring.

`torusCentralizerFactorIsoOfResidueFibres` starts with a commutative group
scheme `T`, a group scheme `G`, a closed homomorphism `t : T.toGrp ⟶ G`,
and a representative `c : C ⟶ G` of the all-test-scheme centralizer of `t`.
Assume both `T` and `C` are smooth over the base and that, on each residue
fibre, the centralizer of the pulled-back homomorphism equals its range.
The construction returns an isomorphism `T.toGrp ≅ C`. Its forward map is
the canonical `torusCentralizerFactor`; the theorem with suffix `_hom_comp`
states that this map followed by `c` equals `t`.

To construct the isomorphism, the proof base changes the centralizer
representation to each residue field and uses the supplied equality to give
another representation by the pulled-back `t`. Uniqueness of represented
subgroups identifies the pulled-back factor with an isomorphism. Smoothness
and the published fibrewise open-immersion criterion make the original
factor an open immersion. Every point of `C` lifts to its residue fibre;
the isomorphism on that fibre supplies a preimage in `T`. Thus the open
immersion is surjective and hence an isomorphism. The usual forgetful
functors reflect this isomorphism back to group schemes.

`torusCentralizer_eq_range_of_residueFibres` then states that the centralizer
of `t` equals its range, with precisely the same hypotheses. It follows by
rewriting the represented range using the comparison isomorphism.

`splitTorusCentralizer_eq_range_of_fibrewiseMaximal_overRing` specializes
this argument to a reductive group over `Spec R` and a closed split torus
whose residue fibres are maximal tori. It supplies smoothness of `T` from
splitness and a smooth centralizer representative from
`splitTorusCentralizer_hasSmoothClosedRepresentative_overRing`. The published
field theorem `maximalTorusCentralizer` supplies self-centralization on each
residue fibre, using reductivity of those fibres. The conclusion is equality
of subgroup functors on every test scheme, including nonreduced ones.

The provenance is the internal combination of these published comparison,
smoothness, base-change and field results. The unit adds no literature
translation. It does not extend this last consequence to nonsplit relative
tori, construct derived intersections, or prove the full derived-group
correspondence.
