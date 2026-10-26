# Relative H2 vanishing from all intermediate-field norms

Worker 68 authored this finite-group assembly and its explanation. The
p-group case is imported from Worker 28 and Worker 68's published
[p-group proof](FinitePGroupNormH2Proof.md).

The theorem
`Langlands.ClassFieldTheory.Local.finiteNormH2Vanishing.{u,v}` proves exactly
the published proposition
`Langlands.ClassFieldTheory.Local.FiniteNormH2Vanishing.{u,v}` from
[the statement module](FiniteNormH2Statement.md). For fields `K : Type v`
and `L : Type u` in independent universes, with `L/K` finite Galois,
surjectivity of `Langlands.LocalClassField.normUnits E L` for every
`E : IntermediateField K L` implies
`Subsingleton (relativeCohomology K L 2)`. The norms are the determinant
norms on the actual unit groups; cohomology is ordinary group cohomology
of the actual Galois action on `Additive Lˣ` over `IntegerScalars.{u}`.
The theorem adds no hypothesis to that proposition.

## Implemented proof

The private lemma `h2_subsingleton_of_sylow` treats a representation `A`
of a finite group `G` over a commutative ring. Suppose ordinary degree-two
cohomology of the restriction to every Sylow subgroup is a subsingleton.
The positive-degree isomorphism `TateCohomology.isoGroupCohomology 2`
then makes each Sylow Tate degree-two group a subsingleton as well.

For a Tate degree-two class `x`, restriction to a Sylow `p`-subgroup `P`
is therefore zero. The published identity
`Langlands.Tate.corestriction_restriction` gives
`(P : Subgroup G).index • x = 0`. Consequently `addOrderOf x` divides
this index. If a prime `p` divided `addOrderOf x`, it would divide
the index of its Sylow subgroup, contradicting `P.not_dvd_index`.
Thus no prime divides `addOrderOf x`, so its value is one and `x = 0`.
This reasoning also excludes the value zero used for infinite additive
order; it does not assume that the cohomology group is finite.
Finally, the same Tate/ordinary isomorphism transports vanishing back
to ordinary degree two.

To apply this lemma to `unitsRepresentation K L`, fix a Sylow subgroup
`P` of `Gal(L/K)` and put
`E = IntermediateField.fixedField (P : Subgroup Gal(L/K))`.
The canonical tower gives finite Galois `L/E`. The group equivalence
`IntermediateField.subgroupEquivAlgEquiv` identifies `P` with `Gal(L/E)`,
so the latter is a `p`-group.

The private lemma `norm_surjective_restrictScalars` supplies the entire
norm family for `L/E`: for `F : IntermediateField E L`, apply the original
hypothesis to `F.restrictScalars K`. Restriction of scalars preserves
the carrier field and its inclusion in `L`. The canonical
finite-dimensional instances therefore elaborate to the required norm
surjectivity directly.

Both `E` and `L` lie in universe `u`, so the published theorem
`finitePGroupNormH2Vanishing.{u}` now gives
`Subsingleton (relativeCohomology E L 2)`. This suffices even though
the original base field `K` lies in the independent universe `v`.
The imported p-group theorem uses cyclic norm comparison, inherited
norm surjectivity, and inflation–restriction; its proof is documented
in its own module.

The private definition `fixedFieldSubgroupCohomologyIso` identifies
ordinary cohomology of the restriction of `unitsRepresentation K L`
to `P` with `relativeCohomology E L`. It applies
`groupCohomology.mapIso` to the preceding group equivalence and the
identity linear equivalence on `Additive Lˣ`. The action compatibility
is definitional. Hence the Sylow restriction group is a subsingleton,
and the detection lemma concludes the proof.

Only vanishing is transported through the Tate/ordinary and group
equivalences. No compatibility between the ordinary and Tate restriction
maps is needed. Every algebra structure is the given structure or a
canonical intermediate-field structure.

## Provenance

This is the finite-extension consequence of Jean-Pierre Serre,
*Local Fields*, translated by Marvin Jay Greenberg, GTM 67 (1979),
Chapter X, Section 7, Proposition 11 and its proof, printed pp.161–162
(PDF pp.167–168). The implementation follows the cyclic and p-group
induction followed by Sylow reduction in the Remark on printed p.162
(PDF p.168). It uses the published p-group theorem and the transfer
identity, rather than implementing the general two-consecutive-degree
criterion of Chapter IX, Section 5, Theorem 8.

The registered original source is `serre-1979-local-fields`, retained at
`/home/taskhub/central-library/Serre--Local Fields--1979.pdf`, SHA256
`109b461d42915da70771c70c4b551a363fc1f33412331ae2671c5c85be433112`.
This module proves the stated implication for a single finite Galois
extension with its full intermediate-field norm family.
