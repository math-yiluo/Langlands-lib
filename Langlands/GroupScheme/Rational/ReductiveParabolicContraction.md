# Original radicals and Levis in a reductive dynamic parabolic

Author: Worker 1264.

This internal composition applies the published theorem
`dynamicCentralizerReductive` to the original radical and Levi maps of an
actual dynamic-parabolic presentation. All fields and the universe `u` are
arbitrary. Every range, centralizer, containment and equality uses subgroup
functors on all test schemes.

`Dynamic.normal_subgroup_range_comp_le_unipotent_of_reductive` takes a
connected reductive ambient group `G`, a cocharacter `χ`, an original map
`p : P → G` representing `Dynamic.parabolic χ`, and any smooth connected
normal unipotent closed subgroup `v : H → P`. It proves contraction of the
original ambient composite `v ≫ p`. The canonical affine representative of
the dynamic centralizer is connected reductive by
`dynamicCentralizerReductive`; its ground-field unipotent radical is trivial
by `IsConnectedReductive.hasTrivialUnipotentRadical`. The published
`Dynamic.normal_subgroup_range_comp_le_unipotent` then proves the conclusion.
No centralizer-reductivity or centralizer-radical premise remains.

`Dynamic.range_comp_radical_eq_unipotent_of_reductive` identifies the actual
ambient image of any supplied ground-field unipotent radical `r : U → P`
with `Dynamic.unipotent χ`. The first theorem gives the forward inclusion.
The published `Dynamic.unipotent_le_range_of_isUnipotentRadical`, which uses
the supplied radical's greatestness, gives the reverse inclusion. This
requires only the ground-field radical predicate and does not change the
supplied representative.

`IsRationalLeviSubgroup.centralizer_eq_of_dynamicParabolic` starts with the
original rational Levi `l : L → P` and a cocharacter in `L` whose ambient
composite presents the original `p` as its dynamic parabolic. The image of
`L` is contained in that parabolic. The published
`Dynamic.range_le_centralizer_of_range_le_parabolic` makes it fixed, using
triviality of the ground-field radical of the reductive group `L`. The
radical supplied by the rational-Levi predicate contracts by the first
theorem. Its original multiplication isomorphism with `L`, together with
containment of the dynamic centralizer in its parabolic, identifies the
full centralizer with the original image `range (l ≫ p)`.

`IsRationalLeviSubgroup.torusCentralizer_eq_of_dynamicParabolic` applies this
to a cocharacter through a central commutative subgroup `a : A → L`. The
whole-`A` centralizer is contained in the cocharacter centralizer; centrality
of `a` gives the reverse containment of the original Levi image.

`IsRationalLeviSubgroup.torusCentralizerIsoOfDynamicParabolic` constructs an
actual group-scheme isomorphism from the original `L` to any supplied
representative `m : M → G` of this whole-group centralizer. Closedness of
the represented dynamic parabolic and of the rational Levi makes `l ≫ p`
monomorphic. The proved centralizer equality makes it a second representative,
and published uniqueness of representatives gives the isomorphism. Its
`_hom_comp` and `_inv_comp` lemmas state the exact ambient identities
`iso.hom ≫ m = l ≫ p` and `iso.inv ≫ l ≫ p = m`.

The original dynamic-parabolic presentation remains an explicit hypothesis.
These results construct no presenting cocharacter or common torus/root
model, prove no splitness or ambient maximality, and do not prove
`MinimalParabolicLeviCentralizerStatement`. Their provenance is the displayed
composition of published Library results. They add no external structural
assertion or source claim. The imported results retain their documented
authorship and mathematical provenance.
