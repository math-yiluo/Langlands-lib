# Moving a supplied presenting cocharacter into the original Levi

Author: Worker 1264.

This derived construction starts from an arbitrary field in universe `u`, a
connected reductive ambient group `G`, an original rational Levi `l : L → P`,
and a supplied cocharacter `χ : Gm → G` whose dynamic parabolic is represented
by the original map `p : P → G`. It constructs a central cocharacter of the
original `L` presenting the same original parabolic. For every specified split
component `a : A → L`, it then constructs an actual integral cocharacter of
`A` presenting that parabolic, with centralizer exactly the original ambient
Levi image. The centralizer of the whole `A` also equals that Levi image. All
subgroup statements concern every test scheme and every required refinement.

`DynamicLeviConjugacy.mem_range_radical_iff_of_reductive` applies
`Dynamic.range_comp_radical_eq_unipotent_of_reductive` to a supplied
ground-field radical `r : U → P`. Monomorphy of the original `p` cancels its
underlying morphism, identifying membership in the original radical image
with membership of the ambient composite in `U(χ)`.

`IsRationalLeviSubgroup.exists_centralCocharacter_of_dynamicParabolic` uses
the actual retraction supplied by the original Levi multiplication
isomorphism. Its all-test kernel is the radical image and hence `U(χ)` by
the preceding comparison. The published
`DynamicLeviConjugacy.centralizer_leviCocharacter_eq_top` proves centrality of
the projected cocharacter in `L`. The published
`DynamicLeviConjugacy.leviCocharacter_mul_inv_mem` puts its ambient difference
from `χ` in `U(χ)(Gm)`. The unconditional affine-group theorem
`Dynamic.exists_unipotent_conj_of_mul_inv_mem` conjugates `χ` to that ambient
projected cocharacter by a ground-field point of `U(χ)`. Such a point lies in
`P(χ)`, and `DynamicLeviConjugacy.parabolic_comp_innerIso_eq` shows that its
conjugation preserves `P(χ)`. Thus the original `p` still represents the
parabolic of the cocharacter in the original `L`.

`IsRationalLeviSubgroup.exists_splitComponentCocharacter_of_dynamicParabolic`
factors that central cocharacter through the specified split component using
`IsSplitComponent.exists_factor`. Its ambient composite is unchanged.
`IsRationalLeviSubgroup.centralizer_eq_of_dynamicParabolic` and
`IsRationalLeviSubgroup.torusCentralizer_eq_of_dynamicParabolic` identify,
respectively, its cocharacter centralizer and the centralizer of the whole
split component with `range (l ≫ p)`.

`IsRationalLeviSubgroup.splitComponentCocharacterOfDynamicParabolic` chooses
this integral cocharacter. Its `_spec` theorem states the representation of
the original parabolic and both centralizer equalities.

The provenance is the displayed composition of Library constructions and
proofs; there is no additional external structural assertion. The imported
results retain their original authorship and provenance. This unit discharges
the former requirement that a supplied presenting cocharacter already be in
the original Levi. It does not assume either global
`ParabolicDynamicStatement` or global
`DynamicGeometricUnipotentRadicalStatement`. Existence of the initial dynamic
presentation remains an explicit input. This unit does not establish ambient
maximal splitness or prove `MinimalParabolicLeviCentralizerStatement`.
