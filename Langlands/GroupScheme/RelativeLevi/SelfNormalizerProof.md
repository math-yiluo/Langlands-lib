# Relative Levi subgroups are self-normalizing

The theorem `relativeLeviSelfNormalizer` proves the unchanged
`Langlands.GroupScheme.RelativeLeviSelfNormalizerStatement` in every universe.
It applies to every base scheme, reductive group scheme, relative parabolic
subgroup and relative Levi subgroup, with no additional hypotheses.

The supplied relative Levi decomposition restricts to an actual complement to
the unipotent radical on every canonical geometric fibre. The ambient group on
that fibre is connected reductive, and the parabolic remains parabolic.
`RelativeLevi.normalizer_eq_of_field_radical` proves self-normalization there:
the multiplication retraction and dynamic parabolic presentation identify a
normalizing radical point with a point in the trivial intersection of a dynamic
centralizer and its unipotent subgroup. Connected reductivity supplies the
separatedness used for uniqueness of the dynamic limit in this intersection.

The geometric-fibre reduction descends equality to residue fibres by fpqc
reflection, and arbitrary field-valued points factor through those residue
fibres. The published smooth affine detection theorem, applied on affine open
tests and glued using the closed subgroup inclusion, then proves equality of
the normalizer and Levi image on all test schemes. This also covers nonreduced
tests; checking geometric points alone would not suffice.

This proves the self-normalizer assertion of Conrad, *Reductive group schemes*
(2014), Corollary 5.4.6, second sentence, as encoded by the published target.
The implemented proof uses dynamic cocharacters and field detection rather
than the source's maximal-torus centralizer argument.
