# General reductions for fibrewise isogenies of smooth affine groups

`IsFibrewiseIsogeny f` is the predicate that the base change of the specified
homomorphism `f` to every residue-field point of its base is `IsIsogeny`.
It abbreviates exactly the fibre hypothesis in the target statement, without
any extra geometric hypotheses.

This internal module defines that predicate and proves general prerequisites for
`Langlands.GroupScheme.ReductiveFibrewiseIsogenyStatement`, without proving that
statement. All schemes and group schemes lie in an arbitrary universe `u`.

- `flat_of_isogeny_fibres` applies the published finite-presentation fibrewise
  flatness criterion to a homomorphism between smooth group schemes whose
  residue-field fibres are isogenies.
- `surjective_of_isogeny_fibres` applies the published fibrewise surjectivity
  criterion; it needs no smoothness assumption.
- `locallyQuasiFinite_of_isogeny_fibres` assumes only that the source structure
  map is locally of finite type. Finiteness of each residue-field fibre map gives
  finite point fibres of the total map, and local finite type then gives local
  quasi-finiteness.
- `isogeny_iff_finite_kernel_of_isogeny_fibres` assumes both groups are smooth
  and affine over the base. Flatness and surjectivity follow from
  the first two lemmas; affineness makes the homomorphism quasi-compact.
  Finiteness of an isogeny's kernel is obtained by pulling back the homomorphism
  along the target unit. Conversely, the published fpqc kernel-pair descent
  theorem `isFinite_of_finite_kernel` gives finiteness of the homomorphism.

The provenance is internal composition of the imported Library theorems. The
mathematical reduction follows the discussion after Definition 3.3.9 on p.103
and the start of the proof of Proposition 6.1.10 on p.192 of Brian Conrad,
*Reductive group schemes* (2014), registered as
`conrad-2014-reductive-group-schemes`. These lemmas do not use reductivity or
prove the remaining finiteness assertion for kernels of reductive groups.
